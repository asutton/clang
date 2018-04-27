//===--- SemaInject.cpp - Semantic Analysis for Injection -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic rules for the injection of declarations into
//  various declarative contexts.
//
//===----------------------------------------------------------------------===//

#include "TreeTransform.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Template.h"
#include "clang/Sema/SemaInternal.h"

using namespace clang;
using namespace sema;

namespace clang {
/// \brief A compile-time value along with its type.
struct TypedValue
{
  TypedValue(QualType T, const APValue& V)
    : Type(T), Value(V)
  { }

  QualType Type;
  APValue Value;
};

/// Records information about a definition inside a fragment that must be
/// processed later. These are typically fields and methods.
struct InjectedDef
{
  InjectedDef(Decl *F, Decl *I) : Fragment(F), Injected(I) { }
  
  /// The declaration within the fragment.
  Decl *Fragment;

  /// The injected declaration.
  Decl *Injected;
};

class InjectionContext;

/// \brief An injection context. This is declared to establish a set of
/// substitutions during an injection.
class InjectionContext : public TreeTransform<InjectionContext>
{
  using Base = TreeTransform<InjectionContext>;
public:
  /// Initialize the context for injecting a fragment.
  InjectionContext(Sema &SemaRef, 
                   CXXFragmentDecl *Frag, 
                   DeclContext *Injectee,
                   Decl *Injection)
      : Base(SemaRef), Prev(SemaRef.CurrentInjectionContext), 
        Fragment(Frag), Injectee(Injectee), Injection(Injection) {
    getSema().CurrentInjectionContext = this;
  }
  
  /// Initialize the context for relocating a declaration.
  InjectionContext(Sema &SemaRef, 
                   DeclContext *Injectee, 
                   Decl *Injection)
    : Base(SemaRef), Prev(SemaRef.CurrentInjectionContext), Fragment(), 
      Injectee(Injectee), Injection(Injection) {
   getSema().CurrentInjectionContext = this;
  }  

  ~InjectionContext() {
    if (Prev != (InjectionContext *)0x1)
      getSema().CurrentInjectionContext = Prev;
  }

  ASTContext &getContext() { return getSema().Context; }

  /// Injection always builds new trees.
  bool AlwaysRebuild() const { return true; }

  /// Detach the context from the semantics object. Returns this object for
  /// convenience.
  InjectionContext *Detach() {
    getSema().CurrentInjectionContext = Prev;
    Prev = (InjectionContext *)0x1;
    return this;
  }

  /// Re-attach the context to the context stack.
  void Attach() {
    assert((Prev == (InjectionContext *)0x1) && "Context not detached");
    Prev = getSema().CurrentInjectionContext;
    getSema().CurrentInjectionContext = this;
  }

  /// \brief Adds a substitution from one declaration to another.
  void AddDeclSubstitution(Decl *Old, Decl *New) {
    assert(TransformedLocalDecls.count(Old) == 0 && "Overwriting substitution");
    transformedLocalDecl(Old, New);
  }

  /// \brief Adds a substitution from a fragment placeholder to its
  /// (type) constant value.
  void AddPlaceholderSubstitution(Decl *Orig, QualType T, const APValue &V) { 
    assert(isa<VarDecl>(Orig) && "Expected a variable declaration");
    assert(PlaceholderSubsts.count(Orig) == 0 && "Overwriting substitution");
    PlaceholderSubsts.try_emplace(Orig, T, V);
  }

  /// \brief Adds substitutions for each placeholder in the fragment. 
  /// The types and values are sourced from the fields of the reflection 
  /// class and the captured values.
  void AddPlaceholderSubstitutions(DeclContext *Fragment,
                                   CXXRecordDecl *Reflection,
                                   ArrayRef<APValue> Captures) {
    assert(isa<CXXFragmentDecl>(Fragment) && "Context is not a fragment");
    auto FieldIter = Reflection->field_begin();
    auto PlaceIter = Fragment->decls_begin();
    for (std::size_t I = 0; I < Captures.size(); ++I) {
      Decl *Var = *PlaceIter++;
      QualType Ty = (*FieldIter++)->getType();
      const APValue &Val = Captures[I];
      AddPlaceholderSubstitution(Var, Ty, Val);
    }
  }

  /// Returns a replacement for D if a substitution has been registered or
  /// nullptr if no such replacement exists.
  Decl *GetDeclReplacement(Decl *D) {
    auto Iter = TransformedLocalDecls.find(D);
    if (Iter != TransformedLocalDecls.end())
      return Iter->second;
    else
      return nullptr;
  }

  /// Returns a replacement expression if E refers to a placeholder.
  Expr *GetPlaceholderReplacement(DeclRefExpr *E) {
    auto Iter = PlaceholderSubsts.find(E->getDecl());
    if (Iter != PlaceholderSubsts.end()) {
      // Build a new constant expression as the replacement. The source
      // expression is opaque since the actual declaration isn't part of
      // the output AST (but we might want it as context later -- makes
      // pretty printing more elegant).
      const TypedValue &TV = Iter->second;
      Expr *O = new (getContext()) OpaqueValueExpr(
          E->getLocation(), TV.Type, VK_RValue, OK_Ordinary, E);
      return new (getContext()) CXXConstantExpr(O, TV.Value);
    } else {
      return nullptr;
    }
  }

  /// Returns the declaration for the injectee.
  Decl *GetInjecteeDecl() const { return Decl::castFromDeclContext(Injectee); }

  /// Returns true if D is within an injected fragment or cloned declaration.
  bool IsInInjection(Decl *D);

  // TreeTransform Overloads

  DeclarationNameInfo TransformDeclarationName(NamedDecl *ND) {
    DeclarationNameInfo DNI(ND->getDeclName(), ND->getLocation());
    return TransformDeclarationNameInfo(DNI);
  }

  Decl *TransformDecl(SourceLocation Loc, Decl *D);
  
  ValueDecl *LookupDecl(NestedNameSpecifierLoc NNS, DeclarationNameInfo DNI);
  ValueDecl *LookupMember(NestedNameSpecifierLoc NNS, DeclarationNameInfo DNI);

  ExprResult TransformDeclRefExpr(DeclRefExpr *E);

  // Declaration injection

  bool InjectDeclarator(DeclaratorDecl *D, 
                        DeclarationNameInfo &DNI, 
                        TypeSourceInfo *&TSI);
  bool InjectMemberDeclarator(DeclaratorDecl *D,
                              DeclarationNameInfo &DNI, 
                              TypeSourceInfo *&TSI, 
                              CXXRecordDecl *&Owner);

  Decl *InjectDecl(Decl *D);
  Decl *InjectEnumDecl(EnumDecl *D);
  Decl *InjectEnumConstantDecl(EnumConstantDecl *D);
  Decl *InjectTypedefNameDecl(TypedefNameDecl *D);
  Decl *InjectVarDecl(VarDecl *D);
  Decl *InjectParmVarDecl(ParmVarDecl *D);
  Decl *InjectCXXRecordDecl(CXXRecordDecl *D);
  Decl *InjectFieldDecl(FieldDecl *D);
  Decl *InjectCXXMethodDecl(CXXMethodDecl *D);
  Decl *InjectAccessSpecDecl(AccessSpecDecl *D);
  Decl *InjectConstexrDecl(ConstexprDecl *D);

  // Members

  /// \brief The previous injection context.
  InjectionContext *Prev;

  /// \brief The fragment being injected.
  CXXFragmentDecl *Fragment;

  /// \brief The context into which the fragment is injected
  DeclContext *Injectee;

  /// \brief The declaration being Injected.
  Decl *Injection;

  /// \brief A mapping of fragment placeholders to their typed compile-time
  /// values. This is used by TreeTransformer to replace references with
  /// constant expressions.
  llvm::DenseMap<Decl *, TypedValue> PlaceholderSubsts;

  /// \brief A list of declarations whose definitions have not yet been
  /// injected. These are processed when a class receiving injections is
  /// completed.
  llvm::SmallVector<InjectedDef, 8> InjectedDefinitions;
};

bool InjectionContext::IsInInjection(Decl *D) {
  // If this is actually a fragment, then we can check in the usual way.
  if (Fragment)
    return D->isInFragment();

  // Otherwise, we're cloning a declaration, (not a fragment) but we need
  // to ensure that any any declarations within that are injected.

  // If D is injection source, then it must be injected.
  if (D == Injection)
    return true;

  // If the injection is not a DC, then D cannot be in the injection because
  // it could not have been declared within (e.g., if the injection is a
  // variable).
  DeclContext *Outer = dyn_cast<DeclContext>(Injection);
  if (!Outer)
    return false;

  // Note that Injection->getDeclContext() == InjecteeDC. We don't want to
  // use that as the outermost context since it includes declarations that
  // should not be injected. That is, copying a member function does not
  // mean that we are copying member variables of the same class.

  // Otherwise, work outwards to see if D is in the Outermost context
  // of the injection. If we reach the outermost scope, we're not inside
  // an injection.
  DeclContext *DC = D->getDeclContext();
  while (DC) {
    if (DC == Outer)
      return true;
    if (DC == Injectee)
      return false;
    DC = DC->getParent();
  }
  return false;
}

Decl* InjectionContext::TransformDecl(SourceLocation Loc, Decl *D) {
  if (!D)
    return nullptr;

  // If D is part of the injection, then we must have seen a previous
  // declaration.
  //
  // FIXME: This may not be true with gotos and labels.
  if (IsInInjection(D))
    return GetDeclReplacement(D);

  // When copying existing declarations, if D is a member of the of the
  // injection's declaration context, then we want to re-map that so that the
  // result is a member of the injection. For example:
  //
  //    struct S {
  //      int x; 
  //      int f() { 
  //        return x; // Not dependent, bound
  //      }
  //    };
  //
  //    struct T { constexpr { __generate $S::f; } };
  //
  // At the point that we inject S::f, the reference to x is not dependent,
  // and therefore not subject to two-phase lookup. However, we would expect
  // the reference to be to the T::x during injection.
  //
  // Note that this isn't necessary for fragments. We expect names to be
  // written dependently there and subject to the usual name resolution
  // rules.
  //
  // Defer the resolution to the caller so that the result can be interpreted
  // within the context of the expression, not here.
  if (!Fragment && D->getDeclContext() == Injection->getDeclContext())
    return nullptr;

  return D;
}

ExprResult InjectionContext::TransformDeclRefExpr(DeclRefExpr *E) {
  if (Expr *Repl = GetPlaceholderReplacement(E))
    return Repl;
  return Base::TransformDeclRefExpr(E);
}

ValueDecl *InjectionContext::LookupDecl(NestedNameSpecifierLoc NNS,
                                        DeclarationNameInfo DNI) {
  return nullptr;
}


ValueDecl *InjectionContext::LookupMember(NestedNameSpecifierLoc NNS,
                                          DeclarationNameInfo DNI) {
  CXXScopeSpec SS;
  SS.Adopt(NNS);
  assert(SS.isEmpty() && "Qualified lookup of member not implemented");

  // FIXME: What if we find an overload set or an ambiguous result?
  // This may need to call ActOnMemberAccessExpr to completely rebuild
  // the original expression. Same with LookupDecl.
  LookupResult R(getSema(), DNI, Sema::LookupMemberName);
  if (!getSema().LookupName(R, getSema().getCurScope())) {
    getSema().DiagnoseEmptyLookup(getSema().getCurScope(), SS, R, nullptr);
    return nullptr;
  }
  return R.getAsSingle<ValueDecl>();
}

static bool InjectEnumDefinition(InjectionContext &Cxt, 
                                 EnumDecl *OldEnum,
                                 EnumDecl *NewEnum) {
  SmallVector<Decl*, 4> Enumerators;
  
  EnumConstantDecl *LastConst = nullptr;
  for (auto *OldConst : OldEnum->enumerators()) {
    // The specified value for the enumerator.
    ExprResult Value;
    if (Expr *OldValue = OldConst->getInitExpr()) {
      // The enumerator's value expression is a constant expression.
      EnterExpressionEvaluationContext Unevaluated(
          Cxt.getSema(), Sema::ExpressionEvaluationContext::ConstantEvaluated);
      Value = Cxt.TransformExpr(OldValue);
    }

    // Drop the initial value and continue.
    bool Invalid = false;
    if (Value.isInvalid()) {
      Value = nullptr;
      Invalid = true;
    }

    // Create the new enum.
    EnumConstantDecl *Const = Cxt.getSema().CheckEnumConstant(
        NewEnum, LastConst, OldConst->getLocation(), 
        OldConst->getIdentifier(), Value.get());
    if (!Const) {
      NewEnum->setInvalidDecl();
      continue;
    }
    Cxt.AddDeclSubstitution(OldConst, Const);

    if (Invalid) {
      Const->setInvalidDecl();
      NewEnum->setInvalidDecl();
    }

    Const->setAccess(OldConst->getAccess());
    NewEnum->addDecl(Const);

    Enumerators.push_back(Const);
    LastConst = Const;
  }

  Cxt.getSema().ActOnEnumBody(
      NewEnum->getLocation(), NewEnum->getBraceRange(), NewEnum,
      Enumerators, /*Scope=*/nullptr, /*AttributeList=*/nullptr);

  return !NewEnum->isInvalidDecl();
}

Decl* InjectionContext::InjectEnumDecl(EnumDecl *D) {
  DeclContext *Owner = getSema().CurContext;

  // FIXME: Transform the name and nested name specifier.

  // FIXME: If there's a previous decl, be sure to link that with this
  // enum.

  // Start by creating the new enumeration.
  EnumDecl *Enum = EnumDecl::Create(
      getContext(), Owner, D->getLocStart(), D->getLocation(), 
      D->getIdentifier(), /*PrevDecl*/nullptr, D->isScoped(), 
      D->isScopedUsingClassTag(), D->isFixed());
  AddDeclSubstitution(D, Enum);
  
  if (D->isFixed()) {
    if (TypeSourceInfo *TSI = D->getIntegerTypeSourceInfo()) {
      // If we have type source information for the underlying type, it means it
      // has been explicitly set by the user. Perform substitution on it before
      // moving on.
      TSI = TransformType(TSI);
      if (!TSI || getSema().CheckEnumUnderlyingType(TSI))
        Enum->setIntegerType(getSema().Context.IntTy);
      else
        Enum->setIntegerTypeSourceInfo(TSI);
    } else {
      assert(!D->getIntegerType()->isDependentType()
             && "Dependent type without type source info");
      Enum->setIntegerType(D->getIntegerType());
    }
  }

  Enum->setAccess(D->getAccess());

  // Forward the mangling number from the template to the instantiated decl.
  getContext().setManglingNumber(Enum, getContext().getManglingNumber(D));
  
  // See if the old tag was defined along with a declarator.
  // If it did, mark the new tag as being associated with that declarator.
  if (DeclaratorDecl *DD = getContext().getDeclaratorForUnnamedTagDecl(D))
    getContext().addDeclaratorForUnnamedTagDecl(Enum, DD);
  
  // See if the old tag was defined along with a typedef.
  // If it did, mark the new tag as being associated with that typedef.
  if (TypedefNameDecl *TD = getContext().getTypedefNameForUnnamedTagDecl(D))
    getContext().addTypedefNameForUnnamedTagDecl(Enum, TD);

  Owner->addDecl(Enum);

  // If the enum is defined, inject it.
  EnumDecl *Def = D->getDefinition();
  if (Def == D)
    InjectEnumDefinition(*this, D, Enum);

  return D;
}

Decl* InjectionContext::InjectEnumConstantDecl(EnumConstantDecl *D) {
  // NOTE: Enumerators are processed by InjectEnumDefinition.
  llvm_unreachable("Should not get here");
}

Decl* InjectionContext::InjectTypedefNameDecl(TypedefNameDecl *D) {
  bool Invalid = false;

  DeclContext *Owner = getSema().CurContext;

  // Transform the type. If this fails, just retain the original, but
  // invalidate the declaration later.
  TypeSourceInfo *TSI = TransformType(D->getTypeSourceInfo());
  if (!TSI) {
    TSI = D->getTypeSourceInfo();
    Invalid = true;
  }
  
  // Create the new typedef
  TypedefNameDecl *Typedef;
  if (isa<TypeAliasDecl>(D))
    Typedef = TypeAliasDecl::Create(
        getContext(), Owner, D->getLocStart(), D->getLocation(), 
        D->getIdentifier(), TSI);
  else
    Typedef = TypedefDecl::Create(
        getContext(), Owner, D->getLocStart(), D->getLocation(), 
        D->getIdentifier(), TSI);
  AddDeclSubstitution(D, Typedef);

  Typedef->setAccess(D->getAccess());
  Typedef->setInvalidDecl(Invalid);
  Owner->addDecl(Typedef);
  
  return Typedef;
}

// Inject the name and the type of a declarator declaration. Sets the
// declaration name info, type, and owner. Returns true if the declarator
// is invalid.
//
// FIXME: If the declarator has a nested names specifier, rebuild that
// also. That potentially modifies the owner of the declaration
bool InjectionContext::InjectDeclarator(DeclaratorDecl *D,
                                        DeclarationNameInfo &DNI, 
                                        TypeSourceInfo *&TSI) {
  bool Invalid = false;

  // Rebuild the name.

  DNI = TransformDeclarationName(D);
  if (!DNI.getName())
    Invalid = true;

  // Rebuild the type.
  TSI = TransformType(D->getTypeSourceInfo());
  if (!TSI) {
    TSI = D->getTypeSourceInfo();
    Invalid = true;
  }

  return Invalid;
}

// Inject the name and the type of a declarator declaration. Sets the
// declaration name info, type, and owner. Returns true if the declarator
// is invalid.
bool InjectionContext::InjectMemberDeclarator(DeclaratorDecl *D, 
                                              DeclarationNameInfo &DNI, 
                                              TypeSourceInfo *&TSI, 
                                              CXXRecordDecl *&Owner) {
  bool Invalid = InjectDeclarator(D, DNI, TSI);
  Owner = cast<CXXRecordDecl>(getSema().CurContext);
  return Invalid;
}

static bool InjectVariableInitializer(InjectionContext &Cxt, 
                                      VarDecl *Old,
                                      VarDecl *New) {
  if (Old->getInit()) {
    if (New->isStaticDataMember() && !Old->isOutOfLine())
      Cxt.getSema().PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::ConstantEvaluated, Old);
    else
      Cxt.getSema().PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::PotentiallyEvaluated, Old);

    // Instantiate the initializer.
    ExprResult Init;
    {
      Sema::ContextRAII SwitchContext(Cxt.getSema(), New->getDeclContext());
      bool DirectInit = (Old->getInitStyle() == VarDecl::CallInit);
      Init = Cxt.TransformInitializer(Old->getInit(), DirectInit);
    }
    
    if (!Init.isInvalid()) {
      Expr *InitExpr = Init.get();
      if (New->hasAttr<DLLImportAttr>() &&
          (!InitExpr || 
           !InitExpr->isConstantInitializer(Cxt.getContext(), false))) {
        // Do not dynamically initialize dllimport variables.
      } else if (InitExpr) {
        Cxt.getSema().AddInitializerToDecl(New, InitExpr, Old->isDirectInit());
      } else {
        Cxt.getSema().ActOnUninitializedDecl(New);
      }
    } else {
      New->setInvalidDecl();
    }

    Cxt.getSema().PopExpressionEvaluationContext();
  } else {
    if (New->isStaticDataMember()) {
      if (!New->isOutOfLine())
        return New;

      // If the declaration inside the class had an initializer, don't add
      // another one to the out-of-line definition.
      if (Old->getFirstDecl()->hasInit())
        return New;
    }

    // We'll add an initializer to a for-range declaration later.
    if (New->isCXXForRangeDecl())
      return New;

    Cxt.getSema().ActOnUninitializedDecl(New);
  }
  
  return New;
}

Decl *InjectionContext::InjectVarDecl(VarDecl *D) {
  DeclContext *Owner = getSema().CurContext;
  
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  bool Invalid = InjectDeclarator(D, DNI, TSI);

  // FIXME: Check for re-declaration.

  VarDecl *Var = VarDecl::Create(
      getContext(), Owner, D->getInnerLocStart(), DNI, TSI->getType(), 
      TSI, D->getStorageClass());
  AddDeclSubstitution(D, Var);

  if (D->isNRVOVariable()) {
    QualType ReturnType = cast<FunctionDecl>(Owner)->getReturnType();
    if (getSema().isCopyElisionCandidate(ReturnType, Var, false))
      Var->setNRVOVariable(true);
  }

  Var->setImplicit(D->isImplicit());
  Var->setInvalidDecl(Invalid);
  Owner->addDecl(Var);

  // If we are instantiating a local extern declaration, the
  // instantiation belongs lexically to the containing function.
  // If we are instantiating a static data member defined
  // out-of-line, the instantiation will have the same lexical
  // context (which will be a namespace scope) as the template.
  if (D->isLocalExternDecl()) {
    Var->setLocalExternDecl();
    Var->setLexicalDeclContext(Owner);
  } else if (D->isOutOfLine()) {
    Var->setLexicalDeclContext(D->getLexicalDeclContext());
  }
  Var->setTSCSpec(D->getTSCSpec());
  Var->setInitStyle(D->getInitStyle());
  Var->setCXXForRangeDecl(D->isCXXForRangeDecl());
  Var->setConstexpr(D->isConstexpr());
  Var->setInitCapture(D->isInitCapture());
  Var->setPreviousDeclInSameBlockScope(D->isPreviousDeclInSameBlockScope());
  Var->setAccess(D->getAccess());

  if (!D->isStaticDataMember()) {
    if (D->isUsed(false))
      Var->setIsUsed();
    Var->setReferenced(D->isReferenced());
  }

  // FIXME: Instantiate attributes.

  // Forward the mangling number from the template to the instantiated decl.
  getContext().setManglingNumber(
      Var, getContext().getManglingNumber(D));
  getContext().setStaticLocalNumber(
      Var, getContext().getStaticLocalNumber(D));

  if (D->isInlineSpecified())
    Var->setInlineSpecified();
  else if (D->isInline())
    Var->setImplicitlyInline();

  InjectVariableInitializer(*this, D, Var);

  // FIXME: Diagnose un-used declarations here?
  
  return Var;
}

Decl *InjectionContext::InjectParmVarDecl(ParmVarDecl *D) {
  // Parameters are created during type transformation. We add mappings
  // for them when creating the function.
  llvm_unreachable("Should not get here");
}

/// Injects the base specifier Base into Class.
static bool InjectBaseSpecifiers(InjectionContext &Cxt, 
                                 CXXRecordDecl *OldClass,
                                 CXXRecordDecl *NewClass) {
  bool Invalid = false;
  SmallVector<CXXBaseSpecifier*, 4> Bases;
  for (const CXXBaseSpecifier &OldBase : OldClass->bases()) {
    TypeSourceInfo *TSI = Cxt.TransformType(OldBase.getTypeSourceInfo());
    if (!TSI) {
      Invalid = true;
      continue;
    }

    CXXBaseSpecifier *NewBase = Cxt.getSema().CheckBaseSpecifier(
        NewClass, OldBase.getSourceRange(), OldBase.isVirtual(), 
        OldBase.getAccessSpecifierAsWritten(), TSI, OldBase.getEllipsisLoc());
    if (!NewBase) {
      Invalid = true;
      continue;
    }

    Bases.push_back(NewBase);
  }

  if (!Invalid && Cxt.getSema().AttachBaseSpecifiers(NewClass, Bases))
    Invalid = true;

  // Invalidate the class if necessary.
  NewClass->setInvalidDecl(Invalid);

  return Invalid;
}

static bool InjectClassMembers(InjectionContext &Cxt,
                               CXXRecordDecl *OldClass,
                               CXXRecordDecl *NewClass) {
  for (Decl *OldMember : OldClass->decls()) {
    // Don't transform invalid declarations.
    if (OldMember->isInvalidDecl())
      continue;

    // Don't transform non-members appearing in a class.
    //
    // FIXME: What does it mean to inject friends?
    if (OldMember->getDeclContext() != OldClass)
      continue;
    
    Decl *NewMember = Cxt.InjectDecl(OldMember);
    if (!NewMember)
      NewClass->setInvalidDecl();
  }
  return NewClass->isInvalidDecl();
}

static bool InjectClassDefinition(InjectionContext &Cxt,
                                  CXXRecordDecl *OldClass,
                                  CXXRecordDecl *NewClass) {
  Sema::ContextRAII SwitchContext(Cxt.getSema(), NewClass);
  Cxt.getSema().StartDefinition(NewClass);
  InjectBaseSpecifiers(Cxt, OldClass, NewClass);
  InjectClassMembers(Cxt, OldClass, NewClass);
  Cxt.getSema().CompleteDefinition(NewClass);
  return NewClass->isInvalidDecl();
}

Decl *InjectionContext::InjectCXXRecordDecl(CXXRecordDecl *D) {
  bool Invalid = false;
  DeclContext *Owner = getSema().CurContext;

  // FIXME: Do a lookup for previous declarations.

  CXXRecordDecl *Class;
  if (D->isInjectedClassName()) {
    DeclarationName DN = cast<CXXRecordDecl>(Owner)->getDeclName();
    Class = CXXRecordDecl::Create(
        getContext(), D->getTagKind(), Owner, D->getLocStart(), 
        D->getLocation(), DN.getAsIdentifierInfo(), /*PrevDecl=*/nullptr);
  } else {
    DeclarationNameInfo DNI = TransformDeclarationName(D);
    if (!DNI.getName())
      Invalid = true;
    Class = CXXRecordDecl::Create(
        getContext(), D->getTagKind(), Owner, D->getLocStart(), 
        D->getLocation(), DNI.getName().getAsIdentifierInfo(), 
        /*PrevDecl=*/nullptr);
  }
  AddDeclSubstitution(D, Class);

  // FIXME: Inject attributes.

  // FIXME: Propagate other properties?
  Class->setAccess(D->getAccess());
  Class->setImplicit(D->isImplicit());
  Class->setInvalidDecl(Invalid);
  Owner->addDecl(Class);

  if (D->hasDefinition()) 
    InjectClassDefinition(*this, D, Class);

  return Class;
}

Decl *InjectionContext::InjectFieldDecl(FieldDecl *D) {
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = InjectMemberDeclarator(D, DNI, TSI, Owner);

  // FIXME: Substitute through the bit width.
  Expr *BitWidth = nullptr;

  // Build and check the field.
  FieldDecl *Field = getSema().CheckFieldDecl(
      DNI.getName(), TSI->getType(), TSI, Owner, D->getLocation(), 
      D->isMutable(), BitWidth, D->getInClassInitStyle(), D->getInnerLocStart(),
      D->getAccess(), nullptr);
  AddDeclSubstitution(D, Field);

  // FIXME: Propagate attributes?

  // FIXME: In general, see VisitFieldDecl in the template instantiatior.
  // There are some interesting cases we probably need to handle.

  // Propagate semantic properties.
  //
  // FIXME: Inherit access as a semantic attribute or trace it through the
  // injection as if parsing?
  Field->setImplicit(D->isImplicit());
  Field->setAccess(D->getAccess());
  Field->setInvalidDecl(Invalid);
  Owner->addDecl(Field);

  // If the field has an initializer, add it to the Fragment so that we
  // can process it later.
  if (D->hasInClassInitializer())
    InjectedDefinitions.push_back(InjectedDef(D, Field));

  return Field;
}

Decl *InjectionContext::InjectCXXMethodDecl(CXXMethodDecl *D) {
  ASTContext &AST = getContext();
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = InjectMemberDeclarator(D, DNI, TSI, Owner);

  // Build the underlying method.
  //
  // FIXME: Should we propagate implicit operators?
  CXXMethodDecl *Method;
  if (CXXConstructorDecl *Ctor = dyn_cast<CXXConstructorDecl>(D)) {
    Method = CXXConstructorDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                        TSI->getType(), TSI,
                                        Ctor->isExplicit(),
                                        Ctor->isInlineSpecified(),
                                        Ctor->isImplicit(), 
                                        Ctor->isConstexpr());
    Method->setRangeEnd(D->getLocEnd());
  } else if (CXXDestructorDecl *Dtor = dyn_cast<CXXDestructorDecl>(D)) {
    Method = CXXDestructorDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                       TSI->getType(), TSI,
                                       Dtor->isInlineSpecified(),
                                       Dtor->isImplicit());
    Method->setRangeEnd(D->getLocEnd());
  } else if (CXXConversionDecl *Conv = dyn_cast<CXXConversionDecl>(D)) {
    Method = CXXConversionDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                       TSI->getType(), TSI,
                                       Conv->isInlineSpecified(),
                                       Conv->isExplicit(), Conv->isConstexpr(),
                                       Conv->getLocEnd());
  } else {
    Method = CXXMethodDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                   TSI->getType(), TSI, 
                                   D->isStatic() ? SC_Static : SC_None, 
                                   D->isInlineSpecified(), D->isConstexpr(), 
                                   D->getLocEnd());
  }
  AddDeclSubstitution(D, Method);

  // Bind the parameters to the method.
  FunctionProtoTypeLoc TL = TSI->getTypeLoc().castAs<FunctionProtoTypeLoc>();
  Method->setParams(TL.getParams());

  // Update the parameters their owning functions and register
  // substitutions.
  assert(Method->getNumParams() == D->getNumParams());
  auto OldParms = D->parameters();
  auto NewParms = Method->parameters();
  for (unsigned I = 0; I < Method->getNumParams(); ++I) {
    ParmVarDecl *Old = OldParms[I];
    ParmVarDecl *New = NewParms[I];
    New->setOwningFunction(Method);
    AddDeclSubstitution(Old, New);
  }

  // FIXME: Propagate attributes

  // FIXME: Check for redeclarations

  // Propagate semantic properties.
  //
  // FIXME: Inherit access as a semantic attribute or trace it through the
  // injection as if parsing?
  Method->setImplicit(D->isImplicit());
  Method->setAccess(D->getAccess());
  Method->setDeletedAsWritten(D->isDeletedAsWritten());
  Method->setDefaulted(D->isDefaulted());
  Method->setInvalidDecl(Invalid);
  Owner->addDecl(Method);

  // If the method is has a body, add it to the context so that we can 
  // process it later. Note that deleted/defaulted definitions are just
  // flags processed above.
  if (D->hasBody())
    InjectedDefinitions.push_back(InjectedDef(D, Method));

  return Method;
}

Decl *InjectionContext::InjectAccessSpecDecl(AccessSpecDecl *D) {
  CXXRecordDecl *Owner = cast<CXXRecordDecl>(getSema().CurContext);
  return AccessSpecDecl::Create(
      getContext(), D->getAccess(), Owner, D->getLocation(), D->getColonLoc());
}

Decl *InjectionContext::InjectConstexrDecl(ConstexprDecl *D) {
  // We can use the ActOn* members since the initial parsing for these
  // declarations is trivial (i.e., don't have to translate declarators).
  unsigned ScopeFlags; // Unused
  Decl *New = getSema().ActOnConstexprDecl(
    /*Scope=*/nullptr, D->getLocation(), ScopeFlags);

  getSema().ActOnStartConstexprDecl(/*Scope=*/nullptr, New);
  StmtResult S = TransformStmt(D->getBody());
  if (!S.isInvalid())
    getSema().ActOnFinishConstexprDecl(/*Scope=*/nullptr, New, S.get());
  else
    getSema().ActOnConstexprDeclError(/*Scope=*/nullptr, New);

  return New;
}


/// \brief Injects a new version of the declaration. Do not use this to
/// resolve references to declarations; use ResolveDecl instead.
Decl *InjectionContext::InjectDecl(Decl *D) {
  assert(!GetDeclReplacement(D) && "Declaration already injected");
  
  // If the declaration does not appear in the context, then it need
  // not be resolved.
  if (!IsInInjection(D))
    return D;

  // Inject the declaration.
  switch (D->getKind()) {
  case Decl::Enum:
    return InjectEnumDecl(cast<EnumDecl>(D));
  case Decl::EnumConstant:
    return InjectEnumConstantDecl(cast<EnumConstantDecl>(D));
  case Decl::Typedef:
  case Decl::TypeAlias:
    return InjectTypedefNameDecl(cast<TypedefNameDecl>(D));
  case Decl::Var:
    return InjectVarDecl(cast<VarDecl>(D));
  case Decl::ParmVar:
    return InjectParmVarDecl(cast<ParmVarDecl>(D));
  case Decl::CXXRecord:
    return InjectCXXRecordDecl(cast<CXXRecordDecl>(D));
  case Decl::Field:
    return InjectFieldDecl(cast<FieldDecl>(D));
  case Decl::CXXMethod:
  case Decl::CXXConstructor:
  case Decl::CXXDestructor:
  case Decl::CXXConversion:
    return InjectCXXMethodDecl(cast<CXXMethodDecl>(D));
  case Decl::AccessSpec:
    return InjectAccessSpecDecl(cast<AccessSpecDecl>(D));
  case Decl::Constexpr:
    return InjectConstexrDecl(cast<ConstexprDecl>(D));
  default:
    D->dump();
    llvm_unreachable("unknown declaration");
  }
}

} // namespace clang

// -------------------------------------------------------------------------- //
// Semantic analysis

// Find variables to capture in the given scope. 
static void FindCapturesInScope(Sema &SemaRef, Scope *S, 
                                SmallVectorImpl<VarDecl *> &Vars) {
  for (Decl *D : S->decls()) {
    if (VarDecl *Var = dyn_cast<VarDecl>(D)) {
      // Only capture locals with initializers.
      //
      // FIXME: If the fragment is in the initializer of a variable, this
      // will also capture that variable. For example:
      //
      //    auto f = __fragment class { ... };
      //
      // The capture list for the fragment will include f. This seems insane,
      // but lambda capture seems to also do this (with some caveats about
      // usage).
      //
      // We can actually detect this case in this implementation because
      // the type must be deduced and we won't have associated the 
      // initializer with the variable yet.
      if (!isa<ParmVarDecl>(Var) &&
          !Var->hasInit() &&
          Var->getType()->isUndeducedType())
        continue;

      Vars.push_back(Var);
    }
  }
}

// Search the scope list for captured variables. When S is null, we're
// applying applying a transformation.
static void FindCaptures(Sema &SemaRef, Scope *S, FunctionDecl *Fn, 
                         SmallVectorImpl<VarDecl *> &Vars) {
  assert(S && "Expected non-null scope");
  while (S && S->getEntity() != Fn) {
    FindCapturesInScope(SemaRef, S, Vars);
    S = S->getParent();
  }
  if (S)
    FindCapturesInScope(SemaRef, S, Vars);
}

/// Construct a reference to each captured value and force an r-value
/// conversion so that we get rvalues during evaluation.
static void ReferenceCaptures(Sema &SemaRef, 
                              SmallVectorImpl<VarDecl *> &Vars,
                              SmallVectorImpl<Expr *> &Refs) {
  Refs.resize(Vars.size());
  std::transform(Vars.begin(), Vars.end(), Refs.begin(), [&](VarDecl *D) {
    Expr *Ref = new (SemaRef.Context) DeclRefExpr(D, false, D->getType(), 
                                                  VK_LValue, D->getLocation());
    return ImplicitCastExpr::Create(SemaRef.Context, D->getType(), 
                                    CK_LValueToRValue, Ref, nullptr, VK_RValue);
  });
}

/// Returns the variable from a captured declaration.
static VarDecl *GetVariableFromCapture(Expr *E)
{
  Expr *Ref = cast<ImplicitCastExpr>(E)->getSubExpr();
  return cast<VarDecl>(cast<DeclRefExpr>(Ref)->getDecl());
}

// Create a placeholder for each captured expression in the scope of the
// fragment. For some captured variable 'v', these have the form:
//
//    constexpr auto v = <opaque>;
//
// These are replaced by their values during injection.
static void CreatePlaceholder(Sema &SemaRef, CXXFragmentDecl *Frag, Expr *E) {
  ValueDecl *Var = GetVariableFromCapture(E);
  SourceLocation IdLoc = Var->getLocation();
  IdentifierInfo *Id = Var->getIdentifier();
  QualType T = SemaRef.Context.DependentTy;
  TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(T);
  VarDecl *Placeholder = VarDecl::Create(SemaRef.Context, Frag, IdLoc, IdLoc, 
                                         Id, T, TSI, SC_Static);
  Placeholder->setConstexpr(true);
  Placeholder->setImplicit(true);
  Placeholder->setInitStyle(VarDecl::CInit);
  Placeholder->setInit(
      new (SemaRef.Context) OpaqueValueExpr(IdLoc, T, VK_RValue));
  Placeholder->setReferenced(true);
  Placeholder->markUsed(SemaRef.Context);
  Frag->addDecl(Placeholder);
}

static void CreatePlaceholders(Sema &SemaRef, CXXFragmentDecl *Frag, 
                               SmallVectorImpl<Expr *> &Captures) {
  std::for_each(Captures.begin(), Captures.end(), [&](Expr *E) {
    CreatePlaceholder(SemaRef, Frag, E);
  });
}

/// Called at the start of a source code fragment to establish the list of
/// automatic variables captured. This is only called by the parser and searches
/// the list of local variables in scope.
void Sema::ActOnCXXFragmentCapture(SmallVectorImpl<Expr *> &Captures) {
  assert(Captures.empty() && "Captures already specified");
  SmallVector<VarDecl *, 8> Vars;
  FindCaptures(*this, CurScope, getCurFunctionDecl(), Vars);
  ReferenceCaptures(*this, Vars, Captures);
}

/// Called at the start of a source code fragment to establish the fragment
/// declaration and placeholders. 
Decl *Sema::ActOnStartCXXFragment(Scope* S, SourceLocation Loc, 
                                  SmallVectorImpl<Expr *> &Captures) {
  CXXFragmentDecl *Fragment = CXXFragmentDecl::Create(Context, CurContext, Loc);
  CreatePlaceholders(*this, Fragment, Captures);
  if (S)
    PushDeclContext(S, Fragment);
  return Fragment;
}

/// Binds the content the fragment declaration. Returns the updated fragment.
/// The Fragment is nullptr if an error occurred during parsing. However,
/// we still need to pop the declaration context.
Decl *Sema::ActOnFinishCXXFragment(Scope *S, Decl *Fragment, Decl *Content) {
  CXXFragmentDecl *FD = nullptr;
  if (Fragment) {
    FD = cast<CXXFragmentDecl>(Fragment);
    FD->setContent(Content);
  }
  
  if (S)
    PopDeclContext();
  
  return FD;
}

/// Builds a new fragment expression.
ExprResult Sema::ActOnCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  return BuildCXXFragmentExpr(Loc, Captures, Fragment);
}

/// \brief Builds a new fragment expression.
/// Consider the following:
///
///   constexpr {
///     int n = 0;
///     auto x = __fragment class { int a, b, c };
///   }
///
/// The type of the expression is a new meta:: class defined, approximately,
/// like this:
///
///   using __base_type = typename($<fragment>); // for exposition
///   
///   struct __fragment_type : base_type
///     // inherit constructors.
///     using base_type::base_type;
///
///     // storage for capture values.
///     int n;
///   };
///
/// TODO: It seems like the base class subobject can be statically initialized
/// as part of a default constructor instead of providing an inherited 
/// constructor and deferring all initialization until evaluation time.
ExprResult Sema::BuildCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  CXXFragmentDecl *FD = cast<CXXFragmentDecl>(Fragment);

  // If the fragment appears in a context that depends on template parameters,
  // then the expression is dependent.
  //
  // FIXME: This is just an approximation of the right answer. In truth, the
  // expression is dependent if the fragment depends on any template parameter
  // in this or any enclosing context.
  if (CurContext->isDependentContext()) {
    return new (Context) CXXFragmentExpr(Context, Loc, Context.DependentTy, 
                                         Captures, FD, nullptr);
  }

  // Build the expression used to the reflection of fragment.
  //
  // TODO: We should be able to compute the type without generating an
  // expression. We're not actually using the expression.
  ExprResult Reflection = BuildDeclReflection(Loc, FD->getContent());
  if (Reflection.isInvalid())
    return ExprError();

  // Generate a fragment expression type.
  //
  // TODO: We currently use the declaration-global Fragment bit to indicate
  // that the type of the expression is (indeed) a reflection of some kind.
  // We might want create the class in the meta:: namespace and rely on only
  // that information.
  CXXRecordDecl *Class = CXXRecordDecl::Create(
      Context, TTK_Class, CurContext, Loc, Loc, nullptr, nullptr);
  Class->setImplicit(true);
  Class->setFragment(true);
  StartDefinition(Class);
  QualType ClassTy = Context.getRecordType(Class);
  TypeSourceInfo *ClassTSI = Context.getTrivialTypeSourceInfo(ClassTy);

  // Build the base class for the fragment type; this is the type of the
  // reflected entity.s
  QualType BaseTy = Reflection.get()->getType();
  TypeSourceInfo *BaseTSI = Context.getTrivialTypeSourceInfo(BaseTy);
  CXXBaseSpecifier* Base = new (Context) CXXBaseSpecifier(
    SourceRange(Loc, Loc), false, true, AS_public, BaseTSI, SourceLocation());
  Class->setBases(&Base, 1);

  // Create a field for each capture.
  SmallVector<FieldDecl *, 4> Fields;
  for (Expr *E : Captures) {
    VarDecl *Var = GetVariableFromCapture(E);
    std::string Name = "__captured_" + Var->getIdentifier()->getName().str();
    IdentifierInfo *Id = &Context.Idents.get(Name);
    TypeSourceInfo *TypeInfo = Context.getTrivialTypeSourceInfo(Var->getType());
    FieldDecl *Field = FieldDecl::Create(
        Context, Class, Loc, Loc, Id, Var->getType(), TypeInfo, nullptr, false, 
        ICIS_NoInit);
    Field->setAccess(AS_public);
    Field->setImplicit(true);
    Fields.push_back(Field);
    Class->addDecl(Field);
  }
  
  // Build a constructor that accepts the generated members.
  DeclarationName Name = Context.DeclarationNames.getCXXConstructorName(
      Context.getCanonicalType(ClassTy));
  DeclarationNameInfo NameInfo(Name, Loc);
  CXXConstructorDecl *Ctor = CXXConstructorDecl::Create(
      Context, Class, Loc, NameInfo, /*Type*/QualType(), /*TInfo=*/nullptr, 
      /*isExplicit=*/true, /*isInline=*/true, /*isImplicitlyDeclared=*/false, 
      /*isConstexpr=*/true);
  Ctor->setAccess(AS_public);

  // Build the function type for said constructor.
  FunctionProtoType::ExtProtoInfo EPI;
  EPI.ExceptionSpec.Type = EST_Unevaluated;
  EPI.ExceptionSpec.SourceDecl = Ctor;
  EPI.ExtInfo = EPI.ExtInfo.withCallingConv(
      Context.getDefaultCallingConvention(/*IsVariadic=*/false,
                                          /*IsCXXMethod=*/true));
  SmallVector<QualType, 4> ArgTypes;
  for (Expr *E : Captures) 
    ArgTypes.push_back(E->getType());
  QualType CtorTy = Context.getFunctionType(Context.VoidTy, ArgTypes, EPI);
  Ctor->setType(CtorTy);

  SmallVector<ParmVarDecl *, 4> Parms;
  for (std::size_t I = 0; I < Captures.size(); ++I) {
    Expr *E = Captures[I];
    VarDecl *Var = GetVariableFromCapture(E);
    std::string Name = "__parm_" + Var->getIdentifier()->getName().str();
    IdentifierInfo* Id = &Context.Idents.get(Name);
    QualType ParmTy = E->getType();
    TypeSourceInfo *TypeInfo = Context.getTrivialTypeSourceInfo(ParmTy);
    ParmVarDecl *Parm = ParmVarDecl::Create(
        Context, Ctor, Loc, Loc, Id, ParmTy, TypeInfo, SC_None, nullptr);
    Parm->setScopeInfo(0, I);
    Parm->setImplicit(true);
    Parms.push_back(Parm);
  }
  Ctor->setParams(Parms);

  // Build constructor initializers.
  std::size_t NumInits = Fields.size() + 1;
  CXXCtorInitializer **Inits = new (Context) CXXCtorInitializer *[NumInits];
  // Build the base initializer.
  {
    SourceLocation EL; // Empty ellipsis.
    Expr *Arg = new (Context) ParenListExpr(Context, Loc, None, Loc);
    Inits[0] = BuildBaseInitializer(BaseTy, BaseTSI, Arg, Class, EL).get();
  }
  // Build member initializers.
  for (std::size_t I = 0; I < Parms.size(); ++I) {
    ParmVarDecl *Parm = Parms[I];
    FieldDecl *Field = Fields[I];
    DeclRefExpr *Ref = new (Context) DeclRefExpr(
        Parm, false, Parm->getType(), VK_LValue, Loc);
    Expr *Arg = new (Context) ParenListExpr(Context, Loc, Ref, Loc);
    Inits[I + 1] = BuildMemberInitializer(Field, Arg, Loc).get();
  }
  Ctor->setNumCtorInitializers(NumInits);
  Ctor->setCtorInitializers(Inits);

  // Build the definition.
  Stmt *Def = new (Context) CompoundStmt(Context, None, Loc, Loc);
  Ctor->setBody(Def);

  Class->addDecl(Ctor);

  CompleteDefinition(Class);

  // Build an expression that that initializes the fragment object.
  Expr *Init;
  if (Captures.size() == 1) {
    CXXConstructExpr *Cast = CXXConstructExpr::Create(
        Context, ClassTy, Loc, Ctor, true, Captures,
        /*HadMultipleCandidates=*/false, /*ListInitialization=*/false, 
        /*StdInitListInitialization=*/false, /*ZeroInitialization=*/false,
        CXXConstructExpr::CK_Complete, SourceRange(Loc, Loc));
    Init = CXXFunctionalCastExpr::Create(
        Context, ClassTy, VK_RValue, ClassTSI, CK_NoOp, Cast, 
        /*Path=*/nullptr, Loc, Loc);
  } else {
    Init = new (Context) CXXTemporaryObjectExpr(
        Context, Ctor, ClassTy, ClassTSI, Captures, SourceRange(Loc, Loc), 
        /*HadMultipleCandidates=*/false, /*ListInitialization=*/false, 
        /*StdInitListInitialization=*/false, /*ZeroInitialization=*/false);
  }

  // Finally, build the fragment expression.
  return new (Context) CXXFragmentExpr(Context, Loc, ClassTy, Captures, FD, Init);
}

/// Returns an injection statement.
StmtResult Sema::ActOnCXXInjectionStmt(SourceLocation Loc, Expr *Reflection) { 
  return BuildCXXInjectionStmt(Loc, Reflection);
}

/// Returns an injection statement.
StmtResult Sema::BuildCXXInjectionStmt(SourceLocation Loc, Expr *Reflection) { 
  // The operand must be a reflection (if non-dependent).
  if (!Reflection->isTypeDependent() && !Reflection->isValueDependent()) {
    if (!isReflectionType(Reflection->getType())) {
      Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
      return StmtError();
    }
  }

  // Perform an lvalue-to-value conversion so that we get an rvalue in
  // evaluation.
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  return new (Context) CXXInjectionStmt(Loc, Reflection);
}

/// An injection declaration injects its fragment members at this point
/// in the program. 
StmtResult Sema::ActOnCXXExtensionStmt(SourceLocation Loc, 
                                       Expr *Target,
                                       Expr *Reflection) { 
  llvm_unreachable("extension not supported");
  // return BuildCXXExtensionStmt(Loc, Target, Reflection);
}

StmtResult Sema::BuildCXXExtensionStmt(SourceLocation Loc, Expr *Target,
                                       Expr *Reflection) { 
  llvm_unreachable("extension not supported");
#if 0
  // Check the glvalue.
  if (!Target->isTypeDependent()) {
    // FIXEM: This isn't strictly *required* since even prvalues are just
    // pointers to a mutable data structure. This is disabled, because the
    // reflection operator returns prvalues, which complicates certain
    // use patterns. For example:
    //
    //    struct C {
    //      constexpr { fill($C); } // Would be an error.
    //    };
    //
    // So, disable this for now.

    // if (!Target->isGLValue()) {
    //   Diag(Target->getExprLoc(), diag::err_extending_rvalue);
    //   return StmtError();
    // }
    
    QualType TargetTy = Context.getCanonicalType(Target->getType());
    if (CXXRecordDecl* Class = TargetTy->getAsCXXRecordDecl()) {
      // FIXME: This isn't the right test. We need to determine during 
      // application if the target satisfies the requirements for extensions.
      // if (!Class->isFragment() || !Class->isBeingDefined()) {
      //   Diag(Target->getExprLoc(), diag::err_extending_declaration);
      //   return StmtError();
      // }
    } else {
      Diag(Target->getExprLoc(), diag::err_extending_non_reflection);
      return StmtError();
    }
  }

  // FIXME: If the reflection is non-dependent, verify that we actually
  // have a reflection.

  // Force an lvalue-to-rvalue conversion.
  if (Target->isGLValue())
    Target = ImplicitCastExpr::Create(Context, Target->getType(), 
                                      CK_LValueToRValue, Target, 
                                      nullptr, VK_RValue);
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  // Build an extension statement that can be evaluated when executed.
  return new (Context) CXXExtensionStmt(Loc, Target, Reflection);
#endif
}

static Decl *
GetDeclFromReflection(Sema &SemaRef, QualType Ty, SourceLocation Loc)
{
  ReflectedConstruct Construct = SemaRef.EvaluateReflection(Ty, Loc);
  Decl *Injection = nullptr;
  if (Type *T = Construct.getAsType()) {
    if (CXXRecordDecl *Class = T->getAsCXXRecordDecl())
      Injection = Class;
  } else
    Injection = Construct.getAsDeclaration();
  if (!Injection) {
    SemaRef.Diag(Loc, diag::err_reflection_not_a_decl);
    return nullptr;
  }
  return Injection;
}

// Not used.
#if 0
static Decl *
GetDeclFromReflection(Sema &SemaRef, Expr *Reflection)
{
  return GetDeclFromReflection(SemaRef, 
                               Reflection->getType(),
                               Reflection->getExprLoc());
}
#endif

/// An injection declaration injects its fragment members at this point
/// in the program. 
Sema::DeclGroupPtrTy Sema::ActOnCXXInjectionDecl(SourceLocation Loc, 
                                                 Expr *Reflection) { 
  llvm_unreachable("injection declarations not supported");
  #if 0
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    Decl *D = CXXInjectionDecl::Create(Context, CurContext, Loc, Reflection);
    // FIXME: Actually use the current access specifier. For now, simply
    // assume that public was meant.
    if (isa<CXXRecordDecl>(CurContext))
      D->setAccess(AS_public);
    CurContext->addDecl(D);
    return DeclGroupPtrTy::make(DeclGroupRef(D));
  }

  // Force an lvalue-to-rvalue conversion.
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  // Get the declaration or fragment to be injected.
  Decl *Injection = GetDeclFromReflection(*this, Reflection);
  if (!Injection)
    return DeclGroupPtrTy();

  // The Injectee is the current context.
  Decl *Injectee = Decl::castFromDeclContext(CurContext);

  // Evaluate the reflection.
  SmallVector<PartialDiagnosticAt, 8> Notes;
  Expr::EvalResult Result;
  Result.Diag = &Notes;
  if (!Reflection->EvaluateAsRValue(Result, Context)) {
    // FIXME: This is not the right error.
    Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
    if (!Notes.empty()) {
      for (const PartialDiagnosticAt &Note : Notes)
        Diag(Note.first, Note.second);
    }
    return DeclGroupPtrTy();
  }

  // FIXME: If this is a fragment without a name, that should probably
  // be an error, right?

  // Always copy the injected declaration.
  QualType Ty = Reflection->getType();
  SmallVector<Decl *, 8> Decls;
  if (!CopyDeclaration(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
    return DeclGroupPtrTy();

  if (Decls.empty()) {
    return DeclGroupPtrTy();
  } else if (Decls.size() == 1) {
    return DeclGroupPtrTy::make(DeclGroupRef(Decls.front()));
  } else {
    DeclGroup *DG = DeclGroup::Create(Context, Decls.data(), Decls.size());
    return DeclGroupPtrTy::make(DeclGroupRef(DG));
  }
  #endif
}

static ClassTemplateSpecializationDecl *ReferencedReflectionClass(Sema &SemaRef, 
                                                                  Expr *E) {
  QualType ExprTy = SemaRef.Context.getCanonicalType(E->getType());
  if (!ExprTy->isRecordType())
    return nullptr;
  CXXRecordDecl* Class = ExprTy->getAsCXXRecordDecl();
  if (!isa<ClassTemplateSpecializationDecl>(Class))
    return nullptr;
  ClassTemplateSpecializationDecl *Spec 
      = cast<ClassTemplateSpecializationDecl>(Class);

  // Make sure that this is actually defined in meta.
  DeclContext* Owner = Class->getDeclContext();
  if (Owner->isInlineNamespace())
    Owner = Owner->getParent();
  if (!Owner->Equals(SemaRef.RequireCppxMetaNamespace(E->getExprLoc()))) 
    return nullptr;
  return Spec;
}

// Returns true if ExprTy refers to either a reflected function or the 
// parameters of a function. If true, Ref is set to the type containing the 
// function's encoded value.
static bool ReferencesFunction(Sema &SemaRef, Expr *E, QualType &RefTy)
{
  auto *Spec = ReferencedReflectionClass(SemaRef, E);
  if (!Spec)
    return false;
  StringRef Name = Spec->getIdentifier()->getName();
  if (Name == "function") {
    RefTy = SemaRef.Context.getTagDeclType(Spec);
    return true;
  }
  if (Name == "reflected_tuple") {
    // Dig out the class containing the info type. It should be:
    //    reflected_tupe<function<X>::parm_info>.
    TemplateArgument First = Spec->getTemplateArgs()[0];
    if (First.getKind() != TemplateArgument::Type)
      return false;
    QualType T = First.getAsType();
    if (!T->isRecordType())
      return false;
    CXXRecordDecl *Class = T->getAsCXXRecordDecl();
    if (Class->getIdentifier()->getName() != "parm_info")
        return false;
    if (!Class->getDeclContext()->isRecord())
      return false;
    Class = cast<CXXRecordDecl>(Class->getDeclContext());
    if (Class->getIdentifier()->getName() != "function" &&
        Class->getIdentifier()->getName() != "method")
      return false;
    RefTy = SemaRef.Context.getTagDeclType(Class);
    return true;
  }

  return false;
}

// Returns true if E refers to a reflected parameter. If true, then Ref is
// set to the type containing the parameter's encoded value.
static bool ReferencesParameter(Sema &SemaRef, Expr *E, QualType &RefTy) {
  auto *Spec = ReferencedReflectionClass(SemaRef, E);
  if (!Spec)
    return false;
  StringRef Name = Spec->getIdentifier()->getName();
  if (Name == "parameter") {
    RefTy = SemaRef.Context.getTagDeclType(Spec);
    return true;
  }
  return false;
}

bool Sema::ActOnCXXInjectedParameter(SourceLocation Loc, Expr *Reflection,
                                     IdentifierInfo *II,
                           SmallVectorImpl<DeclaratorChunk::ParamInfo> &Parms) {
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    // The type is an injected parameter type.
    QualType T = Context.getInjectedParmType(Reflection);
    TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(T);

    // FIXME: Make the constructor accept the type.
    ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                           Context.getTranslationUnitDecl(), 
                                           Loc, Loc, II, T, TSI, SC_None,
                                           nullptr);    
      New->setScopeInfo(CurScope->getFunctionPrototypeDepth(),
                        CurScope->getNextFunctionPrototypeIndex());
    Parms.push_back(DeclaratorChunk::ParamInfo(nullptr, Loc, New));
    return true;
  }

  // If T is meta::function<X> or reflected_tuple<meta::function<X>::parm_info>
  // Then EllipsisLoc must be valid, and we inject all parameters.
  QualType RefTy;
  if (ReferencesFunction(*this, Reflection, RefTy)) {
    ReflectedConstruct C = EvaluateReflection(RefTy, Reflection->getExprLoc());
    FunctionDecl *Fn = cast<FunctionDecl>(C.getAsDeclaration());

    // Clone each parameter, inserting a chunk for the declaration.
    for (ParmVarDecl *Orig : Fn->parameters()) {
      TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(Orig->getType());
      ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                             Context.getTranslationUnitDecl(), 
                                             Orig->getLocStart(), 
                                             Orig->getLocation(), 
                                             Orig->getIdentifier(),
                                             Orig->getType(), TSI, SC_None,
                                             nullptr);
      New->setScopeInfo(CurScope->getFunctionPrototypeDepth(),
                        CurScope->getNextFunctionPrototypeIndex());
      New->setInjected(true);
      Parms.push_back(DeclaratorChunk::ParamInfo(New->getIdentifier(),
                                                 New->getLocation(), New));
    }
    return true;
  }

  // If T is meta::parameter<X>, then we inject that one parameter.
  if (ReferencesParameter(*this, Reflection, RefTy)) {
    // Clone the referenced parameter.
    ReflectedConstruct C = EvaluateReflection(RefTy, Reflection->getExprLoc());
    ParmVarDecl *Orig = cast<ParmVarDecl>(C.getAsDeclaration());
    TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(Orig->getType());
    ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                           Context.getTranslationUnitDecl(),
                                           Orig->getLocStart(), 
                                           Orig->getLocation(), 
                                           Orig->getIdentifier(),
                                           Orig->getType(), TSI, SC_None,
                                           nullptr);
    New->setScopeInfo(CurScope->getFunctionPrototypeDepth(), 
                      CurScope->getNextFunctionPrototypeIndex());
    New->setInjected(true);
    Parms.push_back(DeclaratorChunk::ParamInfo(New->getIdentifier(),
                                               New->getLocation(), New));
    return true;
  }

  // FIXME: Improve diagnostics.
  Diag(Reflection->getExprLoc(), diag::err_compiler_error) << "invalid parameter";
  return false;
}

QualType Sema::BuildInjectedParmType(SourceLocation Loc, Expr *E) {
  if (E->isTypeDependent())
    return Context.getInjectedParmType(E);

  MarkDeclarationsReferencedInExpr(E);
  
  // If T is meta::function<X> or reflected_tuple<meta::function<X>::parm_info>
  // Then EllipsisLoc must be valid, and we inject all parameters.
  QualType RefTy;
  if (ReferencesFunction(*this, E, RefTy)) {
    ReflectedConstruct C = EvaluateReflection(RefTy, E->getExprLoc());
    FunctionDecl *Fn = cast<FunctionDecl>(C.getAsDeclaration());
    return Context.getInjectedParmType(E, Fn->parameters());
  }

  // If T is meta::parameter<X>, then we inject that one parameter.
  if (ReferencesParameter(*this, E, RefTy)) {
    llvm_unreachable("not implemented");
  }

  // FIXME: Improve diagnostics.
  Diag(E->getExprLoc(), diag::err_compiler_error) << "invalid parameter";
  return QualType();
}


// Returns an integer value describing the target context of the injection.
// This correlates to the second %select in err_invalid_injection.
static int DescribeInjectionTarget(DeclContext *DC) {
  if (DC->isFunctionOrMethod())
    return 0;
  else if (DC->isRecord())
    return 1;
  else if (DC->isNamespace())
    return 2;
  else if (DC->isTranslationUnit())
    return 3;
  else
    llvm_unreachable("Invalid injection context");
}

struct TypedValue
{
  QualType Type;
  APValue Value;
};

// Generate an error injecting a declaration of kind SK into the given 
// declaration context. Returns false. Note that SK correlates to the first
// %select in err_invalid_injection.
static bool InvalidInjection(Sema& S, SourceLocation POI, int SK, 
                             DeclContext *DC) {
  S.Diag(POI, diag::err_invalid_injection) << SK << DescribeInjectionTarget(DC);
  return false;
}

// FIXME: This is not particularly good. It would be nice if we didn't have
// to search for ths field.s
static const APValue& GetModifications(const APValue &V, QualType T,
                                       DeclarationName N)
{
  CXXRecordDecl *Class = T->getAsCXXRecordDecl();
  assert(Class && "Expected a class");

  auto Lookup = Class->lookup(N);
  assert(Lookup.size() <= 1 && "Ambiguous reference to traits");
  if (Lookup.empty()) {
    // If we can't find the field, work up recursively.
    if (Class->getNumBases()) {
      CXXBaseSpecifier &B = *Class->bases().begin();
      return GetModifications(V.getStructBase(0), B.getType(), N);
    }
  }
  FieldDecl *F = cast<FieldDecl>(Lookup.front());
  return V.getStructField(F->getFieldIndex());
}

static bool CheckInjectionContexts(Sema &SemaRef, SourceLocation POI,
                                   DeclContext *Injection,
                                   DeclContext *Injectee) {
  if (Injection->isRecord() && !Injectee->isRecord()) {
    InvalidInjection(SemaRef, POI, 1, Injectee);
    return false;
  } else if (Injection->isFileContext() && !Injectee->isFileContext()) {
    InvalidInjection(SemaRef, POI, 0, Injectee);
    return false;
  }
  return true;
}

static bool CheckInjectionKind(Sema &SemaRef, SourceLocation POI,
                               Decl *Injection, DeclContext *Injectee) {
  // Make sure that injection is marginally sane.
  if (VarDecl *Var = dyn_cast<VarDecl>(Injection)) {
    if (Var->hasLocalStorage() && !Injectee->isFunctionOrMethod()) {
      SemaRef.Diag(POI, diag::err_injecting_local_into_invalid_scope)
        << Injectee->isRecord();
      return false;
    }
  }
  return true;
}

/// Inject a fragment into the current context.
bool Sema::InjectFragment(SourceLocation POI, 
                          QualType ReflectionTy, 
                          const APValue &ReflectionVal, 
                          Decl *Injectee, 
                          Decl *Injection) {
  assert(isa<CXXRecordDecl>(Injection) || isa<NamespaceDecl>(Injection));
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);
  DeclContext *InjectionDC = Decl::castToDeclContext(Injection);

  if (!CheckInjectionContexts(*this, POI, InjectionDC, InjecteeDC))
    return false;

  // Extract the captured values for replacement.
  unsigned NumCaptures = ReflectionVal.getStructNumFields();
  ArrayRef<APValue> Captures(None);
  if (NumCaptures) {
    const APValue *First = &ReflectionVal.getStructField(0);
    Captures = ArrayRef<APValue>(First, NumCaptures);
  }

  CXXRecordDecl *Class = ReflectionTy->getAsCXXRecordDecl();
  CXXFragmentDecl *Fragment = cast<CXXFragmentDecl>(Injection->getDeclContext());

  ContextRAII Switch(*this, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // Establish the injection context and register the substitutions.
  InjectionContext *Cxt = new InjectionContext(*this, Fragment, InjecteeDC, Injection);
  Cxt->AddDeclSubstitution(Injection, Injectee);
  Cxt->AddPlaceholderSubstitutions(Fragment, Class, Captures);

  // Inject each declaration in the fragment.
  for (Decl *D : InjectionDC->decls()) {
    // Never inject injected class names.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(D))
      if (Class->isInjectedClassName())
        continue;

    // llvm::outs() << "BEFORE INJECT\n";
    // D->dump();
    
    Decl *R = Cxt->InjectDecl(D);
    if (!R || R->isInvalidDecl()) {
      // if (R && R->isInvalidDecl()) {
      //   llvm::outs() << "INVALID INJECT\n";
      //   R->dump();
      // }
      Injectee->setInvalidDecl(true);
      continue;
    }

    // llvm::outs() << "AFTER INJECT\n";
    // R->dump();
  }

  // If we're injecting into a class and have pending definitions, attach
  // those to the class for subsequent analysis. 
  if (CXXRecordDecl *ClassInjectee = dyn_cast<CXXRecordDecl>(Injectee)) {
    if (!Injectee->isInvalidDecl() && !Cxt->InjectedDefinitions.empty()) {
      PendingClassMemberInjections.push_back(Cxt->Detach());
      return true;
    }
  }

  delete Cxt;
  return !Injectee->isInvalidDecl();
}

/// FIXME: Make this part of the injection context?
static Decl *RewriteAsStaticMemberVariable(InjectionContext &Cxt, FieldDecl *D) {
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = Cxt.InjectMemberDeclarator(D, DNI, TSI, Owner);
  
  VarDecl *Var = VarDecl::Create(
      Cxt.getContext(), Owner, D->getLocation(), DNI, TSI->getType(), 
      TSI, SC_Static);
  Cxt.AddDeclSubstitution(D, Var);
  
  Var->setAccess(D->getAccess());
  Var->setInvalidDecl(Invalid);
  Owner->addDecl(Var);

  // FIXME: This is almost certainly going to break when it runs.
  // if (D->hasInClassInitializer())
  //   Cxt.InjectedDefinitions.push_back(InjectedDef(D, Var));

  if (D->hasInClassInitializer())
    llvm_unreachable("Initialization of static members not implemented");

  return Var;
}

/// Clone a declaration into the current context.
bool Sema::CopyDeclaration(SourceLocation POI, 
                           QualType ReflectionTy, 
                           const APValue &ReflectionVal,
                           Decl *Injectee, 
                           Decl *Injection) {
  DeclContext *InjectionDC = Injection->getDeclContext();
  Decl *InjectionOwner = Decl::castFromDeclContext(InjectionDC);
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);

  // Don't copy injected class names.
  if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(Injection))
    if (Class->isInjectedClassName())
      return true;

  if (!CheckInjectionContexts(*this, POI, InjectionDC, InjecteeDC))
    return false;

  if (!CheckInjectionKind(*this, POI, Injection, InjecteeDC))
    return false;

  // Set up the injection context for the declaration. Note that we're
  // going to replace references to the inectee with the current owner.
  InjectionContext *Cxt = new InjectionContext(*this, InjecteeDC, Injection);
  Cxt->AddDeclSubstitution(InjectionOwner, Injectee);

  // Establish injectee as the current context.
  ContextRAII Switch(*this, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // Unpack the modification traits so we can apply them after generating
  // the declaration.
  DeclarationName Name(&Context.Idents.get("mods"));
  const APValue &Traits = GetModifications(ReflectionVal, ReflectionTy, Name);

  enum StorageMod { NoStorage, Static, Automatic, ThreadLocal };
  enum AccessMod { NoAccess, Public, Private, Protected, Default };

  // linkage_kind new_linkage : 2;
  // access_kind new_access : 2;
  // storage_kind new_storage : 2;
  // bool make_constexpr : 1;
  // bool make_virtual : 1;
  // bool make_pure : 1;
  AccessMod Access = (AccessMod)Traits.getStructField(1).getInt().getExtValue();
  StorageMod Storage = (StorageMod)Traits.getStructField(2).getInt().getExtValue();
  bool Constexpr = Traits.getStructField(3).getInt().getExtValue();
  bool Virtual = Traits.getStructField(4).getInt().getExtValue();
  bool Pure = Traits.getStructField(5).getInt().getExtValue();

  assert(Storage != Automatic && "Can't make declarations automatic");
  assert(Storage != ThreadLocal && "Thread local storage not implemented");

  // llvm::outs() << "BEFORE CLONE\n";
  // Injection->dump();
  // Injectee->dump();

  // Build the declaration. If there was a request to make field static, we'll
  // need to build a new declaration.
  Decl* Result;
  if (isa<FieldDecl>(Injection) && Storage == Static)
    Result = RewriteAsStaticMemberVariable(*Cxt, cast<FieldDecl>(Injection));
  else
    Result = Cxt->InjectDecl(Injection);
  if (!Result || Result->isInvalidDecl()) {
    Injectee->setInvalidDecl(true);
    return false;
  }
  
  // llvm::outs() << "AFTER CLONING\n";
  // Result->dump();
  // Injectee->dump();

  // Update access specifiers.
  if (Access) {
    if (!Result->getDeclContext()->isRecord()) {
      Diag(POI, diag::err_modifies_mem_spec_of_non_member) << 0;
      return false;
    }
    switch (Access) {
    case Public:
      Result->setAccess(AS_public);
      break;
    case Private:
      Result->setAccess(AS_private);
      break;
    case Protected:
      Result->setAccess(AS_protected);
      break;
    default:
      llvm_unreachable("Invalid access specifier");
    }
  } else {
    // FIXME: In some cases (nested classes?) member access specifiers
    // are not inherited from the fragments. Force this to be public for now.
    if (isa<CXXRecordDecl>(InjecteeDC)) {
      if (Result->getAccess() == AS_none)
        Result->setAccess(AS_public);
    }
  }

  if (Constexpr) {
    if (VarDecl *Var = dyn_cast<VarDecl>(Result)) {
      Var->setConstexpr(true);
      CheckVariableDeclarationType(Var);
    }
    else if (isa<CXXDestructorDecl>(Result)) {
      Diag(POI, diag::err_declration_cannot_be_made_constexpr);
      return false;
    }
    else if (FunctionDecl *Fn = dyn_cast<FunctionDecl>(Result)) {
      Var->setConstexpr(true);
      CheckConstexprFunctionDecl(Fn);
    } else {
      // Non-members cannot be virtual.
      Diag(POI, diag::err_virtual_non_function);
      return false;
    }
  }

  if (Virtual) {
    if (!isa<CXXMethodDecl>(Result)) {
      Diag(POI, diag::err_virtual_non_function);
      return false;
    }
    
    CXXMethodDecl *Method = cast<CXXMethodDecl>(Result);
    Method->setVirtualAsWritten(true);
  
    if (Pure) {
      // FIXME: Move pure checks up?
      int Err = 0;
      if (Method->isDefaulted()) Err = 2;
      else if (Method->isDeleted()) Err = 3;
      else if (Method->isDefined()) Err = 1;
      if (Err) {
        Diag(POI, diag::err_cannot_make_pure_virtual) << (Err - 1);
        return false;
      }
      CheckPureMethod(Method, Method->getSourceRange());
    }
  }

  // Finally, update the owning context.
  Result->getDeclContext()->updateDecl(Result);


  // If we're injecting into a class and have pending definitions, attach
  // those to the class for subsequent analysis. 
  if (CXXRecordDecl *ClassInjectee = dyn_cast<CXXRecordDecl>(Injectee)) {
    if (!Injectee->isInvalidDecl() && !Cxt->InjectedDefinitions.empty()) {
      PendingClassMemberInjections.push_back(Cxt->Detach());
      return true;
    }
  }
  return !Injectee->isInvalidDecl(); 
}

bool Sema::ApplyInjection(SourceLocation POI, InjectionInfo &II) {
  // Get the injection declaration.
  Decl *Injection = GetDeclFromReflection(*this, II.ReflectionType, POI);

  /// Get the injectee declaration. This is either the one specified or
  /// the current context.
  Decl *Injectee = nullptr;
  if (!II.InjecteeType.isNull())
    Injectee = GetDeclFromReflection(*this, II.InjecteeType, POI);
  else
    Injectee = Decl::castFromDeclContext(CurContext);
  if (!Injectee)
    return false;

  // FIXME: Make sure that we can actually apply the injection to the
  // target context. For example, we should only be able to extend fragments
  // or classes currently being defined. We'll need to incorporate the kind
  // of extension operator into the InjectionInfo.

  // Apply the injection operation.
  QualType Ty = II.ReflectionType;
  const APValue &Val = II.ReflectionValue;
  CXXRecordDecl *Class = Ty->getAsCXXRecordDecl();
  if (Class->isFragment())
    return InjectFragment(POI, Ty, Val, Injectee, Injection);
  else
    return CopyDeclaration(POI, Ty, Val, Injectee, Injection);
}

// static void
// PrintDecl(Sema &SemaRef, Decl *D) {
//   PrintingPolicy PP = SemaRef.Context.getPrintingPolicy();
//   PP.TerseOutput = false;
//   D->print(llvm::errs(), PP);
//   llvm::errs() << '\n';
// }

// static void
// PrintType(Sema &SemaRef, Type *T) {
//   if (TagDecl *TD = T->getAsTagDecl())
//     return PrintDecl(SemaRef, TD);
//   PrintingPolicy PP = SemaRef.Context.getPrintingPolicy();
//   QualType QT(T, 0);
//   QT.print(llvm::errs(), PP);
//   llvm::errs() << '\n';
// }

static bool
ApplyDiagnostic(Sema &SemaRef, SourceLocation Loc, const APValue &Arg) {
  ReflectedConstruct R(Arg.getInt().getExtValue());
  if (Decl *D = R.getAsDeclaration()) {
    D->dump();
    // PrintDecl(SemaRef, D);
  }
  else if (Type *T = R.getAsType()) {
    if (TagDecl *TD = T->getAsTagDecl())
      TD->dump();
    else
      T->dump();
    // PrintType(SemaRef, T);
  }
  else
    llvm_unreachable("printing invalid reflection");
  return true;
}

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplyEffects(SourceLocation POI, 
                        SmallVectorImpl<EvalEffect> &Effects) {
  bool Ok = true;
  for (EvalEffect &Effect : Effects) {
    if (Effect.Kind == EvalEffect::InjectionEffect)
      Ok &= ApplyInjection(POI, *Effect.Injection);
    else
      Ok &= ApplyDiagnostic(*this, POI, *Effect.DiagnosticArg);
  }
  return Ok;
}

void Sema::InjectPendingDefinitions() {
  while (!PendingClassMemberInjections.empty()) {
    InjectionContext *Cxt = PendingClassMemberInjections.back();
    PendingClassMemberInjections.pop_back();
    InjectPendingDefinitions(Cxt);
  }
}

void Sema::InjectPendingDefinitions(InjectionContext *Cxt) {
  Cxt->Attach();
  for (InjectedDef Def : Cxt->InjectedDefinitions)
    InjectPendingDefinition(Cxt, Def.Fragment, Def.Injected);
  delete Cxt;
}

void Sema::InjectPendingDefinition(InjectionContext *Cxt, 
                                   Decl *Frag, 
                                   Decl *New) {
  ContextRAII ClassCxt (*this, Frag->getDeclContext());
  if (FieldDecl *OldField = dyn_cast<FieldDecl>(Frag)) {
    FieldDecl *NewField = cast<FieldDecl>(New);
    ExprResult Init = Cxt->TransformExpr(OldField->getInClassInitializer());
    if (Init.isInvalid())
      NewField->setInvalidDecl();
    else
      NewField->setInClassInitializer(Init.get());
  }
  else if (CXXMethodDecl *OldMethod = dyn_cast<CXXMethodDecl>(Frag)) {
    CXXMethodDecl *NewMethod = cast<CXXMethodDecl>(New);
    ContextRAII MethodCxt (*this, NewMethod);
    StmtResult Body = Cxt->TransformStmt(OldMethod->getBody());
    if (Body.isInvalid())
      NewMethod->setInvalidDecl();
    else
      NewMethod->setBody(Body.get());
  }
}

Sema::DeclGroupPtrTy Sema::ActOnCXXGeneratedTypeDecl(SourceLocation UsingLoc,
                                                     bool IsClass,
                                                     SourceLocation IdLoc,
                                                     IdentifierInfo *Id,
                                                     Expr *Generator,
                                                     Expr *Reflection) {
  // Create the generated type.
  TagTypeKind TTK = IsClass ? TTK_Class : TTK_Struct;
  CXXRecordDecl *Class = CXXRecordDecl::Create(Context, TTK, CurContext, 
                                               IdLoc, IdLoc, Id);
  Class->setImplicit(true);

  // FIXME: Actually use the current access specifier.
  if (isa<CXXRecordDecl>(CurContext))
    Class->setAccess(AS_public);

  CurContext->addDecl(Class);
  StartDefinition(Class);

  // PushDeclContext(CurScope, Class);
  ContextRAII ClassContext(*this, Class);

  // FIXME: If the reflection (ref) is a fragment DO NOT insert the
  // prototype. A fragment is NOT a type.

  // Insert 'using prototype = typename(ref)'
  IdentifierInfo *ProtoId = &Context.Idents.get("prototype");
  QualType ProtoTy = BuildReflectedType(IdLoc, Reflection);
  TypeSourceInfo *ProtoTSI = Context.getTrivialTypeSourceInfo(ProtoTy);
  Decl *Alias = TypeAliasDecl::Create(Context, Class, IdLoc, IdLoc, 
                                      ProtoId, ProtoTSI);
  Alias->setImplicit(true);
  Alias->setAccess(AS_public);
  Class->addDecl(Alias);

  // Add 'constexpr { <gen>($<id>, <ref>); }' to the class.
  unsigned ScopeFlags;
  Decl *CD = ActOnConstexprDecl(nullptr, UsingLoc, ScopeFlags);
  CD->setImplicit(true);
  CD->setAccess(AS_public);
  
  ActOnStartConstexprDecl(nullptr, CD);
  SourceLocation Loc;

  // Build the expression $<id>.
  QualType ThisType = Context.getRecordType(Class);
  TypeSourceInfo *ThisTypeInfo = Context.getTrivialTypeSourceInfo(ThisType);
  ExprResult Output = ActOnCXXReflectExpr(IdLoc, ThisTypeInfo);

  // Build the call to <gen>($<id>, <ref>)
  Expr *Args[] {Output.get(), Reflection};
  ExprResult Call = ActOnCallExpr(nullptr, Generator, IdLoc, Args, IdLoc);
  Stmt* Body = new (Context) CompoundStmt(Context, Call.get(), IdLoc, IdLoc);

  ActOnFinishConstexprDecl(nullptr, CD, Body);

  CompleteDefinition(Class);
  PopDeclContext();
  
  return DeclGroupPtrTy::make(DeclGroupRef(Class));
}
