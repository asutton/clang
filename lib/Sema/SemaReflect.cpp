//===--- SemaReflect.cpp - Semantic Analysis for Reflection ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for C++ reflection.
//
//===----------------------------------------------------------------------===//

#include "TypeLocBuilder.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/SemaInternal.h"

using namespace clang;
using namespace sema;

/// FIXME: Move this to ASTContext.
bool Sema::isReflectionType(QualType T) {
  if (CXXRecordDecl *Class = T->getAsCXXRecordDecl()) {
    // Fragments are reflections.
    if (Class->isFragment())
      return true;

    // Reflections are specializations. 
    if (!isa<ClassTemplateSpecializationDecl>(Class)) 
      return false;
    
    // Reflections are defined in the meta namespace.
    DeclContext* Owner = Class->getDeclContext();
    if (Owner->isInlineNamespace())
      Owner = Owner->getParent();

    // FIXME: Don't emit errors if this fails, just return false.
    if (!Owner->Equals(RequireCppxMetaNamespace(SourceLocation())))
      return false;

    // FIXME: We should actually test the name of the class. This is mostly a
    // heuristic right now.
    return true;
  }
  
  return false;
}

static ExprResult ValueReflectionError(Sema &SemaRef, SourceLocation Loc) {
  SemaRef.Diag(Loc, diag::err_reflection_not_a_value);
  return ExprResult(true);
}

ReflectedConstruct Sema::EvaluateReflection(QualType T, SourceLocation Loc) {
  T = Context.getCanonicalType(T);
  CXXRecordDecl *Class = T->getAsCXXRecordDecl();
  if (!Class) {
    ValueReflectionError(*this, Loc);
    return ReflectedConstruct();
  }

  if (Class->isFragment()) {
    // If the class is a fragment, then uses its base type for the
    // evaluation.
    assert(Class->getNumBases() == 1 && "invalid injection");
    CXXBaseSpecifier &Base = *Class->bases_begin();
    Class = Base.getType()->getAsCXXRecordDecl();
  }

  // If the type is a reflection...
  if (!isa<ClassTemplateSpecializationDecl>(Class)) {
    Diag(Loc, diag::err_not_a_reflection);
    return ReflectedConstruct();
  }
  ClassTemplateSpecializationDecl *Spec = 
    cast<ClassTemplateSpecializationDecl>(Class);

  // Make sure that this is actually a metaclass.
  DeclContext* Owner = Spec->getDeclContext();
  if (Owner->isInlineNamespace())
    Owner = Owner->getParent();
  if (!Owner->Equals(RequireCppxMetaNamespace(Loc))) {
    Diag(Loc, diag::err_not_a_reflection);
    return ReflectedConstruct();
  }

  const TemplateArgumentList& Args = Spec->getTemplateArgs();
  if (Args.size() == 0) {
    ValueReflectionError(*this, Loc);
    return ReflectedConstruct();
  }

  const TemplateArgument &Arg = Args.get(0);
  if (Arg.getKind() != TemplateArgument::Integral) {
    ValueReflectionError(*this, Loc);
    return ReflectedConstruct();
  }
  
  // Decode the specialization argument.
  llvm::APSInt Data = Arg.getAsIntegral();
  return ReflectedConstruct(Data.getExtValue());  
}

ReflectedConstruct Sema::EvaluateReflection(Expr *E) {
  if (E->getType() == Context.getIntPtrType()) {
    // If this looks like an encoded integer, then evaluate it as such.
    //
    // FIXME: This is *really* unsafe.
    Expr::EvalResult Result;
    if (!E->EvaluateAsRValue(Result, Context)) {
      Diag(E->getExprLoc(), diag::err_expr_not_ice) << 1;
      return ReflectedConstruct();
    }
    return ReflectedConstruct(Result.Val.getInt().getExtValue());
  }
  return EvaluateReflection(E->getType(), E->getExprLoc());
}

/// Returns a reflected declaration or nullptr if E does not reflect a
/// declaration. If E reflects a user-defined type, then this returns the
/// declaration of that type.
Decl *Sema::GetReflectedDeclaration(Expr *E)
{
  ReflectedConstruct R = EvaluateReflection(E);
  Decl *D = R.getAsDeclaration();
  if (!D)
    if (Type *T = R.getAsType())
      D = T->getAsCXXRecordDecl();
  if (!D)
    Diag(E->getLocStart(), diag::err_invalid_reflection);
  return D;
}

/// The expression \c $x returns an object describing the reflected entity \c x.
/// The type of that object depends on the type of the thing reflected.
///
/// The \p E argument is not null.
ExprResult Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, Expr *E) {
  // Try to correct typos.
  if (isa<TypoExpr>(E)) {
    ExprResult Fixed = CorrectDelayedTyposInExpr(E);
    if (!Fixed.isUsable())
      return ExprError();
    E = Fixed.get();
  }

  // If the node is dependent, then preserve the expression until instantiation.
  if (E->isTypeDependent() || E->isValueDependent())
    return new (Context) ReflectionExpr(OpLoc, E, Context.DependentTy);

  if (OverloadExpr *Ovl = dyn_cast<OverloadExpr>(E)) {
    // FIXME: This should be okay. We should be able to provide a limited
    // interface to overloaded functions.
    return ExprError(Diag(OpLoc, diag::err_reflected_overload)
                     << Ovl->getSourceRange());
  }

  if (!isa<DeclRefExpr>(E)) {
    // We can get here when substituting through placeholders in a fragment.
    // For example:
    //
    //    constexpr {
    //      int n = 0;
    //      __generate ... {
    //        __inject $n;
    //      };
    //    }
    //
    // The fragment of __declare is a reflection whose operand refers to
    // a placeholder. When we inject the fragment the name 'n' is replaced
    // by a constant expression with n's value, not a reference to n. That's 
    // an error -- you couldn't declare a value anyway.
    Diag(E->getExprLoc(), diag::err_not_reflection);
    return ExprError();
  }

  // Build the reflection expression.
  return BuildDeclReflection(OpLoc, cast<DeclRefExpr>(E)->getDecl());
}

/// \brief Build a reflection for the type wrapped by \p TSI.
ExprResult Sema::ActOnCXXReflectExpr(SourceLocation OpLoc,
                                     TypeSourceInfo *TSI) {
  QualType T = TSI->getType();

  // If the type is dependent, preserve the expression until instantiation.
  if (T->isDependentType())
    return new (Context) ReflectionExpr(OpLoc, TSI, Context.DependentTy);

  return BuildTypeReflection(OpLoc, T);
}

/// \brief Build a reflection for the type-id stored in \p D.
ExprResult Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, Declarator &D) {
  return ActOnCXXReflectExpr(OpLoc, GetTypeForDeclarator(D, CurScope));
}

/// Try to construct a reflection for the declaration named by \p II.
///
/// This will reflect:
///
///   - id-expressions whose unqualified-id is an identifier
///   - type-names that are identifiers, and
///   - namespace-names
///
// TODO: Handle ambiguous and overloaded lookups.
ExprResult Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, CXXScopeSpec &SS,
                                     IdentifierInfo *II, SourceLocation IdLoc) {
  // Perform any declaration having the given name.
  LookupResult R(*this, II, OpLoc, LookupAnyName);
  LookupParsedName(R, CurScope, &SS);
  if (!R.isSingleResult())
    // FIXME: This doesn't give the best errors in case of e.g., finding
    // an overload (although we should handle that).
    return ExprError();

  Decl *D = R.getAsSingle<Decl>();
  if (!D)
    return ExprError();

  // If the declaration is a template parameter, defer until instantiation.
  //
  // FIXME: This needs to be adapted for non-type and template template
  // parameters also. Most likely, we need to allow ReflectExprs to contain
  // declarations in addition to expressions and types.
  if (TypeDecl *TD = dyn_cast<TypeDecl>(D)) {
    QualType T = Context.getTypeDeclType(TD); // The reflected type.
    QualType R = T; // The result type of the expression.

    // If this refers to a metaclass specifier, then pretend that it's
    // dependent so we don't substitute too early.
    //
    // FIXME: This is a hack. It would be better if we always returned an
    // ReflectionExpr and then packed that will all of the evaluation
    // information needed for later.
    //
    // FIXME: This even hackier since we're adjusting the qualified type to
    // avoid a more principled check for metaclassiness later on.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(TD)) {
      if (Class->isInjectedClassName()) {
        Class = dyn_cast<CXXRecordDecl>(Class->getDeclContext());
        T = Context.getRecordType(Class); // Point at the actual type.
      }
      if (dyn_cast<MetaclassDecl>(Class->getDeclContext()))
        R = Context.DependentTy;
    }

    // If the return type is dependent, don't evaluate too early.
    if (R->isDependentType()) {
      TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(T);
      return new (Context) ReflectionExpr(OpLoc, TSI, Context.DependentTy);
    }
  }

  // If we have a value declaration of dependent type, then make a dependent
  // decl-ref expression to be resolved later.
  if (ValueDecl *VD = dyn_cast<ValueDecl>(D)) {
    QualType T = VD->getType();
    if (T->isDependentType()) {
      Expr *E = new (Context)
          DeclRefExpr(VD, false, Context.DependentTy, VK_LValue, OpLoc);
      return new (Context) ReflectionExpr(OpLoc, E, Context.DependentTy);
    }
  }

  return BuildDeclReflection(OpLoc, D);
}

/// Update the reflection expression with by indicating that it is in fact
/// a reflexpr expression.
ExprResult Sema::ActOnCXXReflexprExpr(Expr *E, 
                                      SourceLocation LParenLoc, 
                                      SourceLocation RParenLoc) {
  assert(isa<ReflectionExpr>(E));
  ReflectionExpr *RE = cast<ReflectionExpr>(E);
  RE->setParenLocs(LParenLoc, RParenLoc);
  return E;
}

static bool AppendStringValue(Sema& S, llvm::raw_ostream& OS, 
                              const APValue& Val) {
  // Extracting the string valkue from the LValue.
  //
  // FIXME: We probably want something like EvaluateAsString in the Expr class.
  APValue::LValueBase Base = Val.getLValueBase();
  if (Base.is<const Expr *>()) {
    const Expr *BaseExpr = Base.get<const Expr *>();
    assert(isa<StringLiteral>(BaseExpr) && "Not a string literal");
    const StringLiteral *Str = cast<StringLiteral>(BaseExpr);
    OS << Str->getString();
  } else {
    llvm_unreachable("Use of string variable not implemented");
    // const ValueDecl *D = Base.get<const ValueDecl *>();
    // return Error(E->getMessage());
  }
  return true;
}


static bool AppendCharacterArray(Sema& S, llvm::raw_ostream &OS, Expr *E, 
                                 QualType T) {
  assert(T->isArrayType() && "Not an array type");
  const ArrayType *ArrayTy = cast<ArrayType>(T.getTypePtr());

  // Check that the type is 'const char[N]' or 'char[N]'.
  QualType ElemTy = ArrayTy->getElementType();
  if (!ElemTy->isCharType()) {
    S.Diag(E->getLocStart(), diag::err_idexpr_invalid_operand_type) << T;
    return false;
  }

  // Evaluate the expression.
  Expr::EvalResult Result;
  if (!E->EvaluateAsLValue(Result, S.Context)) {
    // FIXME: Include notes in the diagnostics.
    S.Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
    return false;
  }

  return AppendStringValue(S, OS, Result.Val);
}

static bool AppendCharacterPointer(Sema& S, llvm::raw_ostream &OS, Expr *E, 
                                   QualType T) {
  assert(T->isPointerType() && "Not a pointer type");
  const PointerType* PtrTy = cast<PointerType>(T.getTypePtr());

  // Check for 'const char*'.
  QualType ElemTy = PtrTy->getPointeeType();
  if (!ElemTy->isCharType() || !ElemTy.isConstQualified()) {
    S.Diag(E->getLocStart(), diag::err_idexpr_invalid_operand_type) << T;
    return false;
  }

  // Try evaluating the expression as an rvalue and then extract the result.
  Expr::EvalResult Result;
  if (!E->EvaluateAsRValue(Result, S.Context)) {
    // FIXME: This is not the right error.
    S.Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
    return false;
  }

  return AppendStringValue(S, OS, Result.Val);
}

static bool AppendInteger(Sema& S, llvm::raw_ostream &OS, Expr *E, QualType T) {
  llvm::APSInt N;
  if (!E->EvaluateAsInt(N, S.Context)) {
    S.Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
    return false;
  }
  OS << N;
  return true;
}

static bool
AppendReflection(Sema& S, llvm::raw_ostream &OS, Expr *E, QualType T) {
  ReflectedConstruct RC = S.EvaluateReflection(E);
  if (Decl *D = RC.getAsDeclaration()) {
    // If this is a named declaration, append its identifier.
    if (!isa<NamedDecl>(D)) {
      // FIXME: Improve diagnostics.
      S.Diag(E->getLocStart(), diag::err_reflection_not_named);
      return false;
    }
    NamedDecl *ND = cast<NamedDecl>(D);

    // FIXME: What if D has a special name? For example operator==?
    // What would we append in that case?
    DeclarationName Name = ND->getDeclName();
    if (!Name.isIdentifier()) {
      S.Diag(E->getLocStart(), diag::err_idexpr_not_an_identifer) << Name;
      return false;
    }
    
    OS << ND->getName();
  } else if (Type *T = RC.getAsType()) {
    // If this is a class type, append its identifier.
    if (auto *RC = T->getAsCXXRecordDecl())
      OS << RC->getName();
    else {
      S.Diag(E->getLocStart(), diag::err_idexpr_not_an_identifer) 
        << QualType(T, 0);
      return false;
    }
  } else {
    // This isn't supported yet.
    llvm_unreachable("Expression reflection");
  }
  return true;
}

static bool HasDependentParts(SmallVectorImpl<Expr *>& Parts) {
 return std::any_of(Parts.begin(), Parts.end(), [](const Expr *E) {
    return E->isTypeDependent();
  }); 
}

/// Constructs a new identifier from the expressions in Parts. Returns nullptr
/// on error.
DeclarationNameInfo Sema::BuildIdExprName(SourceLocation OpLoc, 
                                          SmallVectorImpl<Expr *>& Parts,
                                          SourceLocation EndLoc) {

  // If any components are dependent, we can't compute the name.
  if (HasDependentParts(Parts)) {
    DeclarationName Name
      = Context.DeclarationNames.getCXXIdExprName(Parts.size(), &Parts[0]);
    DeclarationNameInfo NameInfo(Name, OpLoc);
    NameInfo.setCXXIdExprNameRange({OpLoc, EndLoc});
    return NameInfo;
  }

  SmallString<256> Buf;
  llvm::raw_svector_ostream OS(Buf);
  for (std::size_t I = 0; I < Parts.size(); ++I) {
    Expr *E = Parts[I];

    assert(!E->isTypeDependent() && !E->isValueDependent() 
        && "Dependent name component");

    // Get the type of the reflection.
    QualType T = E->getType();
    if (AutoType *D = T->getContainedAutoType()) {
      T = D->getDeducedType();
      if (!T.getTypePtr())
        llvm_unreachable("Undeduced value reflection");
    }
    T = Context.getCanonicalType(T);

    SourceLocation ExprLoc = E->getLocStart();

    // Evaluate the sub-expression (depending on type) in order to compute
    // a string part that will constitute a declaration name.
    if (T->isConstantArrayType()) {
      if (!AppendCharacterArray(*this, OS, E, T))
        return DeclarationNameInfo();
    }
    else if (T->isPointerType()) {
      if (!AppendCharacterPointer(*this, OS, E, T))
        return DeclarationNameInfo();
    }
    else if (T->isIntegerType()) {
      if (I == 0) {
        // An identifier cannot start with an integer value.
        Diag(ExprLoc, diag::err_idexpr_with_integer_prefix);
        return DeclarationNameInfo();
      }
      if (!AppendInteger(*this, OS, E, T))
        return DeclarationNameInfo();
    }
    else if (T->isRecordType()) {
      if (!AppendReflection(*this, OS, E, T))
        return DeclarationNameInfo();
    }
    else {
      Diag(ExprLoc, diag::err_idexpr_invalid_operand_type) << T;
      return DeclarationNameInfo();
    }
  }

  // FIXME: Should we always return a declaration name?
  IdentifierInfo *Id = &PP.getIdentifierTable().get(Buf);
  DeclarationName Name = Context.DeclarationNames.getIdentifier(Id);
  return DeclarationNameInfo(Name, OpLoc);
}

/// Constructs a new identifier from the expressions in Parts. Returns false
/// if no errors were encountered.
bool Sema::BuildDeclnameId(SmallVectorImpl<Expr *>& Parts, 
                           UnqualifiedId& Result,
                           SourceLocation KWLoc,
                           SourceLocation LParenLoc, 
                           SourceLocation RParenLoc) {
  DeclarationNameInfo NameInfo = BuildIdExprName(KWLoc, Parts, RParenLoc);
  DeclarationName Name = NameInfo.getName();
  if (!Name)
    return true;
  if (Name.getNameKind() == DeclarationName::CXXIdExprName)
    Result.setIdExprOperator(KWLoc, Name.getCXXIdExprArguments(), RParenLoc);
  else
    Result.setIdentifier(Name.getAsIdentifierInfo(), KWLoc);
  return false;
}

ExprResult Sema::ActOnHasNameExpr(SourceLocation KWLoc, Expr *E, 
                                  UnqualifiedId & I, SourceLocation RParenLoc) {
  ReflectedConstruct RC = EvaluateReflection(E);
  if (!RC)
    return ExprError();
  
  DeclarationName N1;
  if (Decl *D = RC.getAsDeclaration()) {
    // Get the declration name.
    if (!isa<NamedDecl>(D)) {
      Diag(E->getLocStart(), diag::err_reflection_not_named);
      return ExprError();
    }
    NamedDecl *ND = cast<NamedDecl>(D);
    N1 = ND->getDeclName();
  } else if (Type *T = RC.getAsType()) {
    // Only get the declaration name for classes.
    //
    // FIXME: Why only classes?
    if (!T->isRecordType()) {
      Diag(E->getLocStart(), diag::err_idexpr_not_an_identifer) 
        << QualType(T, 0);
      return ExprError();
    }
    CXXRecordDecl *C = T->getAsCXXRecordDecl();
    N1 = C->getDeclName();
  }

  // DeclarationName N2 = GetNameFromUnqualifiedId(I).getName();
  // if (N1 == N2)
  //   llvm::outs() << "TRUE\n";
  // else
  //   llvm::outs() << "FALSE\n";
  llvm_unreachable("Not implemented");

  // Build a declaration name form I.
  return ExprError();
}


/// Returns the name of the class we're going to instantiate.
///
// TODO: Add templates and... other stuff?
// TODO: Do we want a more precise set of types for these things?
static char const *GetReflectionClass(Decl *D) {
  switch (D->getKind()) {
  case Decl::CXXConstructor:
  case Decl::CXXConversion:
  case Decl::CXXDestructor:
  case Decl::CXXMethod:
    // All non-static member functions are simply methods. But static
    // member functions are functions.
    return cast<CXXMethodDecl>(D)->isStatic() ? "function" : "method";
  case Decl::EnumConstant:
    return "enumerator";
  case Decl::Field:
    return "field";
  case Decl::Function:
    return "function";
  case Decl::Namespace:
    return "ns";
  case Decl::ParmVar:
    return "parameter";
  case Decl::TranslationUnit:
    return "tu";
  case Decl::Var:
    return "variable";
  case Decl::AccessSpec:
    return "access_spec";
  case Decl::Constexpr:
    // Return a placeholder for a declaration. These shouldn't be exposed in
    // the AST, but it's difficult to suppress (we'd have to filter the tuple
    // accessors). For now, push this responsibility onto the library.
    return "internal";
  default:
    break;
  }
  D->dump();
  llvm_unreachable("Unhandled declaration in reflection");
}

/// \brief Return an expression whose type reflects the given node.
ExprResult Sema::BuildDeclReflection(SourceLocation Loc, Decl *D) {
  assert(!isa<MetaclassDecl>(D) && "Reflection of a metaclass");

  // References to a metaclass should refer to the underlying class.
  // FIXME: Handle this above.
  if (auto *MD = dyn_cast<MetaclassDecl>(D))
    D = MD->getDefinition();

  // Use BuildTypeReflection for type declarations.
  if (TagDecl *TD = dyn_cast<TagDecl>(D))
    return BuildTypeReflection(Loc, Context.getTagDeclType(TD));
  if (TypedefNameDecl *TD = dyn_cast<TypedefNameDecl>(D))
    return BuildTypeReflection(Loc, TD->getUnderlyingType());

  // Get the template name for the instantiation.
  char const *Name = GetReflectionClass(D);
  ClassTemplateDecl *Temp = RequireReflectionType(Loc, Name);
  if (!Temp)
    return ExprError();
  TemplateName TempName(Temp);

  // Get the reflected value for D.
  ReflectionValue RV = ReflectionValue::create<RK_Decl>(D);

  // Build a template specialization, instantiate it, and then complete it.
  QualType IntPtrTy = Context.getIntPtrType();
  llvm::APSInt Val = Context.MakeIntValue(RV.getOpaqueValue(), IntPtrTy);
  Expr *Literal = new (Context) IntegerLiteral(Context, Val, IntPtrTy, Loc);
  TemplateArgument Arg(Literal);
  TemplateArgumentLocInfo ArgLocInfo(Literal);
  TemplateArgumentLoc ArgLoc(Arg, ArgLocInfo);
  TemplateArgumentListInfo TempArgs(Loc, Loc);
  TempArgs.addArgument(ArgLoc);
  QualType TempType = CheckTemplateIdType(TempName, Loc, TempArgs);

  if (RequireCompleteType(Loc, TempType, diag::err_incomplete_type))
    return ExprError();

  // Produce a value-initialized temporary of the required type.
  //
  // FIXME: We should actually return a reflection expression and attach
  // the initializer for use in evaluation.
  SmallVector<Expr *, 1> Args;
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(TempType);
  InitializationKind Kind = InitializationKind::CreateValue(Loc, Loc, Loc);
  InitializationSequence InitSeq(*this, Entity, Kind, Args);
  return InitSeq.Perform(*this, Entity, Kind, Args);
}

/// Returns the reflection class name for the type \p T.
///
// TODO: Actually populate this table.
static char const *GetReflectionClass(QualType T) {
  T = T.getCanonicalType();
  switch (T->getTypeClass()) {
  case Type::Pointer:
    return "pointer_type";
  case Type::LValueReference:
  case Type::RValueReference:
    // FIXME: Differentiate lvalue/rvlaue.
    return "reference_type";
  case Type::MemberPointer:
    return "member_pointer";
  case Type::ConstantArray:
  case Type::IncompleteArray:
    return "array_type";
  case Type::FunctionProto:
  case Type::FunctionNoProto:
    return "function_type";
  case Type::Record:
    if (T->isUnionType())
      return "union_type";
    return "class_type";
  case Type::Enum:
    return "enum_type";
  default:
    // FIXME: This probably isn't what we want. We should have a class 
    // for each type.
    return "fundamental_type"; 
  }
}

/// \brief Return an expression whose type reflects the given node.
///
// TODO: Accommodate cv-qualifiers somehow. Perhaps add them as template
// parameters a la:
//
//    template<reflection_t X, bool C, bool V>
//    struct type { ... };
//
// Note that we would need a few alternative traits to combine cv information
// in order to accurately get the type name. I also suspect that we'll need
// noexcept information for function types, and possibly more state flags
// for other types beyond this. Same idea. X is always the value type.
// Additional flags can be added as extensions.
//
// TODO: There's a lot of duplication between this and the BuildDeclReflection
// function above. Surely we can simplify.
ExprResult Sema::BuildTypeReflection(SourceLocation Loc, QualType QT) {
  // Only operate on the canonical type. See through sugar and aliases.
  QT = Context.getCanonicalType(QT);

  // Get the wrapper type.
  char const *Name = GetReflectionClass(QT);
  ClassTemplateDecl *Temp = RequireReflectionType(Loc, Name);
  if (!Temp)
    return ExprError();
  TemplateName TempName(Temp);

  Type *T = const_cast<Type *>(QT.getTypePtr());
  ReflectionValue RV = ReflectionValue::create<RK_Type>(T);

  // Build a template specialization, instantiate it, and then complete it.
  QualType IntPtrTy = Context.getIntPtrType();
  llvm::APSInt Val = Context.MakeIntValue(RV.getOpaqueValue(), IntPtrTy);
  Expr *Literal = new (Context) IntegerLiteral(Context, Val, IntPtrTy, Loc);
  TemplateArgument Arg(Literal);
  TemplateArgumentLocInfo ArgLocInfo(Literal);
  TemplateArgumentLoc ArgLoc(Arg, ArgLocInfo);
  TemplateArgumentListInfo TempArgs(Loc, Loc);
  TempArgs.addArgument(ArgLoc);
  QualType TempType = CheckTemplateIdType(TempName, Loc, TempArgs);

  if (RequireCompleteType(Loc, TempType, diag::err_incomplete_type))
    return ExprError();

  // Produce a value-initialized temporary of the required type.
  SmallVector<Expr *, 1> Args;
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(TempType);
  InitializationKind Kind = InitializationKind::CreateValue(Loc, Loc, Loc);
  InitializationSequence InitSeq(*this, Entity, Kind, Args);
  return InitSeq.Perform(*this, Entity, Kind, Args);
}

/// \brief Returns the cppx namespace if a suitable header has been included.
/// If not, a diagnostic is emitted, and \c nullptr is returned.
///
// TODO: We should probably cache this the same way that we do
// with typeid (see CXXTypeInfoDecl in Sema.h).
NamespaceDecl *Sema::RequireCppxNamespace(SourceLocation Loc) {
  IdentifierInfo *CppxII = &PP.getIdentifierTable().get("cppx");
  LookupResult R(*this, CppxII, Loc, LookupNamespaceName);
  LookupQualifiedName(R, Context.getTranslationUnitDecl());
  if (!R.isSingleResult()) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  NamespaceDecl *Cppx = R.getAsSingle<NamespaceDecl>();
  assert(Cppx && "cppx is not a namespace");
  return Cppx;
}

/// \brief Same as RequireCppxNamespace, but requires cppx::meta.
NamespaceDecl *Sema::RequireCppxMetaNamespace(SourceLocation Loc) {
  NamespaceDecl *Cppx = RequireCppxNamespace(Loc);
  if (!Cppx)
    return nullptr;

  // Get the cppx::meta namespace.
  IdentifierInfo *MetaII = &PP.getIdentifierTable().get("meta");
  LookupResult R(*this, MetaII, Loc, LookupNamespaceName);
  LookupQualifiedName(R, Cppx);
  if (!R.isSingleResult()) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  NamespaceDecl *Meta = R.getAsSingle<NamespaceDecl>();
  assert(Meta && "cppx::meta is not a namespace");
  return Meta;
}

/// \brief Returns the class with the given name in the
/// std::[experimental::]meta namespace.
/// 
/// If no such class can be found, a diagnostic is emitted, and \c nullptr
/// returned.
///
// TODO: Cache these types so we don't keep doing lookup. In on the first
// lookup, cache the names of ALL meta types so that we can easily check
// for appropriate arguments in the reflection traits.
ClassTemplateDecl *Sema::RequireReflectionType(SourceLocation Loc,
                                               char const *Name) {
  NamespaceDecl *Meta = RequireCppxMetaNamespace(Loc);
  if (!Meta)
    return nullptr;

  // Get the corresponding reflection class.
  IdentifierInfo *TypeII = &PP.getIdentifierTable().get(Name);
  LookupResult R(*this, TypeII, SourceLocation(), LookupAnyName);
  LookupQualifiedName(R, Meta);
  ClassTemplateDecl *Decl = R.getAsSingle<ClassTemplateDecl>();
  if (!Decl) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  return Decl;
}

/// Information supporting reflection operations.
///
// TODO: Move all of the functions below into this class since it provides
// the context for their evaluation.
struct Reflector {
  Sema &S;
  SourceLocation KWLoc;
  SourceLocation RParenLoc;
  ArrayRef<Expr *> Args;
  ArrayRef<llvm::APSInt> Vals;

  ExprResult Reflect(ReflectionTrait RT, Decl *D);
  ExprResult Reflect(ReflectionTrait RT, Type *T);
  ExprResult Reflect(ReflectionTrait RT, CXXBaseSpecifier *B);

  // General entity properties.
  ExprResult ReflectName(Decl *D);
  ExprResult ReflectName(Type *D);
  ExprResult ReflectQualifiedName(Decl *D);
  ExprResult ReflectQualifiedName(Type *D);
  ExprResult ReflectDeclarationContext(Decl *D);
  ExprResult ReflectDeclarationContext(Type *T);
  ExprResult ReflectLexicalContext(Decl *D);
  ExprResult ReflectLexicalContext(Type *T);

  ExprResult ReflectTraits(Decl *D);
  ExprResult ReflectTraits(Type *T);

  ExprResult ReflectPointer(Decl *D);
  
  // FIXME: Extend this to work for types. For example, the value (type) of 
  // an T[N] is T. The value type of cv-T is T.
  ExprResult ReflectValue(Decl *D);
  
  ExprResult ReflectType(Decl *D);

  ExprResult ReflectReturn(Decl* D);
  ExprResult ReflectReturn(Type* T);

  // FIXME: Extend this to work for function types as well.
  ExprResult ReflectNumParameters(Decl *D);
  ExprResult ReflectParameter(Decl *D, const llvm::APSInt &N);

  template <typename I>
  ExprResult GetNumMembers(I First, I Limit);

  template <typename I>
  ExprResult GetMember(const llvm::APSInt &N, I First, I Limit);

  ExprResult ReflectNumMembers(Decl *);
  ExprResult ReflectMember(Decl *, const llvm::APSInt &N);
  ExprResult ReflectNumMembers(Type *);
  ExprResult ReflectMember(Type *, const llvm::APSInt &N);

  ExprResult ReflectNumBases(Decl *D);
  ExprResult ReflectBase(Decl *D, const llvm::APSInt &N);
};

/// Returns true if RTK is a reflection trait that would modify a property
/// of a declaration.
static inline bool IsModificationTrait(ReflectionTrait RTK) {
  return RTK >= BRT_ModifyAccess;
}

static bool CheckReflectionArgs(Sema &SemaRef, ArrayRef<Expr *> Args,
                                SmallVectorImpl<llvm::APSInt> &Vals) {
  // Ensure that each operand has integral type.
  for (unsigned i = 0; i < Args.size(); ++i) {
    Expr *E = Args[i];
    if (!E->getType()->isIntegerType()) {
      SemaRef.Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
      return false;
    }
  }

  // Evaluate all of the operands ahead of time. Note that trait arity is
  // checked at parse time.
  Vals.resize(Args.size());
  for (unsigned i = 0; i < Args.size(); ++i) {
    Expr *E = Args[i];
    // FIXME: Emit the right diagnostics.
    if (!E->EvaluateAsInt(Vals[i], SemaRef.Context)) {
      SemaRef.Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
      return false;
    }
  }
  return true;
}

ExprResult Sema::ActOnReflectionTrait(SourceLocation KWLoc,
                                      ReflectionTrait Kind,
                                      ArrayRef<Expr *> Args,
                                      SourceLocation RParenLoc) {
  // If any arguments are dependent, then the result is a dependent expression.
  for (unsigned i = 0; i < Args.size(); ++i) {
    if (Args[i]->isTypeDependent() || Args[i]->isValueDependent()) {
      QualType Ty = Context.DependentTy;
      return new (Context) ReflectionTraitExpr(Context, Kind, Ty, Args,
                                               APValue(), KWLoc, RParenLoc);
    }
  }

  // Modifications are preserved until constexpr evaluation. These expressions
  // have type void.
  //
  // Printing has an effect and must be evaluated, not instantiated.
  if (IsModificationTrait(Kind) || Kind == URT_ReflectPrint)
    return new (Context) ReflectionTraitExpr(Context, Kind, Context.VoidTy,
                                             Args, APValue(), KWLoc, RParenLoc);

  // Get the integer values from the trait arguments.
  SmallVector<llvm::APSInt, 2> Vals;
  if (!CheckReflectionArgs(*this, Args, Vals))
    return ExprError();

  Reflector R = {*this, KWLoc, RParenLoc, Args, Vals};
  ReflectedConstruct C = EvaluateReflection(Args[0]);
  if (Decl *D = C.getAsDeclaration())
    return R.Reflect(Kind, D);
  if (Type *T = C.getAsType())
    return R.Reflect(Kind, T);
  if (CXXBaseSpecifier *B = C.getAsBaseSpecifier())
    return R.Reflect(Kind, B);

  llvm_unreachable("Unhandled reflection kind");
}

/// Returns a string literal that has the given name.
static ExprResult MakeString(ASTContext &C, const std::string &Str) {
  llvm::APSInt Size = C.MakeIntValue(Str.size() + 1, C.getSizeType());
  QualType Elem = C.getConstType(C.CharTy);
  QualType Type = C.getConstantArrayType(Elem, Size, ArrayType::Normal, 0);
  return StringLiteral::Create(C, Str, StringLiteral::Ascii, false, Type,
                               SourceLocation());
}

ExprResult Reflector::Reflect(ReflectionTrait RT, Decl *D) {
  switch (RT) {
  default:
    break;
  case URT_ReflectPrint: {
    PrintingPolicy PP = S.getASTContext().getPrintingPolicy();
    PP.TerseOutput = false;
    D->print(llvm::errs(), PP);
    llvm::errs() << '\n';
    return ExprResult();
  }
  case URT_ReflectName:
    return ReflectName(D);
  case URT_ReflectQualifiedName:
    return ReflectQualifiedName(D);
  case URT_ReflectDeclarationContext:
    return ReflectDeclarationContext(D);
  case URT_ReflectLexicalContext:
    return ReflectLexicalContext(D);
  case URT_ReflectTraits:
    return ReflectTraits(D);
  case URT_ReflectPointer:
    return ReflectPointer(D);
  case URT_ReflectValue:
    return ReflectValue(D);
  case URT_ReflectType:
    return ReflectType(D);
  case URT_ReflectReturn:
    return ReflectReturn(D);
  case URT_ReflectNumParameters:
    return ReflectNumParameters(D);
  case BRT_ReflectParameter:
    return ReflectParameter(D, Vals[1]);
  case URT_ReflectNumMembers:
    return ReflectNumMembers(D);
  case BRT_ReflectMember:
    return ReflectMember(D, Vals[1]);
  case URT_ReflectNumBases:
    return ReflectNumBases(D);
  case BRT_ReflectBase:
    return ReflectBase(D, Vals[1]);
  }

  // FIXME: Improve this error message.
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}

enum LinkageTrait : unsigned { LinkNone, LinkInternal, LinkExternal };

/// Remap linkage specifiers into a 2-bit value.
static LinkageTrait getLinkage(NamedDecl *D) {
  switch (D->getFormalLinkage()) {
  case NoLinkage:
    return LinkNone;
  case InternalLinkage:
    return LinkInternal;
  case ExternalLinkage:
    return LinkExternal;
  default:
    break;
  }
  llvm_unreachable("Invalid linkage specification");
}

enum AccessTrait : unsigned {
  AccessNone,
  AccessPublic,
  AccessPrivate,
  AccessProtected
};

/// Returns the access specifiers for \p D.
static AccessTrait getAccess(Decl *D) {
  switch (D->getAccess()) {
  case AS_public:
    return AccessPublic;
  case AS_private:
    return AccessPrivate;
  case AS_protected:
    return AccessProtected;
  case AS_none:
    return AccessNone;
  }
  llvm_unreachable("Invalid access specifier");
}

/// Returns the access specifier as written for the base class B.
static AccessTrait getAccess(CXXBaseSpecifier *B) {
  switch (B->getAccessSpecifier()) {
  case AS_public:
    return AccessPublic;
  case AS_private:
    return AccessPrivate;
  case AS_protected:
    return AccessProtected;
  case AS_none:
    return AccessNone;
  }
  llvm_unreachable("Invalid access specifier");
}

/// This gives the storage duration of declared objects, not the storage
/// specifier, which incorporates aspects of duration and linkage.
enum StorageTrait : unsigned {
  NoStorage,
  StaticStorage,
  AutomaticStorage,
  ThreadStorage,
};

/// Returns the storage duration of \p D.
static StorageTrait getStorage(VarDecl *D) {
  switch (D->getStorageDuration()) {
  case SD_Automatic:
    return AutomaticStorage;
  case SD_Thread:
    return ThreadStorage;
  case SD_Static:
    return StaticStorage;
  default:
    break;
  }
  return NoStorage;
}

// Traits for access specifiers.
//
// We keep linkage in the object for ease of library implementation. This
// is always set to LinkNone.
struct BasicTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Rest : 28;
};

static BasicTraits getBasicTraits(Decl *D) {
  BasicTraits T = BasicTraits();
  T.Linkage = LinkNone;
  T.Access = getAccess(D);
  return T;
}

/// Traits for named objects.
///
/// Note that a variable can be declared extern and not be defined.
struct VariableTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  StorageTrait Storage : 2;
  unsigned Constexpr : 1;
  unsigned Defined : 1;
  unsigned Inline : 1; ///< Valid only when defined.
  unsigned Rest : 23; 
};

static VariableTraits getVariableTraits(VarDecl *D) {
  VariableTraits T = VariableTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Storage = getStorage(D);
  T.Constexpr = D->isConstexpr();
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInline();
  return T;
}

/// Traits for named sub-objects of a class (or union?).
struct FieldTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Mutable : 1;
  unsigned Rest : 27; 
};

/// Get the traits for a non-static member of a class or union.
static FieldTraits getFieldTraits(FieldDecl *D) {
  FieldTraits T = FieldTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Mutable = D->isMutable();
  return T;
}

/// Computed traits of normal, extern local, and static class functions.
///
// TODO: Add calling conventions to function traits.
struct FunctionTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Constexpr : 1;
  unsigned Nothrow : 1; ///< Called \c noexcept in C++.
  unsigned Defined : 1;
  unsigned Inline : 1;  ///< Valid only when defined.
  unsigned Deleted : 1; ///< Valid only when defined.
  unsigned Rest : 23;
};

static bool getNothrow(ASTContext &C, FunctionDecl *D) {
  if (const FunctionProtoType *Ty = D->getType()->getAs<FunctionProtoType>())
    return Ty->isNothrow(C);
  return false;
}

static FunctionTraits getFunctionTraits(ASTContext &C, FunctionDecl *D) {
  FunctionTraits T = FunctionTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Constexpr = D->isConstexpr();
  T.Nothrow = getNothrow(C, D);
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInlined();
  T.Deleted = D->isDeleted();
  return T;
}

enum MethodKind : unsigned {
  Method,
  Constructor,
  Destructor,
  Conversion
};

/// Traits for normal member functions.
struct MethodTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  MethodKind Kind : 2;
  unsigned Constexpr : 1;
  unsigned Explicit : 1;
  unsigned Virtual : 1;
  unsigned Pure : 1;
  unsigned Final : 1;
  unsigned Override : 1;
  unsigned Nothrow : 1; ///< Called \c noexcept in C++.
  unsigned Defined : 1;
  unsigned Inline : 1;
  unsigned Deleted : 1;
  unsigned Defaulted : 1;
  unsigned Trivial : 1;
  unsigned DefaultCtor : 1;
  unsigned CopyCtor : 1;
  unsigned MoveCtor : 1;
  unsigned CopyAssign : 1;
  unsigned MoveAssign : 1;
  unsigned Rest : 9;
};

static MethodTraits getConstructorTraits(ASTContext &C, CXXConstructorDecl *D) {
  MethodTraits T = MethodTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Kind = Constructor;
  T.Constexpr = D->isConstexpr();
  T.Nothrow = getNothrow(C, D);
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInlined();
  T.Deleted = D->isDeleted();
  T.Defaulted = D->isDefaulted();
  T.Trivial = D->isTrivial();
  T.DefaultCtor = D->isDefaultConstructor();
  T.CopyCtor = D->isCopyConstructor();
  T.MoveCtor = D->isMoveConstructor();
  return T;
}

static MethodTraits getDestructorTraits(ASTContext &C, CXXDestructorDecl *D) {
  MethodTraits T = MethodTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Kind = Destructor;
  T.Virtual = D->isVirtual();
  T.Pure = D->isPure();
  T.Final = D->hasAttr<FinalAttr>();
  T.Override = D->hasAttr<OverrideAttr>();
  T.Nothrow = getNothrow(C, D);
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInlined();
  T.Deleted = D->isDeleted();
  T.Defaulted = D->isDefaulted();
  T.Trivial = D->isTrivial();
  return T;
}

static MethodTraits getConversionTraits(ASTContext &C, CXXConversionDecl *D) {
  MethodTraits T = MethodTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Kind = Conversion;
  T.Constexpr = D->isConstexpr();
  T.Explicit = D->isExplicit();
  T.Virtual = D->isVirtual();
  T.Pure = D->isPure();
  T.Final = D->hasAttr<FinalAttr>();
  T.Override = D->hasAttr<OverrideAttr>();
  T.Nothrow = getNothrow(C, D);
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInlined();
  T.Deleted = D->isDeleted();
  return T;
}

static MethodTraits getMethodTraits(ASTContext &C, CXXMethodDecl *D) {
  MethodTraits T = MethodTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Kind = Method;
  T.Constexpr = D->isConstexpr();
  T.Virtual = D->isVirtual();
  T.Pure = D->isPure();
  T.Final = D->hasAttr<FinalAttr>();
  T.Override = D->hasAttr<OverrideAttr>();
  T.Nothrow = getNothrow(C, D);
  T.Defined = D->getDefinition() != nullptr;
  T.Inline = D->isInlined();
  T.Deleted = D->isDeleted();
  T.CopyAssign = D->isCopyAssignmentOperator();
  T.MoveAssign = D->isMoveAssignmentOperator();
  return T;
}

struct ValueTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Rest : 28;
};

static ValueTraits getValueTraits(EnumConstantDecl *D) {
  ValueTraits T = ValueTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  return T;
}

struct NamespaceTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Inline : 1;
  unsigned Rest : 27;
};

static NamespaceTraits getNamespaceTraits(NamespaceDecl *D) {
  NamespaceTraits T = NamespaceTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Inline = D->isInline();
  return T;
}

// TODO: Accumulate all known type traits for classes.
struct ClassTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Complete : 1;
  unsigned Polymoprhic : 1;
  unsigned Abstract : 1;
  unsigned Final : 1;
  unsigned Empty : 1;
  unsigned Rest : 23;
};

static ClassTraits getClassTraits(CXXRecordDecl *D) {
  ClassTraits T = ClassTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Complete = D->getDefinition() != nullptr;
  if (T.Complete) {
    T.Polymoprhic = D->isPolymorphic();
    T.Abstract = D->isAbstract();
    T.Final = D->hasAttr<FinalAttr>();
    T.Empty = D->isEmpty();
  }
  return T;
}

struct EnumTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Scoped : 1;
  unsigned Complete : 1;
  unsigned Rest : 26;
};

static EnumTraits getEnumTraits(EnumDecl *D) {
  EnumTraits T = EnumTraits();
  T.Linkage = getLinkage(D);
  T.Access = getAccess(D);
  T.Scoped = D->isScoped();
  T.Complete = D->isComplete();
  return T;
}

struct BaseTraits {
  LinkageTrait Linkage : 2;
  AccessTrait Access : 2;
  unsigned Virtual : 1;
  unsigned Rest : 27;
};

static BaseTraits getBaseTraits(CXXBaseSpecifier *B) {
  BaseTraits T = BaseTraits();
  T.Access = getAccess(B);
  T.Virtual = B->isVirtual();
  return T;
}

/// Convert a bit-field structure into a uint32.
template <typename Traits>
static inline std::uint32_t LaunderTraits(Traits S) {
  static_assert(sizeof(std::uint32_t) == sizeof(Traits), 
                "size mismatch");
  unsigned ret = 0;
  std::memcpy(&ret, &S, sizeof(S));
  return ret;
}

ExprResult Reflector::Reflect(ReflectionTrait RT, Type *T) {
  switch (RT) {
  default:
    break;
  case URT_ReflectPrint: {
    PrintingPolicy PP = S.getASTContext().getPrintingPolicy();
    PP.TerseOutput = false;
    if (CXXRecordDecl *Class = T->getAsCXXRecordDecl()) {
      Class->print(llvm::errs(), PP);
    } else {
      QualType Q(T, 0);
      Q.print(llvm::errs(), PP);
    }
    llvm::errs() << '\n';
    return ExprResult();
  }

  case URT_ReflectName:
    return ReflectName(T);
  case URT_ReflectQualifiedName:
    return ReflectQualifiedName(T);
  case URT_ReflectDeclarationContext:
    return ReflectDeclarationContext(T);
  case URT_ReflectLexicalContext:
    return ReflectLexicalContext(T);
  case URT_ReflectTraits:
    return ReflectTraits(T);
  case URT_ReflectReturn:
    return ReflectReturn(T);
  case URT_ReflectNumMembers:
    return ReflectNumMembers(T->getAsTagDecl());
  case BRT_ReflectMember:
    return ReflectMember(T->getAsTagDecl(), Vals[1]);
  case URT_ReflectNumBases:
    return ReflectNumBases(T->getAsTagDecl());
  case BRT_ReflectBase:
    return ReflectBase(T->getAsTagDecl(), Vals[1]);
  }

  // FIXME: Improve this error message.
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}

ExprResult Reflector::Reflect(ReflectionTrait RT, CXXBaseSpecifier *B) {
  switch (RT) {
  default:
    break;
  case URT_ReflectTraits: {
    std::uint32_t Traits = LaunderTraits(getBaseTraits(B));
    llvm::APSInt N = S.Context.MakeIntValue(Traits, S.Context.UnsignedIntTy);
    return IntegerLiteral::Create(S.Context, N, S.Context.UnsignedIntTy, KWLoc);
  }
  case URT_ReflectType:
    return S.BuildTypeReflection(KWLoc, B->getType());
  }
  return ExprError();
}

/// Returns a named declaration or emits an error and returns \c nullptr.
static NamedDecl *RequireNamedDecl(Reflector &R, Decl *D) {
  Sema &S = R.S;
  if (!isa<NamedDecl>(D)) {
    S.Diag(R.Args[0]->getLocStart(), diag::err_reflection_not_named);
    return nullptr;
  }
  return cast<NamedDecl>(D);
}

ExprResult Reflector::ReflectName(Decl *D) {
  if (NamedDecl *ND = RequireNamedDecl(*this, D))
    return MakeString(S.Context, ND->getNameAsString());
  return ExprError();
}

ExprResult Reflector::ReflectName(Type *T) {
  // Use the underlying declaration of tag types for the name. This way,
  // we won't generate "struct or enum" as part of the type.
  if (TagDecl *TD = T->getAsTagDecl())
    return MakeString(S.Context, TD->getNameAsString());
  QualType QT(T, 0);
  return MakeString(S.Context, QT.getAsString());
}

ExprResult Reflector::ReflectQualifiedName(Decl *D) {
  if (NamedDecl *ND = RequireNamedDecl(*this, D))
    return MakeString(S.Context, ND->getQualifiedNameAsString());
  return ExprError();
}

ExprResult Reflector::ReflectQualifiedName(Type *T) {
  if (TagDecl *TD = T->getAsTagDecl())
    return MakeString(S.Context, TD->getQualifiedNameAsString());
  QualType QT(T, 0);
  return MakeString(S.Context, QT.getAsString());
}

// TODO: Currently, this fails to return a declaration context for the
// translation unit and for builtin types (because they aren't declared).
// Perhaps we should return an empty context?

/// Reflects the declaration context of \p D.
ExprResult Reflector::ReflectDeclarationContext(Decl *D) {
  if (isa<TranslationUnitDecl>(D)) {
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  }
  return S.BuildDeclReflection(KWLoc, cast<Decl>(D->getDeclContext()));
}

/// Reflects the declaration context of a user-defined type \p T.
///
// TODO: Emit a better error for non-declared types.
ExprResult Reflector::ReflectDeclarationContext(Type *T) {
  if (TagDecl *TD = T->getAsTagDecl()) {
    Decl *D = cast<Decl>(TD->getDeclContext());
    return S.BuildDeclReflection(KWLoc, D);
  }
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}

/// Reflects the lexical declaration context of \p D.
ExprResult Reflector::ReflectLexicalContext(Decl *D) {
  if (isa<TranslationUnitDecl>(D)) {
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  }
  return S.BuildDeclReflection(KWLoc, cast<Decl>(D->getLexicalDeclContext()));
}

/// Reflects the lexical declaration context of a user-defined type \p T.
///
// TODO: Emit a better error for non-declared types.
ExprResult Reflector::ReflectLexicalContext(Type *T) {
  if (TagDecl *TD = T->getAsTagDecl()) {
    Decl *D = cast<Decl>(TD->getLexicalDeclContext());
    return S.BuildDeclReflection(KWLoc, D);
  }
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}

/// Reflects the specifiers of the declaration \p D.
ExprResult Reflector::ReflectTraits(Decl *D) {
  ASTContext &C = S.Context;

  // FIXME: Use a switch.
  std::uint32_t Traits;
  if (VarDecl *Var = dyn_cast<VarDecl>(D))
    Traits = LaunderTraits(getVariableTraits(Var));
  else if (FieldDecl *Field = dyn_cast<FieldDecl>(D))
    Traits = LaunderTraits(getFieldTraits(Field));
  else if (CXXConstructorDecl *Ctor = dyn_cast<CXXConstructorDecl>(D))
    Traits = LaunderTraits(getConstructorTraits(C, Ctor));
  else if (CXXDestructorDecl *Dtor = dyn_cast<CXXDestructorDecl>(D))
    Traits = LaunderTraits(getDestructorTraits(C, Dtor));
  else if (CXXConversionDecl *Conv = dyn_cast<CXXConversionDecl>(D))
    Traits = LaunderTraits(getConversionTraits(C, Conv));
  else if (CXXMethodDecl *Meth = dyn_cast<CXXMethodDecl>(D))
    Traits = LaunderTraits(getMethodTraits(C, Meth));
  else if (FunctionDecl *Fn = dyn_cast<FunctionDecl>(D))
    Traits = LaunderTraits(getFunctionTraits(C, Fn));
  else if (EnumConstantDecl *Enum = dyn_cast<EnumConstantDecl>(D))
    Traits = LaunderTraits(getValueTraits(Enum));
  else if (NamespaceDecl *Ns = dyn_cast<NamespaceDecl>(D))
    Traits = LaunderTraits(getNamespaceTraits(Ns));
  else if (AccessSpecDecl *Access = dyn_cast<AccessSpecDecl>(D)) {
    Traits = LaunderTraits(getBasicTraits(Access));
  }
  else
    llvm_unreachable("Requested traits for unsupported declaration");

  // FIXME: This needs to be at least 32 bits, 0 extended if greater.
  llvm::APSInt N = C.MakeIntValue(Traits, C.UnsignedIntTy);
  return IntegerLiteral::Create(C, N, C.UnsignedIntTy, KWLoc);
}

ExprResult Reflector::ReflectTraits(Type *T) {
  ASTContext &C = S.Context;

  // Traits are only defined for user-defined types.
  TagDecl *TD = T->getAsTagDecl();
  if (!TD) {
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  }

  std::uint32_t Traits;
  if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(TD))
    Traits = LaunderTraits(getClassTraits(Class));
  else if (EnumDecl *Enum = dyn_cast<EnumDecl>(TD))
    Traits = LaunderTraits(getEnumTraits(Enum));
  else
    llvm_unreachable("Unsupported type");

  // FIXME: This needs to be at least 32 bits, 0 extended if greater.
  llvm::APSInt N = C.MakeIntValue(Traits, C.UnsignedIntTy);
  return IntegerLiteral::Create(C, N, C.UnsignedIntTy, KWLoc);
}

/// Reflects a pointer.
///
/// This only applies to global variables, member variables, and functions.
///
// TODO: We can actually reflect pointers to local variables by storing
// them within the reflected object. For example:
//
//    void f() {
//      int x = 0;
//      auto p = $x; // Constructs a temp with a pointer to x.
//      (void)*p.pointer(); // Evaluates to 0.
//    }
//
// This would require that local declarations reflect differently than
// global declarations.
ExprResult Reflector::ReflectPointer(Decl *D) {
  // We can only take the address of stored declarations.
  if (!isa<VarDecl>(D) && !isa<FieldDecl>(D) && !isa<FunctionDecl>(D)) {
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  }
  ValueDecl *Val = cast<ValueDecl>(D);

  // Don't produce addresses to local variables; they aren't static.
  if (VarDecl *VD = dyn_cast<VarDecl>(Val)) {
    if (VD->hasLocalStorage()) {
      S.Diag(Args[0]->getLocStart(), diag::err_reflection_of_local_reference);
      return ExprError();
    }
  }

  // Determine the type of the declaration pointed at. If it's a member of
  // a class, we need to adjust it to a member pointer type.
  //
  // TODO: This is a subset of what CreateBuiltinUnaryOp does, but for
  // some reason, the result isn't being typed correctly.
  QualType Ty = Val->getType();
  if (FieldDecl *FD = dyn_cast<FieldDecl>(Val)) {
    const Type *Cls = S.Context.getTagDeclType(FD->getParent()).getTypePtr();
    Ty = S.Context.getMemberPointerType(Ty, Cls);
  } else if (isa<CXXConstructorDecl>(Val) || isa<CXXDestructorDecl>(D)) {
    // TODO: Find a better error message to emit.
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  } else if (CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(Val)) {
    const Type *Cls = S.Context.getTagDeclType(MD->getParent()).getTypePtr();
    Ty = S.Context.getMemberPointerType(Ty, Cls);
  } else {
    Ty = S.Context.getPointerType(Ty);
  }

  DeclRefExpr *Ref =
      new (S.Context) DeclRefExpr(Val, false, Val->getType(), VK_LValue, KWLoc);
  S.MarkDeclRefReferenced(Ref);
  Expr *Op = new (S.Context)
      UnaryOperator(Ref, UO_AddrOf, Ty, VK_RValue, OK_Ordinary, KWLoc);
  return Op;
}

/// Reflects the value of an enumerator.
///
// TODO: Consider allowing this for instantiated non-type template arguments
// as well.
ExprResult Reflector::ReflectValue(Decl *D) {
  if (!isa<EnumConstantDecl>(D)) {
    S.Diag(KWLoc, diag::err_reflection_not_supported);
    return ExprError();
  }
  EnumConstantDecl *Enum = cast<EnumConstantDecl>(D);
  QualType Ty = Enum->getType();
  DeclRefExpr *Ref =
      new (S.Context) DeclRefExpr(Enum, false, Ty, VK_RValue, KWLoc);
  S.MarkDeclRefReferenced(Ref);
  return Ref;
}

/// Reflects the type of the typed declaration \p D.
ExprResult Reflector::ReflectType(Decl *D) {
  if (ValueDecl *VD = dyn_cast<ValueDecl>(D))
    return S.BuildTypeReflection(KWLoc, VD->getType());
  S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_typed);
  return ExprError();
}

/// Returns a function declaration or emits a diagnostic and returns \c nullptr.
static FunctionDecl *RequireFunctionDecl(Reflector &R, Decl *D) {
  if (!isa<FunctionDecl>(D)) {
    R.S.Diag(R.Args[0]->getLocStart(), diag::err_reflection_not_function);
    return nullptr;
  }
  return cast<FunctionDecl>(D);
}

/// Reflects the return type of the function.
ExprResult Reflector::ReflectReturn(Decl *D) {
  if (FunctionDecl *Fn = RequireFunctionDecl(*this, D))
    return S.BuildTypeReflection(KWLoc, Fn->getReturnType());
  return ExprError();
}

ExprResult Reflector::ReflectReturn(Type *T) {
  if (FunctionType *Fn = dyn_cast<FunctionType>(T))
    return S.BuildTypeReflection(KWLoc, Fn->getReturnType());
  return ExprError();
}

/// Reflects the number of parameters of a function declaration.
ExprResult Reflector::ReflectNumParameters(Decl *D) {
  if (FunctionDecl *Fn = RequireFunctionDecl(*this, D)) {
    ASTContext &C = S.Context;
    QualType T = C.UnsignedIntTy;
    llvm::APSInt N = C.MakeIntValue(Fn->getNumParams(), T);
    return IntegerLiteral::Create(C, N, T, KWLoc);
  }
  return ExprError();
}

/// Reflects a selected parameter of a function.
ExprResult Reflector::ReflectParameter(Decl *D, const llvm::APSInt &N) {
  if (FunctionDecl *Fn = RequireFunctionDecl(*this, D)) {
    unsigned Num = N.getExtValue();
    if (Num >= Fn->getNumParams()) {
      S.Diag(Args[1]->getLocStart(), diag::err_parameter_out_of_bounds);
      return ExprError();
    }
    return S.BuildDeclReflection(KWLoc, Fn->getParamDecl(Num));
  }
  return ExprError();
}

static NamespaceDecl *RequireNamespace(Reflector &R, Decl *D) {
  if (NamespaceDecl *NS = dyn_cast<NamespaceDecl>(D))
    return NS;
  R.S.Diag(R.Args[0]->getLocStart(), diag::err_reflection_not_supported);
  return nullptr;
}

/// Reflects the number of elements in the context.
template <typename I>
ExprResult Reflector::GetNumMembers(I First, I Limit) {
  ASTContext &C = S.Context;
  QualType T = C.UnsignedIntTy;
  llvm::APSInt N = C.MakeIntValue(std::distance(First, Limit), T);
  return IntegerLiteral::Create(C, N, T, KWLoc);
}

/// Reflects the selected member from the declaration.
template <typename I>
ExprResult Reflector::GetMember(const llvm::APSInt &N, I First, I Limit) {
  unsigned Ix = N.getExtValue();
  if (Ix >= std::distance(First, Limit)) {
    S.Diag(Args[1]->getLocStart(), diag::err_parameter_out_of_bounds);
    return ExprError();
  }
  std::advance(First, Ix);
  return S.BuildDeclReflection(KWLoc, *First);
}

// TODO: The semantics of this query on namespaces are questionable. Should
// we also include members in the anonymous namespace? If not, how could we
// access those? Another trait perhaps. What about imported declarations?
// We probably also need to walk the namespace backwards through previous
// declarations.
ExprResult Reflector::ReflectNumMembers(Decl *D) {
  if (D) {
    if (TagDecl *TD = dyn_cast<TagDecl>(D))
      return GetNumMembers(TD->decls_begin(), TD->decls_end());
    if (NamespaceDecl *NS = RequireNamespace(*this, D))
      return GetNumMembers(NS->decls_begin(), NS->decls_end());
  }
  S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_supported);
  return ExprError();
}

/// Reflects the selected member from the declaration.
ExprResult Reflector::ReflectMember(Decl *D, const llvm::APSInt &N) {
  if (D) {
    if (TagDecl *TD = dyn_cast<TagDecl>(D))
      return GetMember(N, TD->decls_begin(), TD->decls_end());
    if (NamespaceDecl *NS = RequireNamespace(*this, D))
      return GetMember(N, NS->decls_begin(), NS->decls_end());
  }
  S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_supported);
  return ExprError();
}

ExprResult Reflector::ReflectNumBases(Decl *D) {
  if (!isa<CXXRecordDecl>(D)) {
    S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_supported);
    return ExprError();
  }
  CXXRecordDecl *Class = cast<CXXRecordDecl>(D);  
  QualType T = S.Context.UnsignedIntTy;
  llvm::APSInt N = S.Context.MakeIntValue(Class->getNumBases(), T);
  return IntegerLiteral::Create(S.Context, N, T, KWLoc);
}

ExprResult Reflector::ReflectBase(Decl *D, const llvm::APSInt &N) {
  CXXRecordDecl *Class = cast<CXXRecordDecl>(D);  

  auto Iter = std::next(Class->bases_begin(), N.getExtValue());

  // Get the template name for the instantiation.
  ClassTemplateDecl *Temp = S.RequireReflectionType(KWLoc, "base_spec");
  if (!Temp)
    return ExprError();
  TemplateName TempName(Temp);

  // Build a template specialization, instantiate it, and then complete it.
  ReflectionValue RV = ReflectionValue::create<RK_Base>(&*Iter);
  QualType IntPtrTy = S.Context.getIntPtrType();
  llvm::APSInt Val = S.Context.MakeIntValue(RV.getOpaqueValue(), IntPtrTy);
  Expr *Literal = new (S.Context) IntegerLiteral(S.Context, Val, IntPtrTy, KWLoc);
  TemplateArgument Arg(Literal);
  TemplateArgumentLocInfo ArgLocInfo(Literal);
  TemplateArgumentLoc ArgLoc(Arg, ArgLocInfo);
  TemplateArgumentListInfo TempArgs(KWLoc, KWLoc);
  TempArgs.addArgument(ArgLoc);
  QualType TempType = S.CheckTemplateIdType(TempName, KWLoc, TempArgs);

  if (S.RequireCompleteType(KWLoc, TempType, diag::err_incomplete_type))
    return ExprError();

  // Produce a value-initialized temporary of the required type.
  SmallVector<Expr *, 1> Args;
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(TempType);
  InitializationKind Kind = InitializationKind::CreateValue(KWLoc, KWLoc, KWLoc);
  InitializationSequence InitSeq(S, Entity, Kind, Args);
  return InitSeq.Perform(S, Entity, Kind, Args);
}

/// Modify the access specifier of a given declaration.
bool Sema::ModifyDeclarationAccess(ReflectionTraitExpr *E) {
  llvm::ArrayRef<Expr *> Args(E->getArgs(), E->getNumArgs());
  SmallVector<llvm::APSInt, 2> Vals;

  CheckReflectionArgs(*this, Args, Vals);

  ReflectedConstruct C(Vals[0].getExtValue());
  Decl *D = C.getAsDeclaration();
  if (!D) {
    Diag(E->getLocStart(), diag::err_invalid_reflection) << 0;
    return false;
  }

  // FIXME: What about friend declarations?
  DeclContext *Owner = D->getDeclContext();
  if (!Owner->isRecord()) {
    Diag(E->getLocStart(), diag::err_modifies_mem_spec_of_non_member) << 0;
    return false;
  }

  switch (Vals[1].getExtValue()) {
  case AccessPublic:
    D->setAccess(AS_public);
    break;
  case AccessPrivate:
    D->setAccess(AS_private);
    break;
  case AccessProtected:
    D->setAccess(AS_protected);
    break;
  default:
    Diag(E->getLocStart(), diag::err_invalid_access_specifier);
    return false;
  }

  Owner->updateDecl(D);
  return true;
}

/// Modify the virtual specifier of a given declaration.
bool Sema::ModifyDeclarationVirtual(ReflectionTraitExpr *E) {
  llvm::ArrayRef<Expr *> Args(E->getArgs(), E->getNumArgs());
  SmallVector<llvm::APSInt, 2> Vals;

  CheckReflectionArgs(*this, Args, Vals);

  ReflectedConstruct C(Vals[0].getExtValue());
  Decl *D = C.getAsDeclaration();
  if (!D) {
    Diag(E->getLocStart(), diag::err_invalid_reflection) << 0;
    return false;
  }

  DeclContext *Owner = D->getDeclContext();
  if (!Owner->isRecord()) {
    Diag(E->getLocStart(), diag::err_modifies_mem_spec_of_non_member) << 1;
    return false;
  }

  // FIXME: It is an error if D is a member function template. The diagnostic
  // code is: err_virt_member_function_template
  CXXMethodDecl *Method = dyn_cast<CXXMethodDecl>(D);
  if (!Method) {
    Diag(E->getLocStart(), diag::err_virtual_non_function);
    return false;
  }
  if (isa<CXXConstructorDecl>(Method)) {
    Diag(E->getLocStart(), diag::err_constructor_cannot_be) << "virtual";
    return false;
  }

  // All requests make methods virtual.
  Method->setVirtualAsWritten(true);

  // But it's only pure when the 2nd operand is non-zero.
  if (Vals[1].getExtValue()) {
    int Err = 0;
    if (Method->isDefaulted()) Err = 2;
    else if (Method->isDeleted()) Err = 3;
    else if (Method->isDefined()) Err = 1;
    if (Err) {
      Diag(E->getLocStart(), diag::err_cannot_make_pure_virtual) << (Err - 1);
      return false;
    }
    CheckPureMethod(Method, Method->getSourceRange());
  }

  Owner->updateDecl(D);
  return true;
}

/// Modify the constexpr specifier of a given declaration.
bool Sema::ModifyDeclarationConstexpr(ReflectionTraitExpr *E) {
  llvm::ArrayRef<Expr *> Args(E->getArgs(), E->getNumArgs());
  SmallVector<llvm::APSInt, 1> Vals;

  CheckReflectionArgs(*this, Args, Vals);

  ReflectedConstruct C(Vals[0].getExtValue());
  Decl *D = C.getAsDeclaration();
  if (!D) {
    Diag(E->getLocStart(), diag::err_invalid_reflection) << 0;
    return false;
  }

  if (VarDecl *Var = dyn_cast<VarDecl>(D)) {
    Var->setConstexpr(true);
    CheckVariableDeclarationType(Var);
  } else if (FunctionDecl *Fn = dyn_cast<FunctionDecl>(D)) {
    Fn->setConstexpr(true);
    CheckConstexprFunctionDecl(Fn);
  } else {
    Diag(D->getLocation(), diag::err_declration_cannot_be_made_constexpr);
    return false;
  }

  D->getDeclContext()->updateDecl(D);
  return true;
}

/// Diagnose a type reflection error and return a type error.
static QualType TypeReflectionError(Sema &SemaRef, Expr *E) {
  SemaRef.Diag(E->getLocStart(), diag::err_reflection_not_a_type)
      << E->getSourceRange();
  return QualType();
}

// Compute the type of a reflection.
//
// FIXME: A lot of this code seems to be duplicated from elsewhere.
QualType
GetNonDependentReflectedType(Sema &SemaRef, Expr *E)
{
  // Get the type of the reflection.
  QualType T = E->getType();
  if (AutoType *D = T->getContainedAutoType()) {
    T = D->getDeducedType();
    if (!T.getTypePtr())
      llvm_unreachable("Undeduced type reflection");
  }

  // Unpack information from the expression.
  CXXRecordDecl *Class = T->getAsCXXRecordDecl();
  if (!Class)
    return TypeReflectionError(SemaRef, E);
  if (!isa<ClassTemplateSpecializationDecl>(Class)) {
    // This could be a fragment; search the base list for the type.
    if (Class->getNumBases() == 0)
      return TypeReflectionError(SemaRef, E);
    Class = (*Class->bases_begin()).getType()->getAsCXXRecordDecl();
  }
  if (!Class)
    return TypeReflectionError(SemaRef, E);

  ClassTemplateSpecializationDecl *Spec =
      cast<ClassTemplateSpecializationDecl>(Class);
  
  // FIXME: We should verify that this Class actually a meta class object so 
  // that we aren't arbitrarily converting integers into addresses.
  
  const TemplateArgumentList &Args = Spec->getTemplateArgs();
  if (Args.size() == 0)
    return TypeReflectionError(SemaRef, E);
  const TemplateArgument &Arg = Args.get(0);
  if (Arg.getKind() != TemplateArgument::Integral)
    return TypeReflectionError(SemaRef, E);

  // Decode the specialization argument as a type.
  llvm::APSInt Data = Arg.getAsIntegral();

  ReflectedConstruct C(Data.getExtValue());

  if (Type *T = C.getAsType()) {
    // Returns the referenced type. For example:
    //
    //    typename($int) x; // int x
    QualType QT(T, 0);
    return SemaRef.Context.getReflectedType(E, QT);
  } else if (Decl *D = C.getAsDeclaration()) {
    // Returns the type of the referenced declaration. For example:
    //
    //    char x;
    //    typename($x) y; // char y
    if (!isa<ValueDecl>(D)) {
      SemaRef.Diag(E->getLocStart(), diag::err_reflection_not_a_typed_decl)
                   << E->getSourceRange();
      return QualType();
    }
    return SemaRef.Context.getReflectedType(E, cast<ValueDecl>(D)->getType());
  }
  else
    llvm_unreachable("expression type not implemented");
}

/// Evaluates the given expression and yields the computed type.
QualType Sema::BuildReflectedType(SourceLocation TypenameLoc, Expr *E) {
  QualType T;
  if (E->isTypeDependent())
    return Context.getReflectedType(E, Context.DependentTy);
  else
    return GetNonDependentReflectedType(*this, E);
}

/// Evaluates the given expression and yields the computed type.
TypeResult Sema::ActOnTypeReflectionSpecifier(SourceLocation TypenameLoc,
                                              Expr *E) {
  QualType T = BuildReflectedType(TypenameLoc, E);
  if (T.isNull())
    return TypeResult(true);

  // FIXME: Add parens?
  TypeLocBuilder TLB;
  ReflectedTypeLoc TL = TLB.push<ReflectedTypeLoc>(T);
  TL.setNameLoc(TypenameLoc);
  TypeSourceInfo *TSI = TLB.getTypeSourceInfo(Context, T);
  return CreateParsedType(T, TSI);
}

/// Buid a new metaclass definition.
Decl *Sema::ActOnMetaclass(Scope *S, SourceLocation DLoc, SourceLocation IdLoc,
                           IdentifierInfo *II) {
  assert(II);

  bool IsInvalid = false;

  // Make sure that this definition doesn't conflict with existing tag
  // definitions.
  LookupResult Previous(*this, II, IdLoc, LookupOrdinaryName, ForRedeclaration);
  LookupName(Previous, S);
  if (!Previous.empty()) {
    NamedDecl *PrevDecl = Previous.getRepresentativeDecl();
    MetaclassDecl *PrevMD = dyn_cast<MetaclassDecl>(PrevDecl);
    if (PrevMD) {
      Diag(IdLoc, diag::err_redefinition) << II;
      Diag(PrevMD->getLocation(), diag::note_previous_definition);
    } else {
      Diag(IdLoc, diag::err_redefinition_different_kind) << II;
      Diag(PrevDecl->getLocation(), diag::note_previous_definition);
    }
    IsInvalid = true;
  }

  MetaclassDecl *Metaclass =
      MetaclassDecl::Create(Context, CurContext, DLoc, IdLoc, II);

  if (IsInvalid)
    Metaclass->setInvalidDecl();

  PushOnScopeChains(Metaclass, S);
  return Metaclass;
}

void Sema::ActOnMetaclassStartDefinition(Scope *S, Decl *MD, 
                                         ParsedAttributes &Attrs,
                                         CXXRecordDecl *&Definition,
                                         unsigned Depth) {
  MetaclassDecl *Metaclass = cast<MetaclassDecl>(MD);

  PushDeclContext(S, Metaclass);
  ActOnDocumentableDecl(Metaclass);

  TagTypeKind Kind = TypeWithKeyword::getTagTypeKindForTypeSpec(TST_metaclass);

  // Create a nested class to store the metaclass member declarations.
  Definition = CXXRecordDecl::Create(
      Context, Kind, CurContext, Metaclass->getLocStart(),
      Metaclass->getLocation(), Metaclass->getIdentifier());
  Definition->setImplicit(true);
  Definition->setFragment(true);
  CurContext->addHiddenDecl(Definition);
  
  StartDefinition(Definition);
  
  assert(Definition->isMetaclassDefinition() && "Broken metaclass definition");

  // Build an implicit template parameter 'prototype'. This is essentially
  // a reserved identifier within the scope of the metaclass.
  auto *Proto = TemplateTypeParmDecl::Create(Context, Definition,
                                             SourceLocation(), SourceLocation(), 
                                             Depth, 0,
                                             &Context.Idents.get("prototype"),
                                             /*Typename=*/true,
                                             /*ParameterPack=*/false);
  Proto->setImplicit(true);
  Definition->addDecl(Proto);
  PushOnScopeChains(Proto, S, false);

  // Apply attributes to the definition.
  if (AttributeList *List = Attrs.getList())
    ProcessDeclAttributeList(CurScope, Definition, List, true);

  Metaclass->setDefinition(Definition);
}

void Sema::ActOnMetaclassFinishDefinition(Scope *S, Decl *MD,
                                          SourceRange BraceRange) {
  MetaclassDecl *Metaclass = cast<MetaclassDecl>(MD);
  Metaclass->setBraceRange(BraceRange);

  PopDeclContext();
}

void Sema::ActOnMetaclassDefinitionError(Scope *S, Decl *MD) {
  MetaclassDecl *Metaclass = cast<MetaclassDecl>(MD);
  Metaclass->setInvalidDecl();

  PopDeclContext();
}

namespace {

class MetaclassNameValidatorCCC : public CorrectionCandidateCallback {
public:
  explicit MetaclassNameValidatorCCC(bool AllowInvalid)
      : AllowInvalidDecl(AllowInvalid) {
    WantExpressionKeywords = false;
    WantCXXNamedCasts = false;
    WantRemainingKeywords = false;
  }

  bool ValidateCandidate(const TypoCorrection &candidate) override {
    if (NamedDecl *ND = candidate.getCorrectionDecl()) {
      bool IsMetaclass = isa<MetaclassDecl>(ND);
      return IsMetaclass && (AllowInvalidDecl || !ND->isInvalidDecl());
    }
    return false;
  }

private:
  bool AllowInvalidDecl;
};

} // end anonymous namespace

/// Determine whether the given identifier is the name of a C++ metaclass.
///
/// \param S                  The scope from which unqualified metaclass name
///                           lookup will begin.
/// \param SS                 If non-null, the C++ scope specifier that
///                           qualifies the name \p Name.
/// \param Name               The identifier.
/// \param NameLoc            The source location of the identifier \p Name.
/// \param [in,out] Metaclass If non-null and this function returns \c true,
///                           will contain the metaclass declaration found by
///                           lookup.
/// \returns                  \c true if a metaclass declaration with the
///                           specified name is found, \c false otherwise.
bool Sema::isMetaclassName(Scope *S, CXXScopeSpec *SS,
                           const IdentifierInfo &Name, SourceLocation NameLoc,
                           Decl **Metaclass) {
  // FIXME: What kind of lookup should be performed for metaclass names?
  LookupResult R(*this, &Name, NameLoc, LookupOrdinaryName);
  // TODO: Check for metaclass template specializations.
  LookupParsedName(R, S, SS);

  if (R.isAmbiguous()) {
    // FIXME: Diagnose an ambiguity if we find at least one declaration.
    R.suppressDiagnostics();
    return false;
  }

  MetaclassDecl *MD = R.getAsSingle<MetaclassDecl>();

  if (!MD)
    return false;
  if (Metaclass)
    *Metaclass = MD;
  return true;
}

/// \brief If the identifier refers to a metaclass name within this scope,
/// return the declaration of that type.
///
/// This routine performs ordinary name lookup of the identifier \p II
/// within the given scope, with optional C++ scope specifier \p SS, to
/// determine whether the name refers to a metaclass. If so, returns an
/// opaque pointer (actually a QualType) corresponding to that
/// type. Otherwise, returns \c NULL.
///
/// \note This function extracts the type from a MetaclassDecl's underlying
///       CXXRecordDecl representation and is used to provide a ParsedType
///       object to Parser::ParseMetaclassBaseSpecifier() when parsing metaclass
///       base specifiers. Should MetaclassDecl ever become a subclass of
///       RecordDecl or CXXRecordDecl, this function will hopefully no longer be
///       necessary.
///
/// \see  Sema::getTypeName()
ParsedType Sema::getMetaclassName(const IdentifierInfo &II,
                                  SourceLocation NameLoc, Scope *S,
                                  CXXScopeSpec *SS,
                                  bool WantNontrivialTypeSourceInfo,
                                  IdentifierInfo **CorrectedII) {
  // Determine where we will perform name lookup.
  DeclContext *LookupCtx = nullptr;
  if (SS && SS->isNotEmpty()) {
    LookupCtx = computeDeclContext(*SS, false);

    if (!LookupCtx) {
      if (isDependentScopeSpecifier(*SS)) {
        // FIXME: Update this section if metaclasses are ever allowed to be
        // members of a dependent context.

        // C++ [temp.res]p3:
        //   A qualified-id that refers to a type and in which the
        //   nested-name-specifier depends on a template-parameter (14.6.2)
        //   shall be prefixed by the keyword typename to indicate that the
        //   qualified-id denotes a type, forming an
        //   elaborated-type-specifier (7.1.5.3).
        //
        // We therefore do not perform any name lookup if the result would
        // refer to a member of an unknown specialization.

        // We know from the grammar that this name refers to a type,
        // so build a dependent node to describe the type.
        if (WantNontrivialTypeSourceInfo)
          return ActOnTypenameType(S, SourceLocation(), *SS, II, NameLoc).get();

        NestedNameSpecifierLoc QualifierLoc = SS->getWithLocInContext(Context);
        QualType T = CheckTypenameType(ETK_None, SourceLocation(), QualifierLoc,
                                       II, NameLoc);
        return ParsedType::make(T);
      }

      return nullptr;
    }

    if (!LookupCtx->isDependentContext() &&
        RequireCompleteDeclContext(*SS, LookupCtx))
      return nullptr;
  }

  LookupResult Result(*this, &II, NameLoc, LookupOrdinaryName);
  if (LookupCtx) {
    // Perform "qualified" name lookup into the declaration context we
    // computed, which is either the type of the base of a member access
    // expression or the declaration context associated with a prior
    // nested-name-specifier.
    LookupQualifiedName(Result, LookupCtx);
  } else {
    // Perform unqualified name lookup.
    LookupName(Result, S);
  }

  NamedDecl *IIDecl = nullptr;
  switch (Result.getResultKind()) {
  case LookupResult::NotFound:
  case LookupResult::NotFoundInCurrentInstantiation:
    if (CorrectedII) {
      TypoCorrection Correction =
          CorrectTypo(Result.getLookupNameInfo(), LookupOrdinaryName, S, SS,
                      llvm::make_unique<MetaclassNameValidatorCCC>(true),
                      CTK_ErrorRecovery);
      IdentifierInfo *NewII = Correction.getCorrectionAsIdentifierInfo();
      NestedNameSpecifier *NNS = Correction.getCorrectionSpecifier();
      CXXScopeSpec NewSS, *NewSSPtr = SS;
      if (SS && NNS) {
        NewSS.MakeTrivial(Context, NNS, SourceRange(NameLoc));
        NewSSPtr = &NewSS;
      }
      if (Correction && (NNS || NewII != &II)) {
        ParsedType Ty = getMetaclassName(*NewII, NameLoc, S, NewSSPtr,
                                         WantNontrivialTypeSourceInfo);
        if (Ty) {
          diagnoseTypo(Correction,
                       PDiag(diag::err_unknown_type_or_class_name_suggest)
                           << Result.getLookupName() << /*class*/ 1);
          if (SS && NNS)
            SS->MakeTrivial(Context, NNS, SourceRange(NameLoc));
          *CorrectedII = NewII;
          return Ty;
        }
      }
    }
  // If typo correction failed or was not performed, fall through
  case LookupResult::FoundOverloaded:
  case LookupResult::FoundUnresolvedValue:
    Result.suppressDiagnostics();
    return nullptr;

  case LookupResult::Ambiguous:
    // Recover from metaclass-hiding ambiguities by hiding the metaclass.  We'll
    // do the lookup again when looking for an object, and we can
    // diagnose the error then.  If we don't do this, then the error
    // about hiding the metaclass will be immediately followed by an error
    // that only makes sense if the identifier was treated like a metaclass.
    // FIXME: Should we really suppress diagnostics here?
    if (Result.getAmbiguityKind() == LookupResult::AmbiguousTagHiding) {
      Result.suppressDiagnostics();
      return nullptr;
    }

    // Look to see if we have a metaclass anywhere in the list of results.
    for (LookupResult::iterator Res = Result.begin(), ResEnd = Result.end();
         Res != ResEnd; ++Res) {
      if (isa<MetaclassDecl>(*Res)) {
        if (!IIDecl ||
            (*Res)->getLocation().getRawEncoding() <
                IIDecl->getLocation().getRawEncoding())
          IIDecl = *Res;
      }
    }

    if (!IIDecl) {
      // None of the entities we found is a metaclass, so there is no way
      // to even assume that the result is a metaclass. In this case, don't
      // complain about the ambiguity. The parser will either try to
      // perform this lookup again (e.g., as an object name), which
      // will produce the ambiguity, or will complain that it expected
      // a metaclass name.
      Result.suppressDiagnostics();
      return nullptr;
    }

    // We found a metaclass within the ambiguous lookup; diagnose the
    // ambiguity and then return that metaclass. This might be the right
    // answer, or it might not be, but it suppresses any attempt to
    // perform the name lookup again.
    break;

  case LookupResult::Found:
    IIDecl = Result.getFoundDecl();
    break;
  }

  assert(IIDecl && "Didn't find decl");

  QualType T;
  if (MetaclassDecl *MD = dyn_cast<MetaclassDecl>(IIDecl)) {
    // Get the underlying class that contains the metaclass' definition.
    TypeDecl *TD = MD->getDefinition();

    DiagnoseUseOfDecl(IIDecl, NameLoc);

    T = Context.getTypeDeclType(TD);
    // MarkAnyDeclReferenced(TD->getLocation(), TD, /*OdrUse=*/false);
  }

  if (T.isNull()) {
    // If it's not plausibly a type, suppress diagnostics.
    Result.suppressDiagnostics();
    return nullptr;
  }

  // FIXME: Is this necessary?
  if (SS && SS->isNotEmpty()) {
    if (WantNontrivialTypeSourceInfo) {
      // Construct a type with type-source information.
      TypeLocBuilder Builder;
      Builder.pushTypeSpec(T).setNameLoc(NameLoc);

      T = getElaboratedType(ETK_None, *SS, T);
      ElaboratedTypeLoc ElabTL = Builder.push<ElaboratedTypeLoc>(T);
      ElabTL.setElaboratedKeywordLoc(SourceLocation());
      ElabTL.setQualifierLoc(SS->getWithLocInContext(Context));
      return CreateParsedType(T, Builder.getTypeSourceInfo(Context, T));
    } else {
      T = getElaboratedType(ETK_None, *SS, T);
    }
  }

  return ParsedType::make(T);
}

/// Returns true if a constexpr-declaration in declaration context DC
/// would be represented using a function (vs. a lambda).
static inline bool NeedsFunctionRepresentation(const DeclContext *DC) {
  return DC->isFileContext() || DC->isRecord();
}

/// Create a constexpr-declaration that will hold the body of the
/// constexpr-declaration.
///
/// \p ScopeFlags is set to the value that should be used to create the scope
/// containing the constexpr-declaration body.
Decl *Sema::ActOnConstexprDecl(Scope *S, SourceLocation ConstexprLoc,
                               unsigned &ScopeFlags) {
  ConstexprDecl *CD;
  if (NeedsFunctionRepresentation(CurContext)) {
    ScopeFlags = Scope::FnScope | Scope::DeclScope;
    PushFunctionScope();

    // Build the function
    //
    //  constexpr void __constexpr_decl() compound-statement
    //
    // where compound-statement is the as-of-yet parsed body of the
    // constexpr-declaration.
    IdentifierInfo *II = &PP.getIdentifierTable().get("__constexpr_decl");
    DeclarationName Name(II);
    DeclarationNameInfo NameInfo(Name, ConstexprLoc);

    FunctionProtoType::ExtProtoInfo EPI(
        Context.getDefaultCallingConvention(/*IsVariadic=*/false,
                                            /*IsCXXMethod=*/false));
    QualType FunctionTy = Context.getFunctionType(Context.VoidTy, None, EPI);
    TypeSourceInfo *FunctionTyInfo =
        Context.getTrivialTypeSourceInfo(FunctionTy);
    
    // FIXME: Why is the owner the current context? We should probably adjust
    // this to the constexpr-decl later on. Maybe the owner should be the
    // nearest file context, since this is essentially a non-member function.
    FunctionDecl *Function =
        FunctionDecl::Create(Context, CurContext, ConstexprLoc, NameInfo,
                             FunctionTy, FunctionTyInfo, SC_None,
                             /*isInlineSpecified=*/false,
                             /*hasWrittenPrototype=*/true,
                             /*isConstexprSpecified=*/true);
    Function->setImplicit();
    Function->setMetaprogram();

    // Build the constexpr declaration around the function.
    CD = ConstexprDecl::Create(Context, CurContext, ConstexprLoc, Function);
  } else if (CurContext->isFunctionOrMethod()) {
    ScopeFlags = Scope::BlockScope | Scope::FnScope | Scope::DeclScope;

    LambdaScopeInfo *LSI = PushLambdaScope();

    // Build the expression
    //
    //    []() -> void compound-statement
    //
    // where compound-statement is the as-of-yet parsed body of the
    // constexpr-declaration. Note that the return type is not deduced (it
    // doesn't need to be).
    //
    // TODO: It would be great if we could only capture constexpr declarations,
    // but C++ doesn't have a constexpr default.
    const bool KnownDependent = S->getTemplateParamParent();

    FunctionProtoType::ExtProtoInfo EPI(
        Context.getDefaultCallingConvention(/*IsVariadic=*/false,
                                            /*IsCXXMethod=*/true));
    EPI.HasTrailingReturn = true;
    EPI.TypeQuals |= DeclSpec::TQ_const;
    QualType MethodTy = Context.getFunctionType(Context.VoidTy, None, EPI);
    TypeSourceInfo *MethodTyInfo = Context.getTrivialTypeSourceInfo(MethodTy);

    LambdaIntroducer Intro;
    Intro.Range = SourceRange(ConstexprLoc);
    Intro.Default = LCD_None;

    CXXRecordDecl *Closure = createLambdaClosureType(
        Intro.Range, MethodTyInfo, KnownDependent, Intro.Default);
    CXXMethodDecl *Method =
        startLambdaDefinition(Closure, Intro.Range, MethodTyInfo, ConstexprLoc,
                              None, /*IsConstexprSpecified=*/true);
    buildLambdaScope(LSI, Method, Intro.Range, Intro.Default, Intro.DefaultLoc,
                     /*ExplicitParams=*/false,
                     /*ExplicitResultType=*/true,
                     /*Mutable=*/false);
    Method->setMetaprogram();

    // NOTE: The call operator is not yet attached to the closure type. That
    // happens in ActOnFinishConstexprDecl(). The operator is, however,
    // available in the LSI.
    CD = ConstexprDecl::Create(Context, CurContext, ConstexprLoc, Closure);
  } else
    llvm_unreachable("constexpr declaration in unsupported context");

  // Add the declaration to the current context. This will be removed from the 
  // AST after evaluation.
  CurContext->addDecl(CD);
  
  return CD;
}

/// Called just prior to parsing the body of a constexpr-declaration.
///
/// This ensures that the declaration context is pushed with the appropriate
/// scope.
void Sema::ActOnStartConstexprDecl(Scope *S, Decl *D) {
  ConstexprDecl *CD = cast<ConstexprDecl>(D);

  if (CD->hasFunctionRepresentation()) {
    if (S)
      PushDeclContext(S, CD->getFunctionDecl());
    else
      CurContext = CD->getFunctionDecl();
  } else {
    LambdaScopeInfo *LSI = cast<LambdaScopeInfo>(FunctionScopes.back());
    if (S)
      PushDeclContext(S, LSI->CallOperator);
    else
      CurContext = LSI->CallOperator;
    PushExpressionEvaluationContext(
        ExpressionEvaluationContext::PotentiallyEvaluated);
  }
}

/// Called immediately after parsing the body of a constexpr-declaration.
///
/// The statements within the body are evaluated here.
void Sema::ActOnFinishConstexprDecl(Scope *S, Decl *D, Stmt *Body) {
  ConstexprDecl *CD = cast<ConstexprDecl>(D);
  if (CD->hasFunctionRepresentation()) {
    FunctionDecl *Fn = CD->getFunctionDecl();
    ActOnFinishFunctionBody(Fn, Body);
    if (!CurContext->isDependentContext())
      EvaluateConstexprDecl(CD, Fn);
  } else {
    ExprResult Lambda = ActOnLambdaExpr(CD->getLocation(), Body, S);
    if (!CurContext->isDependentContext())
      EvaluateConstexprDecl(CD, Lambda.get());
  }

  // If we didn't have a scope when building this, we need to restore the
  // current context.
  if (!S)
    CurContext = CD->getDeclContext();
}

/// Called when an error occurs while parsing the constexpr-declaration body.
void Sema::ActOnConstexprDeclError(Scope *S, Decl *D) {
  ConstexprDecl *CD = cast<ConstexprDecl>(D);
  CD->setInvalidDecl();
  if (CD->hasFunctionRepresentation())
    ActOnFinishFunctionBody(CD->getFunctionDecl(), nullptr);
  else
    ActOnLambdaError(CD->getLocation(), S);

  // Remove the declaration; we don't want to see it in the source tree.
  //
  // FIXME: Do we really want to do this?
  CD->getDeclContext()->removeDecl(CD);
}

/// Process a constexpr-declaration.
///
/// This builds an unnamed constexpr void function whose body is that of
/// the constexpr-delaration, and evaluates a call to that function.
bool Sema::EvaluateConstexprDecl(ConstexprDecl *CD, FunctionDecl *D) {
  QualType FunctionTy = D->getType();
  DeclRefExpr *Ref =
      new (Context) DeclRefExpr(D, /*RefersToEnclosingVariableOrCapture=*/false,
                                FunctionTy, VK_LValue, SourceLocation());
  QualType PtrTy = Context.getPointerType(FunctionTy);
  ImplicitCastExpr *Cast =
      ImplicitCastExpr::Create(Context, PtrTy, CK_FunctionToPointerDecay, Ref,
                               /*BasePath=*/nullptr, VK_RValue);
  CallExpr *Call =
      new (Context) CallExpr(Context, Cast, ArrayRef<Expr *>(), Context.VoidTy,
                             VK_RValue, SourceLocation());
  return EvaluateConstexprDeclCall(CD, Call);
}

/// Process a constexpr-declaration.
///
/// This builds an unnamed \c constexpr \c void function whose body is that of
/// the constexpr-delaration, and evaluates a call to that function.
bool Sema::EvaluateConstexprDecl(ConstexprDecl *CD, Expr *E) {
  LambdaExpr *Lambda = cast<LambdaExpr>(E);
  CXXMethodDecl *Method = Lambda->getCallOperator();
  QualType MethodTy = Method->getType();
  DeclRefExpr *Ref = new (Context)
      DeclRefExpr(Method, /*RefersToEnclosingVariableOrCapture=*/false,
                  MethodTy, VK_LValue, SourceLocation());
  QualType PtrTy = Context.getPointerType(MethodTy);
  ImplicitCastExpr *Cast =
      ImplicitCastExpr::Create(Context, PtrTy, CK_FunctionToPointerDecay, Ref,
                               /*BasePath=*/nullptr, VK_RValue);
  CallExpr *Call = new (Context) CXXOperatorCallExpr(Context, OO_Call,
                                                     Cast, {Lambda}, 
                                                     Context.VoidTy, 
                                                     VK_RValue, 
                                                     SourceLocation(),
                                                     FPOptions());
  return EvaluateConstexprDeclCall(CD, Call);
}

/// Evaluate the expression.
///
/// \returns  \c true if the expression \p E can be evaluated, \c false
///           otherwise.
///
// FIXME: We probably want to trap declarative effects so that we can apply
// them as declarations after execution. That would require a modification to
// EvalResult (e.g., an injection set?).
bool Sema::EvaluateConstexprDeclCall(ConstexprDecl *CD, CallExpr *Call) {
  // Associate the call expression with the declaration.
  CD->setCallExpr(Call);

  // Don't evaluate the call if this declaration appears within a metaclass.
  if (CXXRecordDecl *RD = dyn_cast_or_null<CXXRecordDecl>(CurContext)) {
    if (RD->isMetaclassDefinition())
      return true;
  }

  // assert(InjectedStmts.empty() && "Residual injected statements");

  SmallVector<PartialDiagnosticAt, 8> Notes;
  SmallVector<EvalEffect, 16> Effects;
  Expr::EvalResult Result;
  Result.Diag = &Notes;
  Result.Effects = &Effects;

  bool Folded = Call->EvaluateAsRValue(Result, Context);
  if (!Folded) {
    // If the only error is that we didn't initialize a (void) value, that's
    // actually okay. APValue doesn't know how to do this anyway.
    //
    // FIXME: We should probably have a top-level EvaluateAsVoid() function that
    // handles this case.
    if (!Notes.empty()) {
      // If we got a compiler error, then just emit that.
      if (Notes[0].second.getDiagID() == diag::err_user_defined_error)
        Diag(CD->getLocStart(), Notes[0].second);
      else if (Notes[0].second.getDiagID() != diag::note_constexpr_uninitialized) {
        // FIXME: These source locations are wrong.
        Diag(CD->getLocStart(), diag::err_expr_not_ice) << LangOpts.CPlusPlus;
        for (const PartialDiagnosticAt &Note : Notes)
          Diag(Note.first, Note.second);
      }
    }
  }

  // Apply any modifications, and if successful, remove the declaration from
  // the class; it shouldn't be visible in the output code.
  SourceLocation POI = CD->getSourceRange().getEnd();
  ApplyEffects(POI, Effects);

  // FIXME: Do we really want to remove the metaprogram after evaluation? Or
  // should we just mark it completed.
  CD->getDeclContext()->removeDecl(CD);
  
  return Notes.empty();
}

