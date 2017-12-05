//===--- ParseInject.cpp - Reflection Parsing -----------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements parsing for C++ injection statements.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/RAIIObjectsForParser.h"
#include "clang/Sema/PrettyDeclStackTrace.h"

using namespace clang;

/// Parse a fragment. Fragments can appear within fragment expressions and
/// injection statements and declarations. Returns the parsed declaration
/// fragment and captures for subsequent use.
///
///   fragment-expression:
///     named-namespace-definition
///     class-specifier
///     enum-specifier
///     compound-statement
///
/// FIXME: The parses are a bit more custom than the usual definitions.
Decl* Parser::ParseCXXFragment(SmallVectorImpl<Expr *> &Captures) {
  // Implicitly capture automatic variables as captured constants.
  Actions.ActOnCXXFragmentCapture(Captures);

  // A name declared in the the fragment is not leaked into the enclosing
  // scope. That is, fragments names are only accessible from within.
  ParseScope FragmentScope(this, Scope::DeclScope);

  // Start the fragment. The fragment is finished in one of the 
  // ParseCXX*Fragment functions.
  Decl *Fragment = Actions.ActOnStartCXXFragment(getCurScope(), 
                                                 Tok.getLocation(), 
                                                 Captures);

  switch (Tok.getKind()) {
    case tok::kw_namespace:
      return ParseNamespaceFragment(Fragment);

    case tok::kw_struct:
    case tok::kw_class:
    case tok::kw_union:
      return ParseClassFragment(Fragment);

    case tok::kw_enum:
      return ParseEnumFragment(Fragment);

    case tok::l_brace:
      llvm_unreachable("block fragments not implemented");

    default:
      break;
  }

  Diag(Tok.getLocation(), diag::err_expected_fragment);
  SkipUntil(tok::semi);
  return nullptr;
}

/// Parses a namespace fragment. Returns the completed fragment declaration.
Decl *Parser::ParseNamespaceFragment(Decl *Fragment) {
  assert(Tok.is(tok::kw_namespace) && "expected 'namespace'");

  SourceLocation NamespaceLoc = ConsumeToken();
  IdentifierInfo *Id = nullptr;
  SourceLocation IdLoc;
  if (Tok.is(tok::identifier)) {
    Id = Tok.getIdentifierInfo();
    IdLoc = ConsumeToken();
  } else {
    // FIXME: This shouldn't be an error. ActOnStartNamespaceDef will 
    // treat a missing identifier as the anonymous namespace, which this
    // is not. An injection into the anonymous namespace must be written
    // as:
    //
    //    -> namespace <id> { namespace { decls-to-inject } }
    //
    // Just generate a unique name for the namespace. Its guaranteed not 
    // conflict since we're in a nested scope.
    Diag(Tok.getLocation(), diag::err_expected) << tok::identifier;
    return nullptr;
  }

  BalancedDelimiterTracker T(*this, tok::l_brace);
  if (T.consumeOpen()) {
    Diag(Tok, diag::err_expected) << tok::l_brace;
    return nullptr;
  }

  ParseScope NamespaceScope(this, Scope::DeclScope);

  SourceLocation InlineLoc;
  ParsedAttributesWithRange Attrs(AttrFactory);
  UsingDirectiveDecl *ImplicitUsing = nullptr;
  Decl *Ns = Actions.ActOnStartNamespaceDef(getCurScope(), InlineLoc,
                                            NamespaceLoc, IdLoc, Id,
                                            T.getOpenLocation(), 
                                            Attrs.getList(), ImplicitUsing);

  // Parse the declarations within the namespace. Note that this will match
  // the closing brace. We don't allow nested specifiers for the vector.
  std::vector<IdentifierInfo *> NsIds;
  std::vector<SourceLocation> NsIdLocs;
  std::vector<SourceLocation> NsLocs;
  ParseInnerNamespace(NsIdLocs, NsIds, NsLocs, 0, InlineLoc, Attrs, T);

  NamespaceScope.Exit();

  Actions.ActOnFinishNamespaceDef(Ns, T.getCloseLocation());
  if (Ns->isInvalidDecl())
    return nullptr;
  
  return Actions.ActOnFinishCXXFragment(getCurScope(), Fragment, Ns);
}

/// Parses a class fragment. Returns the completed fragment declaration.
Decl *Parser::ParseClassFragment(Decl *Fragment) {
  assert(Tok.isOneOf(tok::kw_struct, tok::kw_class, tok::kw_union) &&
         "expected 'struct', 'class', or 'union'");

  DeclSpec::TST TagType;
  if (Tok.is(tok::kw_struct))
    TagType = DeclSpec::TST_struct;
  else if (Tok.is(tok::kw_class))
    TagType = DeclSpec::TST_class;
  else
    TagType = DeclSpec::TST_union;

  SourceLocation ClassKeyLoc = ConsumeToken();
  IdentifierInfo *Id = nullptr;
  SourceLocation IdLoc;
  if (Tok.is(tok::identifier)) {
    Id = Tok.getIdentifierInfo();
    IdLoc = ConsumeToken();
  }

  // Build a tag type for the injected class.
  CXXScopeSpec SS;
  MultiTemplateParamsArg MTP;
  bool IsOwned;
  bool IsDependent;
  TypeResult TR;
  Decl *Class = Actions.ActOnTag(getCurScope(), TagType, 
                                 /*Metaclass=*/nullptr, Sema::TUK_Definition, 
                                 ClassKeyLoc, SS, Id, IdLoc, 
                                 /*AttributeList=*/nullptr, AS_none,
                                 /*ModulePrivateLoc=*/SourceLocation(), 
                                 MTP, IsOwned, IsDependent, 
                                 /*ScopedEnumKWLoc=*/SourceLocation(), 
                                 /*ScopeEnumUsesClassTag=*/false, TR,
                                 /*IsTypeSpecifier*/false);

  // Parse the class definition.
  ParsedAttributesWithRange PA(AttrFactory);
  ParseCXXMemberSpecification(ClassKeyLoc, SourceLocation(), PA, TagType,
                              Class);
  if (Class->isInvalidDecl())
    return nullptr;
  
  return Actions.ActOnFinishCXXFragment(getCurScope(), Fragment, Class);
}

/// Parses an enum fragment. Returns the completed fragment declaration.
Decl *Parser::ParseEnumFragment(Decl *Fragment) {
  llvm_unreachable("not implemented");
}

// StmtResult Parser::ParseCXXBlockInjection(SourceLocation ArrowLoc) {
//   assert(Tok.is(tok::kw_do) && "expected 'do'");

//   // FIXME: Save the introducer token?
//   ConsumeToken();

//   StmtResult Injection 
//       = Actions.ActOnInjectionStmt(getCurScope(), ArrowLoc, /*IsBlock=*/true);

//   // Parse the block statement as if it were a lambda '[]()stmt'. 
//   ParseScope BodyScope(this, Scope::BlockScope | 
//                              Scope::FnScope | 
//                              Scope::DeclScope);
//   Actions.ActOnStartBlockFragment(getCurScope());
//   StmtResult Body = ParseCompoundStatement();
//   Actions.ActOnFinishBlockFragment(getCurScope(), Body.get());
//   return Injection;
// }


/// Parse a fragment expression. It has the form:
///
///   fragment-expression:
///     '__fragment' fragment
ExprResult Parser::ParseCXXFragmentExpression() {
  assert(Tok.is(tok::kw___fragment) && "Expected __fragment");
  SourceLocation Loc = ConsumeToken();

  // Scrape automatic variables as captured constants.
  SmallVector<Expr *, 8> Captures;
  Decl *Fragment = ParseCXXFragment(Captures);
  if (!Fragment)
    return ExprError();

  return Actions.ActOnCXXFragmentExpr(Loc, Captures, Fragment);
}

/// \brief Parse a C++ injection statement.
///
///   injection-statement:
///     '__generate' reflection ';'
///     '__generate' fragment ';'
///
/// Note that the statement parser will collect the trailing semicolon.
StmtResult Parser::ParseCXXInjectionStatement() {
  assert(Tok.is(tok::kw___generate) && "expected __generate");;
  SourceLocation Loc = ConsumeToken();

  /// Get a reflection as the operand of the 
  ExprResult Reflection;
  switch (Tok.getKind()) {
    case tok::kw_namespace:
    case tok::kw_struct:
    case tok::kw_class:
    case tok::kw_union:
    case tok::kw_enum:
    case tok::l_brace: {
      SmallVector<Expr *, 8> Captures;
      Decl *Fragment = ParseCXXFragment(Captures);
      if (!Fragment)
        return StmtError();
      Reflection = Actions.ActOnCXXFragmentExpr(Loc, Captures, Fragment);
      break;
    }
    
    default: {
      Reflection = ParseConstantExpression();
      break;
    }
  }
  if (Reflection.isInvalid())
    return StmtResult();

  return Actions.ActOnCXXInjectionStmt(Loc, Reflection.get());
}

/// \brief Parse a C++ injection declaration.
///
///   injection-declaration:
///     '__inject' reflection ';'
///
/// Returns the group of declarations parsed.
Parser::DeclGroupPtrTy Parser::ParseCXXInjectionDeclaration() {
  assert(Tok.is(tok::kw___inject) && "expected __inject");
  SourceLocation Loc = ConsumeToken();

  /// Get a reflection as the operand of the 
  ExprResult Reflection = ParseConstantExpression();
  if (Reflection.isInvalid())
    return DeclGroupPtrTy();
  ExpectAndConsumeSemi(diag::err_expected_semi_after_fragment);

  return Actions.ActOnCXXInjectionDecl(Loc, Reflection.get());
}

/// \brief Parse a C++ extension declaration.
///
///   extension-declaration:
///     '__extend' '(' reflection ')' reflection ';'
///     '__extend' '(' reflection ')' fragment ';'
///
/// Returns the group of declarations parsed.
Parser::DeclGroupPtrTy Parser::ParseCXXExtensionDeclaration() {
  assert(Tok.is(tok::kw___extend) && "expected __extend");
  SourceLocation Loc = ConsumeToken();

  // Match the '(reflection)' clause.
  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.consumeOpen()) {
    Diag(Tok, diag::err_expected) << tok::l_paren;
    return nullptr;
  }
  ExprResult Injectee = ParseConstantExpression();
  if (Injectee.isInvalid())
    return DeclGroupPtrTy();
  if (T.consumeClose()) {
    Diag(Tok, diag::err_expected) << tok::l_paren;
    return nullptr;
  }

  // Get a reflection as the operand of the 
  ExprResult Reflection;
  switch (Tok.getKind()) {
    case tok::kw_namespace:
    case tok::kw_struct:
    case tok::kw_class:
    case tok::kw_union:
    case tok::kw_enum:
    case tok::l_brace: {
      SmallVector<Expr *, 8> Captures;
      Decl *Fragment = ParseCXXFragment(Captures);
      if (!Fragment)
        return DeclGroupPtrTy();
      Reflection = Actions.ActOnCXXFragmentExpr(Loc, Captures, Fragment);
      break;
    }
    
    default: {
      Reflection = ParseConstantExpression();
      break;
    }
  }
  if (Reflection.isInvalid())
    return DeclGroupPtrTy();

  // FIXME: Save the semicolon?
  ExpectAndConsumeSemi(diag::err_expected_semi_after_fragment);

  return Actions.ActOnCXXExtensionDecl(Loc, Injectee.get(), Reflection.get());
}
