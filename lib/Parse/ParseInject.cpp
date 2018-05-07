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
  // Add a new depth for template parameters. This ensures that any
  // template parameters within the fragment will not be referenced by 
  // template arguments during an instantiation. They will always be outside
  // the depth of a template argument list.
  TemplateParameterDepthRAII CurTemplateDepthTracker(TemplateParameterDepth);
  ++CurTemplateDepthTracker;


  // Implicitly capture automatic variables as captured constants.
  Actions.ActOnCXXFragmentCapture(Captures);

  // A name declared in the the fragment is not leaked into the enclosing
  // scope. That is, fragments names are only accessible from within.
  ParseScope FragmentScope(this, Scope::DeclScope | Scope::FragmentScope);

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

  // FIXME: We could accept an idexpr here, except that those names aren't
  // exported. They're really only meant to be used for self-references
  // within the fragment.
  if (Tok.isNot(tok::identifier) && Tok.isNot(tok::l_brace)) {
    Diag(Tok.getLocation(), diag::err_expected) << "class-fragment";
    Actions.ActOnFinishCXXFragment(getCurScope(), nullptr, nullptr);
    return nullptr;
  }

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

/// \brief Parse a C++ extension declaration.
///
///   extension-declaration:
///     '__extend' '(' reflection ')' reflection ';'
///     '__extend' '(' reflection ')' fragment ';'
///
/// Returns the group of declarations parsed.
StmtResult Parser::ParseCXXExtensionStatement() {
  assert(Tok.is(tok::kw___extend) && "expected __extend");
  SourceLocation Loc = ConsumeToken();

  // Match the '(reflection)' clause.
  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.consumeOpen()) {
    Diag(Tok, diag::err_expected) << tok::l_paren;
    return StmtError();
  }
  ExprResult Injectee = ParseConstantExpression();
  if (Injectee.isInvalid())
    return StmtError();
  if (T.consumeClose()) {
    Diag(Tok, diag::err_expected) << tok::l_paren;
    return StmtError();
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
    return StmtError();

  return Actions.ActOnCXXExtensionStmt(Loc, Injectee.get(), Reflection.get());
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

/// \brief Parse a generated type declaration.
///
///   generated-type-declaration:
///     'using' class-key identifier 'as' type-generator
///
///   type-generator:
///     generator-name '(' reflection ')'
///
///   generator-name:
///     id-expression
///
/// The type generator is 'like' a function call, except that the id-expression
/// denotes a function template that takes two arguments. The second is
/// given implicitly.
///
/// FIXME: Support union as a class key? What about enum?
Parser::DeclGroupPtrTy
Parser::ParseCXXGeneratedTypeDeclaration(SourceLocation UsingLoc)
{
  assert(Tok.is(tok::kw_class) || Tok.is(tok::kw_struct));

  // Match the class key.
  bool IsClass = Tok.is(tok::kw_class);
  ConsumeToken();

  // Match the identifier.
  IdentifierInfo *Id = nullptr;
  SourceLocation IdLoc;
  if (Tok.is(tok::identifier)) {
    Id = Tok.getIdentifierInfo();
    IdLoc = ConsumeToken();
  } else {
    Diag(Tok.getLocation(), diag::err_expected) << tok::identifier;
    return DeclGroupPtrTy();
  }

  // Match the context keyword "as".
  if (Tok.isNot(tok::identifier)) {
    Diag(Tok.getLocation(), diag::err_expected) << "as";
    return DeclGroupPtrTy();
  }
  IdentifierInfo *As = Tok.getIdentifierInfo();
  if (As->getName() != "as") {
    Diag(Tok.getLocation(), diag::err_expected) << "as";
    return DeclGroupPtrTy();
  }
  ConsumeToken();

  ExprResult Generator = ParseCXXIdExpression();
  if (Generator.isInvalid())
    return DeclGroupPtrTy();

  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.expectAndConsume(diag::err_expected_lparen_after, "generator-name"))
    return DeclGroupPtrTy();
  ExprResult Reflection = ParseConstantExpression();
  if (Reflection.isInvalid())
    return DeclGroupPtrTy();
  if (T.consumeClose())
    return DeclGroupPtrTy();

  return Actions.ActOnCXXGeneratedTypeDecl(UsingLoc, IsClass, IdLoc, Id,
                                           Generator.get(), 
                                           Reflection.get());

  // if (!Result.isInvalid())
  //   Result = Actions.ActOnCXXReflexprExpr(Result.get(), T.getOpenLocation(),
  //                                         T.getCloseLocation());

  return DeclGroupPtrTy();
}

// parameter:
//      '__inject' '(' constant-expression ')' identifier
//
// FIXME: Do I want an ellipsis here? Maybe consider alternative syntax
// like: 'using identifier = constant-expression'. 
bool Parser::ParseCXXInjectedParameter(
                       SmallVectorImpl<DeclaratorChunk::ParamInfo> &ParamInfo) {
  assert(Tok.is(tok::kw___inject) && "Expected __inject");
  SourceLocation Loc = ConsumeToken();
  
  if (ExpectAndConsume(tok::l_paren))
    return false;

  // The constant expression is unevaluated; we get everything we need
  // from it's type.
  EnterExpressionEvaluationContext Unevaluated(
      Actions, Sema::ExpressionEvaluationContext::Unevaluated);
  ExprResult Reflection = ParseConstantExpression();
  if (Reflection.isInvalid())
    return false;

  if (ExpectAndConsume(tok::r_paren))
    return false;

  IdentifierInfo *II = nullptr;
  if (Tok.is(tok::identifier)) {
    II = Tok.getIdentifierInfo();
    ConsumeToken();
  }

  Actions.ActOnCXXInjectedParameter(Loc, Reflection.get(), II, ParamInfo);
  return true;
}


void Parser::LateClassFragmentParserCallback(void *P,
                                             void *Cxt,
                                             void *Cls) {
  Parser* This = reinterpret_cast<Parser *>(P);
  This->LateParseClassFragment(Cxt, Cls);
}

void Parser::LateParseClassFragment(void *Cxt, void *Cls) {
}

void Parser::LateParsedDeclaration::ParseAfterInjection(void *Cxt) {

}

void Parser::LateParsedClass::ParseAfterInjection(void *Cxt) {
  
}

void Parser::LateParsedAttribute::ParseAfterInjection(void *Cxt) {
  
}

void Parser::LexedMethod::ParseAfterInjection(void *Cxt) {
  Self->ParseInjectedMethodDefinition(*this, Cxt);
}

void Parser::LateParsedMethodDeclaration::ParseAfterInjection(void *Cxt) {
  Self->ParseInjectedMethodDeclaration(*this, Cxt);
}

void Parser::LateParsedMemberInitializer::ParseAfterInjection(void *Cxt) {
  Self->ParseInjectedMemberInitializer(*this, Cxt);
}

void
Parser::ParseInjectedMethodDefinition(LexedMethod &Method, 
                                      void *Cxt) {
}

void
Parser::ParseInjectedMethodDeclaration(LateParsedMethodDeclaration &Method, 
                                       void *Cxt) {
}

void
Parser::ParseInjectedMemberInitializer(LateParsedMemberInitializer &Init,
                                       void *Cxt) {
}

