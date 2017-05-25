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

/// \brief Parse a C++ injection statement.
///
/// \verbatim
/// injection-statement:
///   '->' injection
///
/// injection:
///   compound-statement
///   class-key identifier_opt '{' member-specification_opt '}'
///   'namespace' identifier_opt '{' namespace-body '}'
///
/// TODO: Allow template and function parameters for local name bindings. 
/// For example:
///
///   immediate void leave_with_value() { -> (int x) { return x; } }
///
///   void foo() {
///     int x = 4;
///     constexpr { leave_with_value(); }
///   }
///
/// When the injection '-> (int x) ... ' is applied, we would perform lookup
/// on x at the injection site (e.g., after the '}' of the constexpr block).
/// That finds x, and so the resulting function would be:
///
///   void f() {
///     int x = 4;
///     return x;
///   }
///
/// TODO: Could we provide ALTERNATIVE bindings for the required names? Maybe
/// like this:
///
///   void bar() {
///     int y = 12;
///     constexpr using (x = y) { leave_with_value(); }
///   }
///
/// Here, the 'using' component would establish bind the name 'x' to 'y' before
/// evaluating the given function. Note that we don't actually *need* this
/// feature. We can define aliases for variables (references), types and
/// namespaces.
///
///   void bar() {
///     int y = 12;
///     constexpr { int& x = y; leave_with_value(); }
///   }
///
/// TODO: Is there a way that 'leave_with_value' can announce which names it
/// requires? Maybe something like this?
///
///   immediate void leave_with_value() using (int x) {
///     -> { return x; }
///   }
///
/// Here, 'x' is declared as an environment parameter and is is resolved
/// as such within the injection?
///
/// Maybe using functions for these things isn't the right thing to do. Perhaps:
///
///   using<typename T>(int x) leave_with_value() {
///     -> { return x; }
///   }
///
/// TODO: Can we automatically determine which names are unbound and skip
/// the parameters by default?
///
/// \endverbatim
StmtResult Parser::ParseCXXInjectionStmt() {
  assert(Tok.is(tok::arrow));
  SourceLocation ArrowLoc = ConsumeToken();

  // A name declared in the the injection statement is local to the injection
  // statement. Establish a new declaration scope for the following injection.
  ParseScope InjectionScope(this, Scope::DeclScope | Scope::InjectionScope);

  switch (Tok.getKind()) {
    case tok::l_brace:
      return ParseCXXBlockInjection(ArrowLoc);

    case tok::kw_struct:
    case tok::kw_class:
    case tok::kw_union:
      return ParseCXXClassInjection(ArrowLoc);

    case tok::kw_namespace:
      return ParseCXXNamespaceInjection(ArrowLoc);

    default:
      Diag(Tok.getLocation(), diag::err_expected_injection);
      return StmtError();
  }
}

StmtResult Parser::ParseCXXBlockInjection(SourceLocation ArrowLoc) {
  assert(Tok.is(tok::l_brace) && "expected '{'");

  // FIXME: What is the scope of variables appearing within this block? If
  // they're local to block, that's obvious. But can names refer to entities
  // outside of this scope (e.g., a metaclass?). Probably not. Do we need
  // to consider parameterized injections -- and how would those work exactly?
  //
  // Also, in return statements, what should the type be? Should we just
  // suppress certain checks if this is an injection.

  StmtResult R = ParseCompoundStatement();
  if (R.isInvalid())
    return R;
  return Actions.ActOnCXXBlockInjection(ArrowLoc, R.get());
}

StmtResult Parser::ParseCXXClassInjection(SourceLocation ArrowLoc) {
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
    return StmtError();
  return Actions.ActOnCXXClassInjection(ArrowLoc, Class);
}

StmtResult Parser::ParseCXXNamespaceInjection(SourceLocation ArrowLoc) {
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
    return StmtError();
  }

  BalancedDelimiterTracker T(*this, tok::l_brace);
  if (T.consumeOpen()) {
    Diag(Tok, diag::err_expected) << tok::l_brace;
    return StmtError();
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
  std::vector<IdentifierInfo *> Ids;
  std::vector<SourceLocation> IdLocs;
  std::vector<SourceLocation> NsLocs;
  ParseInnerNamespace(IdLocs, Ids, NsLocs, 0, InlineLoc, Attrs, T);

  NamespaceScope.Exit();

  Actions.ActOnFinishNamespaceDef(Ns, T.getCloseLocation());
  if (Ns->isInvalidDecl())
    return StmtError();
  return Actions.ActOnCXXNamespaceInjection(ArrowLoc, Ns);
}

#if 0
/// Enter the injected tokens into the stream. Append the current token to the
/// end of the new token stream so that we replay it after the injected tokens.
void Parser::InjectTokens(Stmt *S, CachedTokens &Toks) {
  // Build the list of tokens to inject.
  ArrayRef<Token> InjectedToks = Actions.GetTokensToInject(S);
  Toks.resize(InjectedToks.size() + 1);
  auto Iter = std::copy(InjectedToks.begin(), InjectedToks.end(), Toks.begin());
  *Iter = Tok;

  // llvm::errs() << "INJECTING\n";
  // for (Token K : InjectedToks) {
  //   PP.DumpToken(K);
  //   llvm::errs() << '\n';
  // }

  // Inject the tokens and consume the current token.
  PP.EnterTokenStream(Toks, true);
  ConsumeAnyToken();

  // Sanity check.
  assert(Tok.is(Toks.front().getKind()));
}

void Parser::ParseInjectedNamespaceMember(Stmt *S) {
  CachedTokens Toks;
  InjectTokens(S, Toks);

  // The parsing method depends on context.
  if (Actions.CurContext->isTranslationUnit()) {
    DeclGroupPtrTy Decls;
    ParseTopLevelDecl(Decls);
    Actions.getASTConsumer().HandleTopLevelDecl(Decls.get());
  } else {
    ParsedAttributesWithRange Attrs(AttrFactory);
    ParseExternalDeclaration(Attrs);
  }
}

void Parser::ParseInjectedClassMember(Stmt *S) {
  CachedTokens Toks;
  InjectTokens(S, Toks);

  // FIXME: This is entirely wrong. Lots of stuff to fix here:
  //
  // 1. Get the current access specifier.
  // 2. Actually allow attributes to be parsed.
  // 3. Get information about the class if it's a template.
  //
  // Note that we don't actually have to do anything with the resulting
  // class. Members are automatically registered in the current class when
  // parsed.
  ParseCXXClassMemberDeclaration(AS_public, /*AccessAttrs=*/nullptr,
                                 ParsedTemplateInfo(),
                                 /*TemplateDiags=*/nullptr,
                                 /*IsInjected=*/true);
}

void Parser::ParseInjectedStatement(Stmt *S) {
  CachedTokens Toks;
  InjectTokens(S, Toks);

  StmtVector Stmts;

  // FIXME: Parse a statement-seq.
  StmtResult R = ParseStatement();
  if (R.isInvalid())
    return;
  Stmts.push_back(R.get());

  // Build a compound statement to store the injected results.
  InjectedStmts =
      Actions.ActOnCompoundStmt(S->getLocStart(), S->getLocEnd(), Stmts, false);
}

void Parser::InjectedNamespaceMemberCB(void *OpaqueParser, Stmt *Injection) {
  Parser *P = reinterpret_cast<Parser *>(OpaqueParser);
  return P->ParseInjectedNamespaceMember(Injection);
}

void Parser::InjectedClassMemberCB(void *OpaqueParser, Stmt *Injection) {
  Parser *P = reinterpret_cast<Parser *>(OpaqueParser);
  return P->ParseInjectedClassMember(Injection);
}

void Parser::InjectedStatementCB(void *OpaqueParser, Stmt *Injection) {
  Parser *P = reinterpret_cast<Parser *>(OpaqueParser);
  return P->ParseInjectedStatement(Injection);
}
#endif