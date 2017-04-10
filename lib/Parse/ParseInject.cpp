//===--- ParseReflect.cpp - Reflection Parsing ----------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements parsing for C++ reflection.
//
//===----------------------------------------------------------------------===//

#include "RAIIObjectsForParser.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/PrettyDeclStackTrace.h"

using namespace clang;

/// injection-statement:
///   '->' '{' token-list '}'
///
/// FIXME: Allow '-> token-list ;' for non-nested injections?
StmtResult Parser::ParseCXXInjectionStmt()
{
  assert(Tok.is(tok::arrow));
  SourceLocation ArrowLoc = ConsumeToken();

  BalancedDelimiterTracker Braces(*this, tok::l_brace);
  if (Braces.expectAndConsume())
    return StmtError();

  // Consume all of the tokens up to but not including the closing brace.
  CachedTokens Toks; 
  ConsumeAndStoreUntil(tok::r_brace, Toks, false, false);

  if (Braces.consumeClose())
    return StmtError();

  return Actions.ActOnCXXInjectionStmt(ArrowLoc, 
                                       Braces.getOpenLocation(),
                                       Braces.getCloseLocation(),
                                       Toks);
}

// Enter the injected tokens in to the stream. Add to that the current
// token so that we replay it after the injected tokens.
void Parser::InjectTokens(Stmt *S, CachedTokens& Toks)
{
  // Build the list of tokens to inject.
  ArrayRef<Token> InjectedToks = Actions.GetTokensToInject(S);
  Toks.resize(InjectedToks.size() + 1);
  auto Iter = std::copy(InjectedToks.begin(), InjectedToks.end(), Toks.begin());
  *Iter = Tok;

  // Inject the tokens and consume the current token.
  PP.EnterTokenStream(Toks, true);
  ConsumeAnyToken();

  // Sanity check.
  assert(Tok.is(Toks.front().getKind()));
}

void Parser::ParseInjectedNamespaceMember(Stmt *S)
{
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

void Parser::ParseInjectedClassMember(Stmt *S)
{
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
                                 /*TemplateDiags=*/nullptr);
}

void Parser::ParseInjectedStatement(Stmt *S)
{
  CachedTokens Toks;
  InjectTokens(S, Toks);

  StmtVector Stmts;

  // FIXME: Parse a statement-seq.
  StmtResult R = ParseStatement();
  if (R.isInvalid())
    return;
  Stmts.push_back(R.get());

  // Build a compound statement to store the injected results.
  InjectedStmts = Actions.ActOnCompoundStmt(S->getLocStart(), 
                                            S->getLocEnd(),
                                            Stmts, false);
}

void Parser::InjectedNamespaceMemberCB(void *OpaqueParser, Stmt *Injection)
{
  Parser* P = reinterpret_cast<Parser*>(OpaqueParser);
  return P->ParseInjectedNamespaceMember(Injection);
}

void
Parser::InjectedClassMemberCB(void *OpaqueParser, Stmt *Injection)
{
  Parser* P = reinterpret_cast<Parser*>(OpaqueParser);
  return P->ParseInjectedClassMember(Injection);
}

void Parser::InjectedStatementCB(void *OpaqueParser, Stmt *Injection)
{
  Parser* P = reinterpret_cast<Parser*>(OpaqueParser);
  return P->ParseInjectedStatement(Injection);
}

