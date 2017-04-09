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

void
Parser::ParseInjectedNamespaceMember(Stmt *S)
{
  ArrayRef<Token> Toks = Actions.GetTokensToInject(S);
  PP.EnterTokenStream(Toks, true);

  SourceLocation End;
  ParsedAttributesWithRange Attrs(AttrFactory);
  DeclGroupPtrTy Decls = ParseDeclaration(Declarator::FileContext, End, Attrs);
  (void)Decls;
}

void
Parser::ParseInjectedClassMember(Stmt *S)
{
  ArrayRef<Token> Toks = Actions.GetTokensToInject(S);
  PP.EnterTokenStream(Toks, true);

  // for (const Token& tok : Toks)
  //   PP.DumpToken(tok);
  // llvm::errs() << "\n";


  // FIXME: This is entirely wrong. Lots of stuff to fix here.
  // 1. Get the current access specifier.
  // 2. Actually allow attributes to be parsed.
  // 3. Get information about the class if it's a template.
  DeclGroupPtrTy Decls = 
    ParseCXXClassMemberDeclaration(AS_public, /*AccessAttrs=*/nullptr, 
                                   ParsedTemplateInfo(), 
                                   /*TemplateDiags=*/nullptr);
  (void)Decls;
}

void
Parser::ParseInjectedStatement(Stmt *S)
{
  ArrayRef<Token> Toks = Actions.GetTokensToInject(S);
  PP.EnterTokenStream(Toks, true);

  StmtResult R = ParseStatement();
  (void)R;
}

void
Parser::InjectedNamespaceMemberCB(void *OpaqueParser, Stmt *Injection)
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

void
Parser::InjectedStatementCB(void *OpaqueParser, Stmt *Injection)
{
  Parser* P = reinterpret_cast<Parser*>(OpaqueParser);
  return P->ParseInjectedStatement(Injection);
}

