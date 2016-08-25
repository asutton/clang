//===--- ParseExprCXX.cpp - C++ Expression Parsing ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the Expression parsing implementation for C++.
//
//===----------------------------------------------------------------------===//
#include "clang/AST/ASTContext.h"
#include "RAIIObjectsForParser.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Basic/PrettyStackTrace.h"
#include "clang/Lex/LiteralSupport.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/DeclSpec.h"
#include "clang/Sema/ParsedTemplate.h"
#include "clang/Sema/Scope.h"
#include "llvm/Support/ErrorHandling.h"
using namespace clang;


/// Parse a reflect expression.
///
///   primary-expression:
///     '$' id-expression
///     '$' type-id
///     '$' nested-name-specifier[opt] namespace-name
///
/// TODO: Consider adding specifiers? $static? $private?
ExprResult
Parser::ParseReflectExpression()
{
  assert(Tok.is(tok::dollar));
  SourceLocation OpLoc = ConsumeToken();

  // Tentatively parse the nested name specifier before parsing an expression.
  // Semantically, if we can't resolve this, then we're going to fail quietly,
  // and match this as either a type or expression.
  TentativeParsingAction TPA(*this);
  CXXScopeSpec SS;
  ParseOptionalCXXScopeSpecifier(SS, nullptr, /*EnteringContext=*/false);
  if (!SS.isInvalid() && Tok.is(tok::identifier)) {
    IdentifierInfo* II = Tok.getIdentifierInfo();
    SourceLocation IdLoc = ConsumeToken();
    ExprResult Expr = Actions.ActOnCXXReflectExpr(OpLoc, SS, II, IdLoc);
    if (!Expr.isInvalid()) {
      TPA.Commit();
      return Expr;
    }
  }
  TPA.Revert();

  // Potentially parse the type-id.
  if (isTypeIdUnambiguously()) {
    DeclSpec DS(AttrFactory);
    ParseSpecifierQualifierList(DS);
    Declarator D(DS, Declarator::TypeNameContext);
    ParseDeclarator(D);
    return Actions.ActOnCXXReflectExpr(OpLoc, D);
  }

  // We might have previously classified the token as a primary expression.
  if (Tok.is(tok::annot_primary_expr)) {
    ExprResult Primary = getExprAnnotation(Tok);
    ConsumeToken();
    return Actions.ActOnCXXReflectExpr(OpLoc, Primary.get());
  }

  // Otherwise, this is an unparsed expression.
  ExprResult Id = ParseCXXIdExpression(false);
  if (!Id.isInvalid())
    return Actions.ActOnCXXReflectExpr(OpLoc, Id.get());
  return Id;
}


static ReflectionTrait ReflectionTraitKind(tok::TokenKind kind) {
  switch (kind) {
    default: llvm_unreachable("Not a known type trait");
#define REFLECTION_TRAIT_1(Spelling,K) \
    case tok::kw_##Spelling: return URT_##K;
#define REFLECTION_TRAIT_2(Spelling,K) \
    case tok::kw_##Spelling: return BRT_##K;
#include "clang/Basic/TokenKinds.def"
  }
}

static unsigned ReflectionTraitArity(tok::TokenKind kind) {
  switch (kind) {
    default: llvm_unreachable("Not a known type trait");
#define REFLECTION_TRAIT(N,Spelling,K) \
    case tok::kw_##Spelling: return N;
#include "clang/Basic/TokenKinds.def"
  }
}


/// Parse a reflection trait.
///
///       primary-expression:
///          reflection-trait '(' expression-list ')'
///
///       reflection-trait: one of
///          ...
ExprResult
Parser::ParseReflectionTrait()
{
  tok::TokenKind Kind = Tok.getKind();
  SourceLocation Loc = ConsumeToken();
  
  // Parse any number of arguments in parens.
  BalancedDelimiterTracker Parens(*this, tok::l_paren);
  if (Parens.expectAndConsume())
    return ExprError();
  SmallVector<Expr *, 2> Args;
  do {
    ExprResult Expr = ParseConstantExpression();
    if (Expr.isInvalid()) {
      Parens.skipToEnd();
      return ExprError();
    }
    Args.push_back(Expr.get());
  } while (TryConsumeToken(tok::comma));
  if (Parens.consumeClose())
    return ExprError();
  SourceLocation EndLoc = Parens.getCloseLocation();

  // Make sure that the number of arguments matches the arity of trait.
  unsigned Arity = ReflectionTraitArity(Kind);
  if (Args.size() != Arity) {
    Diag(EndLoc, diag::err_type_trait_arity)
      << Arity << 0 << (Arity > 1) << (int)Args.size() << SourceRange(Loc);
    return ExprError();
  }

  ReflectionTrait Trait = ReflectionTraitKind(Kind);
  return Actions.ActOnReflectionTrait(Loc, Trait, Args, EndLoc);
}


