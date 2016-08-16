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


/// Parse a reflector trait.
///
///       primary-expression:
///          unary-reflector '(' constant-expression ')'
///          binary-reflector-trait '(' constant-expression ',' constant-expression ')'
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

  unsigned Arity = ReflectionTraitArity(Kind);
  if (Args.size() != Arity) {
    Diag(EndLoc, diag::err_type_trait_arity)
      << Arity << 0 << (Arity > 1) << (int)Args.size() << SourceRange(Loc);
    return ExprError();
  }

  // Check that we have an appropriate arity.
  if (!Arity && Args.empty()) {
    Diag(EndLoc, diag::err_type_trait_arity)
      << 1 << 1 << 1 << (int)Args.size() << SourceRange(Loc);
    return ExprError();
  }

  ReflectionTrait Trait = ReflectionTraitKind(Kind);
  return Actions.ActOnReflectionTrait(Trait, Loc, Args, EndLoc);
}


#if 0
/// Parse the __get_attribute_trait invocation.
///
///   get-attribute-trait:
///     __get_attribute ( assignment-expression , constant-expression )
///
ExprResult
Parser::ParseGetAttributeTraitExpr()
{
  assert(Tok.is(tok::kw___get_attribute));
  SourceLocation Loc = ConsumeToken();  
  
  BalancedDelimiterTracker Parens(*this, tok::l_paren);
  if (Parens.expectAndConsume())
    return ExprError();

  ExprResult Node = ParseAssignmentExpression();
  if (ExpectAndConsume(tok::comma))
    return ExprError();
  ExprResult Attr = ParseConstantExpression();
  
  if (Parens.consumeClose())
    return ExprError();

  return Actions.ActOnGetAttributeTraitExpr(Loc, Node, Attr);
}

ExprResult
Parser::ParseSetAttributeTraitExpr()
{
  llvm_unreachable("not implemented");
}

ExprResult
Parser::ParseGetArrayElementTraitExpr()
{
  assert(Tok.is(tok::kw___get_array_element));
  SourceLocation Loc = ConsumeToken();  
  
  BalancedDelimiterTracker Parens(*this, tok::l_paren);
  if (Parens.expectAndConsume())
    return ExprError();

  ExprResult Node = ParseAssignmentExpression();
  if (ExpectAndConsume(tok::comma))
    return ExprError();
  ExprResult Attr = ParseConstantExpression();
  if (ExpectAndConsume(tok::comma))
    return ExprError();
  ExprResult Elem = ParseAssignmentExpression();
  
  if (Parens.consumeClose())
    return ExprError();

  return Actions.ActOnGetArrayElementTraitExpr(Loc, Node, Attr, Elem);
}

ExprResult
Parser::ParseGetTupleElementTraitExpr()
{
  llvm_unreachable("not implemented");
}

#endif
