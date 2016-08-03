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

