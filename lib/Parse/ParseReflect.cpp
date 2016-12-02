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

using namespace clang;

/// \brief Parse a reflect expression.
///
/// \verbatim
///   primary-expression:
///     '$' id-expression
///     '$' type-id
///     '$' nested-name-specifier[opt] namespace-name
/// \endverbatim
///
// TODO: Consider adding specifiers? $static? $private?
ExprResult Parser::ParseReflectExpression() {
  assert(Tok.is(tok::dollar));
  SourceLocation OpLoc = ConsumeToken();

  // TODO: Actually look at the token following the '$'. We should be able
  // to easily predict the parse.

  CXXScopeSpec SS;
  ParseOptionalCXXScopeSpecifier(SS, nullptr, /*EnteringContext=*/false);

  // If the next token is an identifier, try to resolve that. This will likely
  // match most uses of the reflection operator, but there are some cases
  // of id-expressions and type-ids that must be handled separately.
  if (!SS.isInvalid() && Tok.is(tok::identifier)) {
    SourceLocation IdLoc = Tok.getLocation();
    IdentifierInfo *II = Tok.getIdentifierInfo();
    ExprResult Expr = Actions.ActOnCXXReflectExpr(OpLoc, SS, II, IdLoc);
    if (!Expr.isInvalid()) {
      ConsumeToken();
      return Expr;
    }
  }

  // Determine if the operand is actually a type-id.
  if (isCXXTypeId(TypeIdAsTemplateArgument)) {
    DeclSpec DS(AttrFactory);
    ParseSpecifierQualifierList(DS);
    Declarator D(DS, Declarator::TypeNameContext);
    ParseDeclarator(D);
    return Actions.ActOnCXXReflectExpr(OpLoc, D);
  }

  // If not that, then this could be an id-expression. Try parsing this.
  Token Replacement;
  ExprResult Id = tryParseCXXIdExpression(SS, true, Replacement);
  if (!Id.isInvalid())
    return Actions.ActOnCXXReflectExpr(OpLoc, Id.get());
  return ExprError();
}

static ReflectionTrait ReflectionTraitKind(tok::TokenKind kind) {
  switch (kind) {
  default:
    llvm_unreachable("Not a known type trait");
#define REFLECTION_TRAIT_1(Spelling, K)                                        \
  case tok::kw_##Spelling:                                                     \
    return URT_##K;
#define REFLECTION_TRAIT_2(Spelling, K)                                        \
  case tok::kw_##Spelling:                                                     \
    return BRT_##K;
#include "clang/Basic/TokenKinds.def"
  }
}

static unsigned ReflectionTraitArity(tok::TokenKind kind) {
  switch (kind) {
  default:
    llvm_unreachable("Not a known type trait");
#define REFLECTION_TRAIT(N, Spelling, K)                                       \
  case tok::kw_##Spelling:                                                     \
    return N;
#include "clang/Basic/TokenKinds.def"
  }
}

/// \brief Parse a reflection trait.
///
/// \verbatim
///   primary-expression:
///     reflection-trait '(' expression-list ')'
///
///   reflection-trait:
///     '__reflect_name'
///     '__reflect_qualified_name'
///     '__reflect_type'
///     '__reflect_traits'
///     '__reflect_specifiers'
///     '__reflect_pointer'
///     '__reflect_value'
///     '__reflect_num_parameters'
///     '__reflect_parameter'
///     '__reflect_declaration_context'
///     '__reflect_lexical_context'
///     '__reflect_num_members'
///     '__reflect_member'
/// \endverbatim
ExprResult Parser::ParseReflectionTrait() {
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
