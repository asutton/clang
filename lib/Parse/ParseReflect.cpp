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

ExprResult Parser::ParseReflectOperand(SourceLocation OpLoc)
{
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

/// \brief Parse a reflect expression.
///
///   primary-expression:
///     '$' id-expression
///     '$' type-id
///     '$' nested-name-specifier[opt] namespace-name
///
// TODO: Consider adding specifiers? $static? $private?
ExprResult Parser::ParseReflectExpression() {
  assert(Tok.is(tok::dollar));
  SourceLocation OpLoc = ConsumeToken();
  return ParseReflectOperand(OpLoc);
}

/// \brief Parse a reflexpr expression.
///
///   primary-expression:
///      'reflexpr' '(' id-expression ')'
///      'reflexpr' '(' type-id ')'
///      'reflexpr' '(' nested-name-specifier[opt] namespace-name ')'
ExprResult Parser::ParseReflexprExpression() {
  assert(Tok.is(tok::kw_reflexpr));
  SourceLocation KeyLoc = ConsumeToken();
  
  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.expectAndConsume(diag::err_expected_lparen_after, "reflexpr"))
    return ExprError();
  ExprResult Result = ParseReflectOperand(KeyLoc);
  T.consumeClose();
  if (!Result.isInvalid())
    Result = Actions.ActOnCXXReflexprExpr(Result.get(), 
                                          T.getOpenLocation(), 
                                          T.getCloseLocation());
  return Result;
}

/// \brief Parse a declname-id
///
///   unqualified-id:
///      'declname' '(' id-concatenation-seq ')'
///
///   id-concatenation-seq:
///       constant-expression
///       id-concatenation-seq constant-expression
///
/// Returns true if parsing or semantic analysis fail.
bool Parser::ParseDeclnameId(UnqualifiedId& Result) {
  assert(Tok.is(tok::kw_declname));
  SourceLocation KeyLoc = ConsumeToken();
  
  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.expectAndConsume(diag::err_expected_lparen_after, "declname"))
    return true;
  SmallVector<Expr *, 4> Parts;
  while (Tok.isNot(tok::r_paren)) {
    ExprResult Result = ParseConstantExpression();
    if (Result.isInvalid())
      return true;
    Parts.push_back(Result.get());
  }
  if (T.consumeClose())
    return true;

  return Actions.BuildDeclnameId(Parts, Result, KeyLoc, 
                                 T.getOpenLocation(), T.getCloseLocation());
}


/// Parse a reflection type specifier.
///
///   reflection-type-specifier
///     'typename' '(' constant-expression ')'
///
/// The constant-expression must be a reflection of a type.
TypeResult Parser::ParseTypeReflectionSpecifier(SourceLocation TypenameLoc,
                                                SourceLocation& EndLoc) {
  BalancedDelimiterTracker T(*this, tok::l_paren);
  if (T.expectAndConsume(diag::err_expected_lparen_after, "reflexpr"))
    return TypeResult(true);
  ExprResult Result = ParseConstantExpression();
  if (!T.consumeClose()) {
    EndLoc = T.getCloseLocation();
    if (!Result.isInvalid())
      return Actions.ActOnTypeReflectionSpecifier(TypenameLoc, Result.get());
  }
  return TypeResult(true);
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
///     unary-reflection-trait '(' expression ')'
///     binary-reflection-trait '(' expression ',' expression ')'
///
///   unary-reflection-trait:
///     '__reflect_name'
///     '__reflect_qualified_name'
///     '__reflect_type'
///     '__reflect_traits'
///     '__reflect_specifiers'
///     '__reflect_pointer'
///     '__reflect_value'
///     '__reflect_num_parameters'
///     '__reflect_declaration_context'
///     '__reflect_lexical_context'
///     '__reflect_num_members'
///
///   binary-reflection-trait:
///     '__reflect_parameter'
///     '__reflect_member'
///     '__modify_access'
///     '__modify_virtual'
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

/// \brief Replace the current identifier token (and possibly the C++ scope
/// specifier that precedes it) with a C++ metaclass-name annotation token.
///
/// \param SS         If non-null, the C++ scope specifier that qualifies the
///                   metaclass-name and was extracted from the preceding scope
///                   annotation token.
/// \param Metaclass  The C++ metaclass declaration that corresponds to the
///                   metaclass-name.
void Parser::AnnotateMetaclassName(CXXScopeSpec *SS, Decl *Metaclass) {
  assert(getLangOpts().Reflection &&
         "Can only annotate metaclass-names when C++ reflection is enabled");
  assert(Tok.is(tok::identifier));

  // Replace the current token with an annotation token.
  Tok.setKind(tok::annot_metaclass);
  Tok.setAnnotationValue(Metaclass);
  Tok.setAnnotationEndLoc(Tok.getLocation());
  if (SS && SS->isNotEmpty()) // C++ qualified metaclass-name.
    Tok.setLocation(SS->getBeginLoc());

  // Update any cached tokens.
  PP.AnnotateCachedTokens(Tok);
}

/// Parse a C++ metaclass definition.
///
/// \verbatim
///   metaclass-name:
///     identifier
///
///   metaclass-definition:
///     metaclass-head '{' member-specification[opt] '}'
///
///   metaclass-head:
///     '$class' metaclass-name metaclass-base-clause[opt]
/// \endverbatim
Parser::DeclGroupPtrTy Parser::ParseMetaclassDefinition() {
  assert(Tok.is(tok::dollar));
  SourceLocation DLoc = ConsumeToken();
  // For now, pretend we are defining a class that was declared with the
  // 'struct' class-key.
  DeclSpec::TST TagType = DeclSpec::TST_struct;
  assert(Tok.is(tok::kw_class)); // TODO: Support for '$struct' and '$union'?
  ConsumeToken();

  // TODO: Parse attributes?
  ParsedAttributesWithRange attrs(AttrFactory);
  SourceLocation AttrFixItLoc = Tok.getLocation();

  // Parse the metaclass name.
  assert(Tok.is(tok::identifier));
  IdentifierInfo *II = Tok.getIdentifierInfo();
  SourceLocation IdLoc = ConsumeToken();

  if (Tok.isNot(tok::colon) && Tok.isNot(tok::l_brace)) {
    Diag(Tok, diag::err_expected_either) << tok::colon << tok::l_brace;
    return nullptr;
  }

  Decl *Metaclass = Actions.ActOnMetaclass(getCurScope(), DLoc, IdLoc, II);
  CXXRecordDecl *MetaclassDef = nullptr;

  // Enter a scope for the metaclass.
  ParseScope MetaclassScope(this, Scope::DeclScope);

  Actions.ActOnMetaclassStartDefinition(getCurScope(), Metaclass, MetaclassDef);

  PrettyDeclStackTraceEntry CrashInfo(Actions, Metaclass, DLoc,
                                      "parsing metaclass body");

  // Parse the body of the metaclass.
  ParseCXXMemberSpecification(DLoc, AttrFixItLoc, attrs, TagType, MetaclassDef);

  if (MetaclassDef->isInvalidDecl()) {
    Actions.ActOnMetaclassDefinitionError(getCurScope(), Metaclass);
    return nullptr;
  }

  Actions.ActOnMetaclassFinishDefinition(getCurScope(), Metaclass,
                                         MetaclassDef->getBraceRange());

  return Actions.ConvertDeclToDeclGroup(Metaclass);
}

/// Parse a C++ metaclass-base-specifier.
///
/// Note that we only check that the result names a type; semantic analysis will
/// need to verify that the type names a class. The result is either a type or
/// null, depending on whether a type name was found.
///
/// \verbatim
///   metaclass-base-clause:
///     ':' metaclass-base-specifier-list
///
///   metaclass-base-specifier-list:
///     metaclass-base-specifier
///     metaclass-base-specifier ',' metaclass-base-specifier
///
///   metaclass-base-specifier:
///     nested-name-specifier[opt] metaclass-name
/// \endverbatim
TypeResult Parser::ParseMetaclassBaseSpecifier(SourceLocation &BaseLoc,
                                               SourceLocation &EndLocation) {
  // Parse optional nested-name-specifier.
  CXXScopeSpec SS;
  ParseOptionalCXXScopeSpecifier(SS, nullptr, /*EnteringContext=*/false);

  BaseLoc = Tok.getLocation();

  if (Tok.isNot(tok::identifier)) {
    Diag(Tok, diag::err_expected_class_name);
    return true;
  }

  IdentifierInfo *Id = Tok.getIdentifierInfo();
  SourceLocation IdLoc = ConsumeToken();

  // We have an identifier; check whether it is actually is a metaclass.
  IdentifierInfo *CorrectedII = nullptr;
  ParsedType Type =
      Actions.getMetaclassName(*Id, IdLoc, getCurScope(), &SS,
                               /*NonTrivialTypeSourceInfo=*/true, &CorrectedII);

  if (!Type) {
    Diag(IdLoc, diag::err_expected_class_name);
    return true;
  }

  // Consume the identifier.
  EndLocation = IdLoc;

  // Fake up a Declarator to use with ActOnTypeName.
  DeclSpec DS(AttrFactory);
  DS.SetRangeStart(IdLoc);
  DS.SetRangeEnd(EndLocation);
  DS.getTypeSpecScope() = SS;

  const char *PrevSpec = nullptr;
  unsigned DiagID;
  DS.SetTypeSpecType(TST_typename, IdLoc, PrevSpec, DiagID, Type,
                     Actions.getASTContext().getPrintingPolicy());

  Declarator DeclaratorInfo(DS, Declarator::TypeNameContext);
  return Actions.ActOnTypeName(getCurScope(), DeclaratorInfo);
}

/// Parse a constexpr-declaration.
///
/// \verbatim
///   constexpr-declaration:
///     'constexpr' compound-statement
/// \endverbatim
Parser::DeclGroupPtrTy Parser::ParseConstexprDeclaration() {
  assert(getLangOpts().CPlusPlus1z &&
         "Can only parse constexpr declarations in C++1z");
  assert(Tok.is(tok::kw_constexpr));

  SourceLocation ConstexprLoc = ConsumeToken();

  if (!Tok.is(tok::l_brace)) {
    Diag(Tok, diag::err_expected) << tok::l_brace;
    return nullptr;
  }

  unsigned ScopeFlags;
  Decl *D = Actions.ActOnConstexprDecl(getCurScope(), ConstexprLoc, ScopeFlags);

  // Enter a scope for the constexpr declaration body.
  ParseScope BodyScope(this, ScopeFlags);

  Actions.ActOnStartConstexprDecl(getCurScope(), D);

  PrettyDeclStackTraceEntry CrashInfo(Actions, D, ConstexprLoc,
                                      "parsing constexpr declaration body");

  // Parse the body of the constexpr declaration.
  StmtResult Body(ParseCompoundStatementBody());

  if (!Body.isInvalid())
    Actions.ActOnFinishConstexprDecl(getCurScope(), D, Body.get());
  else
    Actions.ActOnConstexprDeclError(getCurScope(), D);

  return Actions.ConvertDeclToDeclGroup(D);
}
