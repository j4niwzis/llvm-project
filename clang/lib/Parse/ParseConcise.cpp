//===--- ParseConcise.cpp - cppsh's concise declarations ------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// cppsh's concise declarations, parsed straight into the Sema actions of the
// C++ they stand for -- a DeclSpec and a Declarator for each name, a template
// parameter list, a function chunk:
//
//   x: T = e;                   a variable (`x: & = e`, `x: const = e`: auto)
//   f a b: T = e;               a function; an untyped parameter is auto
//   f(a: T = d, int b) { ... }  parenthesized: defaults, C++ parameters too
//   f<T, n: int = 3> ... = e;   explicit template parameters
//   f a: T' = e;                a primed name declares a type parameter
//   f a -> R ? C<R> = e;        a trailing return type, a requires-clause
//
// The body is a block, or `= expression`: a ReturnStmt built by Sema
// (ParseFunctionExpressionBody, ParseStmt.cpp).
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/QualTypeNames.h"
#include "clang/Basic/DiagnosticParse.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/RAIIObjectsForParser.h"
#include "clang/Sema/DeclSpec.h"
#include "clang/Sema/EnterExpressionEvaluationContext.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/ParsedTemplate.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/Sema.h"

using namespace clang;

bool Parser::isConciseContext() {
  return getLangOpts().CPlusPlus && Tok.is(tok::identifier) &&
         !PP.getSourceManager().isInSystemHeader(Tok.getLocation()) &&
         !PP.isBacktrackEnabled() &&
         !(getCurScope() && getCurScope()->isClassScope());
}

// Whether a name is declared here already -- a type, a template, anything:
// then `name ...` uses it, and declares no new function.
bool Parser::isConciseKnownName(const Token &T) {
  IdentifierInfo *II = T.getIdentifierInfo();
  if (!II)
    return false;
  if (Actions.getTypeName(*II, T.getLocation(), getCurScope()))
    return true;
  LookupResult R(Actions, II, T.getLocation(), Sema::LookupOrdinaryName);
  Actions.LookupName(R, getCurScope());
  R.suppressDiagnostics();
  return !R.empty();
}

// Whether the K-th token ahead begins the type of a concise declaration.
bool Parser::isConciseTypeStart(unsigned K) {
  Token T = GetLookAheadToken(K);
  if (T.isOneOf(tok::amp, tok::ampamp, tok::kw_auto, tok::kw_const,
                tok::kw_constexpr, tok::kw_volatile, tok::kw_int, tok::kw_long,
                tok::kw_short, tok::kw_char, tok::kw_bool, tok::kw_float,
                tok::kw_double, tok::kw_unsigned, tok::kw_signed, tok::kw_void,
                tok::kw_decltype))
    return true;
  if (!T.is(tok::identifier))
    return false;
  if (T.isCppshPrime() || GetLookAheadToken(K + 1).is(tok::coloncolon))
    return true;
  IdentifierInfo *II = T.getIdentifierInfo();
  if (Actions.getTypeName(*II, T.getLocation(), getCurScope()))
    return true;
  // A class or alias template: `x: vector<int> = ...`.
  if (!GetLookAheadToken(K + 1).is(tok::less))
    return false;
  LookupResult R(Actions, II, T.getLocation(), Sema::LookupOrdinaryName);
  Actions.LookupName(R, getCurScope());
  R.suppressDiagnostics();
  return llvm::any_of(R, [](NamedDecl *D) {
    return isa<ClassTemplateDecl, TypeAliasTemplateDecl,
               TemplateTemplateParmDecl>(D->getUnderlyingDecl());
  });
}

bool Parser::isConciseVariable() {
  return isConciseContext() && NextToken().is(tok::colon) &&
         isConciseTypeStart(2);
}

bool Parser::isConciseParameter() {
  return getLangOpts().CPlusPlus && Tok.is(tok::identifier) &&
         NextToken().is(tok::colon) &&
         !PP.getSourceManager().isInSystemHeader(Tok.getLocation());
}

// The template parameter list of a concise function, looked over from the
// K-th token ahead (its first parameter) without consuming anything: where
// it ends (End: the token after its `>`), and whether every parameter has a
// default.
bool Parser::scanConciseTemplateParams(unsigned K, unsigned &End,
                                       bool &AllDefaults) {
  AllDefaults = true;
  // Over a type (up to `=`, `,`, `>`) or a default (up to `,`, `>`).
  auto Skip = [&](bool StopAtEqual) {
    int Angle = 0, Depth = 0;
    while (true) {
      Token T = GetLookAheadToken(K);
      if (T.isOneOf(tok::eof, tok::semi))
        return false;
      if (Angle == 0 && Depth == 0 &&
          (T.isOneOf(tok::comma, tok::greater) ||
           (StopAtEqual && T.is(tok::equal))))
        return true;
      if (T.isOneOf(tok::l_paren, tok::l_brace, tok::l_square)) {
        ++Depth;
      } else if (T.isOneOf(tok::r_paren, tok::r_brace, tok::r_square)) {
        if (Depth == 0)
          return false;
        --Depth;
      } else if (T.is(tok::less)) {
        ++Angle;
      } else if (T.is(tok::greater)) {
        --Angle;
      } else if (T.is(tok::greatergreater)) {
        if (Angle < 2)
          return false;
        Angle -= 2;
      }
      ++K;
    }
  };
  while (true) {
    Token T = GetLookAheadToken(K);
    const bool Keyword = T.isOneOf(tok::kw_class, tok::kw_typename);
    if (Keyword)
      T = GetLookAheadToken(++K);
    if (!T.is(tok::identifier))
      return false;
    ++K;
    if (!Keyword && GetLookAheadToken(K).is(tok::colon)) {
      ++K;
      if (!Skip(/*StopAtEqual=*/true))
        return false;
    }
    const bool HasDefault = GetLookAheadToken(K).is(tok::equal);
    if (HasDefault) {
      ++K;
      if (!Skip(/*StopAtEqual=*/false))
        return false;
    }
    AllDefaults &= HasDefault;
    Token Next = GetLookAheadToken(K++);
    if (Next.is(tok::comma))
      continue;
    if (Next.is(tok::greater)) {
      End = K;
      return true;
    }
    return false;
  }
}

bool Parser::isConciseFunction() {
  if (!isConciseContext())
    return false;
  unsigned K = 1;
  bool Explicit = false;
  if (NextToken().is(tok::less) && !isConciseKnownName(Tok)) {
    unsigned End = 0;
    bool AllDefaults = false;
    if (!scanConciseTemplateParams(2, End, AllDefaults))
      return false;
    K = End;
    Explicit = true;
  }
  Token N = GetLookAheadToken(K);
  if (Explicit && N.isOneOf(tok::equal, tok::question, tok::kw_requires,
                            tok::arrow, tok::l_brace))
    return true;
  // `f a b: T = e`: parameters without parentheses.
  if (N.is(tok::identifier) && (Explicit || !isConciseKnownName(Tok))) {
    if (GetLookAheadToken(K + 1).is(tok::colon))
      return true;
    for (unsigned I = K + 1; I <= K + 7; ++I) {
      Token T = GetLookAheadToken(I);
      if (T.isOneOf(tok::equal, tok::question, tok::kw_requires, tok::arrow))
        return true;
      if (!T.is(tok::identifier))
        break;
    }
    return false;
  }
  if (N.is(tok::l_paren)) {
    Token A = GetLookAheadToken(K + 1), B = GetLookAheadToken(K + 2);
    if (A.is(tok::identifier) && B.is(tok::colon))
      return true;
    if (A.is(tok::r_paren) &&
        B.isOneOf(tok::equal, tok::question, tok::kw_requires) &&
        (Explicit || !Actions.getTypeName(*Tok.getIdentifierInfo(),
                                          Tok.getLocation(), getCurScope())))
      return true;
    return Explicit;
  }
  return false;
}

// Without parentheses, a `=` after a parameter is its default where another
// `=` -- the body's -- follows at depth 0; otherwise it is the body's own.
bool Parser::isConciseUnparenDefault() {
  int Depth = 0;
  for (unsigned K = 1;; ++K) {
    Token T = GetLookAheadToken(K);
    if (T.is(tok::eof) || (Depth == 0 && T.is(tok::semi)))
      return false;
    if (T.isOneOf(tok::l_paren, tok::l_brace, tok::l_square)) {
      ++Depth;
    } else if (T.isOneOf(tok::r_paren, tok::r_brace, tok::r_square)) {
      if (Depth == 0)
        return false;
      --Depth;
    } else if (Depth == 0 && T.is(tok::equal)) {
      return true;
    }
  }
}

void Parser::SetConciseAuto(DeclSpec &DS, SourceLocation Loc) {
  const char *PrevSpec = nullptr;
  unsigned DiagID = 0;
  DS.SetTypeSpecType(DeclSpec::TST_auto, Loc, PrevSpec, DiagID,
                     Actions.getASTContext().getPrintingPolicy());
  if (DS.getSourceRange().getBegin().isInvalid())
    DS.SetRangeStart(Loc);
  if (DS.getSourceRange().getEnd().isInvalid())
    DS.SetRangeEnd(Loc);
}

// The type after `name:` -- decl-specifiers, auto where they name no type
// (`&`, `const`, nothing). Its ptr-operators are the declarator's
// (ParseConciseDeclarator).
void Parser::ParseConciseType(DeclSpec &DS, DeclSpecContext DSC,
                              SourceLocation AutoLoc) {
  // A primed name no template declares here (a lambda's `a: T'`): auto.
  if (Tok.is(tok::identifier) && Tok.isCppshPrime() &&
      !Actions.getTypeName(*Tok.getIdentifierInfo(), Tok.getLocation(),
                           getCurScope())) {
    SetConciseAuto(DS, ConsumeToken());
    DS.Finish(Actions, Actions.getASTContext().getPrintingPolicy());
    return;
  }
  ParsedTemplateInfo TemplateInfo;
  ParseDeclarationSpecifiers(DS, TemplateInfo, AS_none, DSC);
  if (!DS.hasTypeSpecifier())
    SetConciseAuto(DS, DS.getSourceRange().getEnd().isValid()
                           ? DS.getSourceRange().getEnd()
                           : AutoLoc);
}

// The declarator of a concise declaration: its name came first, read
// already; what is left of it is the ptr-operators after the type.
void Parser::ParseConciseDeclarator(Declarator &D, IdentifierInfo *Name,
                                    SourceLocation NameLoc) {
  ConciseName = Name;
  ConciseNameLoc = NameLoc;
  ParseDeclaratorInternal(D, &Parser::ParseConciseDirectDeclarator);
  D.SetRangeBegin(NameLoc);
}

void Parser::ParseConciseDirectDeclarator(Declarator &D) {
  D.SetIdentifier(ConciseName, ConciseNameLoc);
}

// The tokens of a template parameter's type or default, kept to be parsed
// later (ConciseReplay) -- as clang keeps a member's default arguments.
void Parser::ConsumeAndStoreConcise(CachedTokens &Toks, bool StopAtEqual) {
  int Angle = 0, Depth = 0;
  while (Tok.isNot(tok::eof) && Tok.isNot(tok::semi)) {
    if (Angle == 0 && Depth == 0 &&
        (Tok.isOneOf(tok::comma, tok::greater) ||
         (StopAtEqual && Tok.is(tok::equal))))
      return;
    if (Tok.isOneOf(tok::l_paren, tok::l_brace, tok::l_square)) {
      ++Depth;
    } else if (Tok.isOneOf(tok::r_paren, tok::r_brace, tok::r_square)) {
      if (Depth == 0)
        return;
      --Depth;
    } else if (Tok.is(tok::less)) {
      ++Angle;
    } else if (Tok.is(tok::greater)) {
      --Angle;
    } else if (Tok.is(tok::greatergreater)) {
      if (Angle < 2)
        return;
      Angle -= 2;
    }
    Toks.push_back(Tok);
    ConsumeAnyToken();
  }
}

// Parse kept tokens next: they, an eof marked with Mark, then the current
// token again.
void Parser::ConciseReplay(ArrayRef<Token> Toks, const void *Mark) {
  auto Buf = std::make_unique<Token[]>(Toks.size() + 2);
  llvm::copy(Toks, Buf.get());
  Token &End = Buf[Toks.size()];
  End.startToken();
  End.setKind(tok::eof);
  End.setLocation(Toks.empty() ? Tok.getLocation() : Toks.back().getEndLoc());
  End.setEofData(Mark);
  Buf[Toks.size() + 1] = Tok;
  PP.EnterTokenStream(std::move(Buf), Toks.size() + 2,
                      /*DisableMacroExpansion=*/true, /*IsReinject=*/true);
  ConsumeAnyToken(/*ConsumeCodeCompletionTok=*/true);
}

void Parser::ConciseEndReplay(const void *Mark) {
  while (Tok.isNot(tok::eof))
    ConsumeAnyToken();
  if (Tok.getEofData() == Mark)
    ConsumeAnyToken();
}

Parser::DeclGroupPtrTy Parser::ParseConciseVariable(DeclaratorContext Ctx,
                                                    SourceLocation &DeclEnd) {
  IdentifierInfo *Name = Tok.getIdentifierInfo();
  const SourceLocation NameLoc = ConsumeToken();
  const SourceLocation ColonLoc = ConsumeToken();
  ParsingDeclSpec DS(*this);
  ParseConciseType(DS,
                   Ctx == DeclaratorContext::File
                       ? DeclSpecContext::DSC_top_level
                       : DeclSpecContext::DSC_normal,
                   ColonLoc);
  ParsedAttributes DAttrs(AttrFactory);
  ParsingDeclarator D(*this, DS, DAttrs, Ctx);
  ParseConciseDeclarator(D, Name, NameLoc);
  Decl *Var = ParseDeclarationAfterDeclaratorAndAttributes(D);
  D.complete(Var);
  DeclEnd = Tok.getLocation();
  if (ExpectAndConsumeSemi(Ctx == DeclaratorContext::File
                               ? diag::err_invalid_token_after_toplevel_declarator
                               : diag::err_expected_semi_declaration) &&
      !isDeclarationSpecifier(ImplicitTypenameContext::No))
    SkipMalformedDecl();
  SmallVector<Decl *, 1> Decls;
  if (Var)
    Decls.push_back(Var);
  return Actions.FinalizeDeclaratorGroup(getCurScope(), DS, Decls);
}

Parser::DeclGroupPtrTy Parser::ParseConciseFunction(SourceLocation &DeclEnd) {
  IdentifierInfo *Name = Tok.getIdentifierInfo();
  const SourceLocation NameLoc = ConsumeToken();
  const PrintingPolicy &Policy = Actions.getASTContext().getPrintingPolicy();

  // Every explicit parameter defaulted, and no parameter to call it with:
  // beside the template (whose parameters have no defaults then), a
  // function of no template arguments that calls it with the defaults --
  // its locals, so that a default read at run time is a need it is cut at
  // (ParseConciseForwarder).
  bool Forward = false;
  if (Tok.is(tok::less)) {
    unsigned End = 0;
    bool AllDefaults = false;
    Forward = scanConciseTemplateParams(1, End, AllDefaults) && AllDefaults &&
              GetLookAheadToken(End).isOneOf(tok::equal, tok::l_brace,
                                             tok::question, tok::kw_requires,
                                             tok::arrow);
  }

  // The primed names of the declaration (`T'`): its type parameters, beside
  // the explicit ones.
  SmallVector<std::pair<IdentifierInfo *, SourceLocation>, 2> Primes;
  for (unsigned K = 0, Depth = 0;; ++K) {
    Token T = GetLookAheadToken(K);
    if (T.is(tok::eof) || (Depth == 0 && T.is(tok::semi)))
      break;
    if (T.isOneOf(tok::l_paren, tok::l_brace, tok::l_square)) {
      ++Depth;
    } else if (T.isOneOf(tok::r_paren, tok::r_brace, tok::r_square)) {
      if (Depth > 0)
        --Depth;
      if (Depth == 0 && T.is(tok::r_brace))
        break;
    } else if (T.is(tok::identifier) && T.isCppshPrime() &&
               llvm::none_of(Primes, [&](const auto &P) {
                 return P.first == T.getIdentifierInfo();
               })) {
      Primes.emplace_back(T.getIdentifierInfo(), T.getLocation());
    }
  }

  std::vector<ConciseForwardArg> ForwardArgs;
  Decl *Fn = nullptr;
  SourceLocation CutLoc;
  {
    MultiParseScope TemplateParamScopes(*this);
    TemplateParameterDepthRAII DepthTracker(TemplateParameterDepth);
    TemplateParameterLists ParamLists;
    if (Tok.is(tok::less) || !Primes.empty()) {
      TemplateParamScopes.Enter(Scope::TemplateParamScope);
      const unsigned Depth = DepthTracker.getDepth();
      SmallVector<NamedDecl *, 4> TParams;
      SourceLocation LAngle, RAngle;
      if (Tok.is(tok::less)) {
        LAngle = ConsumeToken();
        while (true) {
          const bool Keyword = Tok.isOneOf(tok::kw_class, tok::kw_typename);
          const SourceLocation KeyLoc = Tok.getLocation();
          if (Keyword)
            ConsumeToken();
          if (Tok.isNot(tok::identifier)) {
            Diag(Tok, diag::err_expected) << tok::identifier;
            SkipUntil(tok::greater, StopAtSemi | StopBeforeMatch);
            break;
          }
          IdentifierInfo *PII = Tok.getIdentifierInfo();
          const SourceLocation PLoc = ConsumeToken();
          const unsigned Pos = TParams.size();
          NamedDecl *P = nullptr;
          if (Keyword || (Tok.isNot(tok::colon) && Tok.isNot(tok::equal))) {
            // `T`, `class T = int`: a type.
            SourceLocation EqLoc;
            ParsedType Default;
            if (Tok.is(tok::equal)) {
              if (Forward) {
                ConciseForwardArg &A = ForwardArgs.emplace_back();
                A.IsType = true;
                A.II = PII;
                A.Loc = PLoc;
                ConsumeToken();
                ConsumeAndStoreConcise(A.Default, /*StopAtEqual=*/false);
              } else {
                EqLoc = ConsumeToken();
                DelayTemplateIdDestructionRAII DontDestruct(*this, true);
                TemplateParameterDepthRAII DefaultDepth(TemplateParameterDepth);
                ++DefaultDepth;
                Default = ParseTypeName(/*Range=*/nullptr,
                                        DeclaratorContext::TemplateTypeArg)
                              .get();
              }
            }
            P = Actions.ActOnTypeParameter(
                getCurScope(), /*Typename=*/true, SourceLocation(),
                Keyword ? KeyLoc : PLoc, PII, PLoc, Depth, Pos, EqLoc, Default,
                /*HasTypeConstraint=*/false);
          } else if (Forward) {
            // A value whose default the forwarder gives: its type and its
            // `= default` kept, the type parsed now, the default there.
            ConciseForwardArg &A = ForwardArgs.emplace_back();
            A.IsType = false;
            A.II = PII;
            A.Loc = PLoc;
            if (TryConsumeToken(tok::colon))
              ConsumeAndStoreConcise(A.Type, /*StopAtEqual=*/true);
            if (Tok.is(tok::equal)) {
              A.Default.push_back(Tok);
              ConsumeToken();
              ConsumeAndStoreConcise(A.Default, /*StopAtEqual=*/false);
            }
            DeclSpec DS(AttrFactory);
            const bool Typed = !A.Type.empty();
            if (Typed) {
              ConciseReplay(A.Type, &A);
              ParseConciseType(DS, DeclSpecContext::DSC_template_param, PLoc);
            } else {
              SetConciseAuto(DS, PLoc);
              DS.Finish(Actions, Policy);
            }
            Declarator PD(DS, ParsedAttributesView::none(),
                          DeclaratorContext::TemplateParam);
            if (Typed) {
              ParseConciseDeclarator(PD, PII, PLoc);
              ConciseEndReplay(&A);
            } else {
              PD.SetIdentifier(PII, PLoc);
            }
            P = Actions.ActOnNonTypeTemplateParameter(
                getCurScope(), PD, Depth, Pos, SourceLocation(), nullptr);
          } else {
            // `n: int = 3`, `n = 3` (auto): a value.
            DeclSpec DS(AttrFactory);
            const SourceLocation ColonLoc = Tok.getLocation();
            if (TryConsumeToken(tok::colon)) {
              ParseConciseType(DS, DeclSpecContext::DSC_template_param,
                               ColonLoc);
            } else {
              SetConciseAuto(DS, PLoc);
              DS.Finish(Actions, Policy);
            }
            Declarator PD(DS, ParsedAttributesView::none(),
                          DeclaratorContext::TemplateParam);
            ParseConciseDeclarator(PD, PII, PLoc);
            SourceLocation EqLoc;
            ExprResult Default;
            if (Tok.is(tok::equal)) {
              EqLoc = ConsumeToken();
              DelayTemplateIdDestructionRAII DontDestruct(*this, true);
              GreaterThanIsOperatorScope G(GreaterThanIsOperator, false);
              TemplateParameterDepthRAII DefaultDepth(TemplateParameterDepth);
              ++DefaultDepth;
              EnterExpressionEvaluationContext ConstantEvaluated(
                  Actions,
                  Sema::ExpressionEvaluationContext::ConstantEvaluated);
              Default = Actions.ActOnConstantExpression(ParseInitializer());
              if (Default.isInvalid())
                SkipUntil(tok::comma, tok::greater,
                          StopAtSemi | StopBeforeMatch);
            }
            P = Actions.ActOnNonTypeTemplateParameter(
                getCurScope(), PD, Depth, Pos, EqLoc,
                Default.isUsable() ? Default.get() : nullptr);
          }
          if (P)
            TParams.push_back(P);
          if (!TryConsumeToken(tok::comma))
            break;
        }
        if (Tok.is(tok::greater)) {
          RAngle = ConsumeToken();
        } else {
          Diag(Tok, diag::err_expected) << tok::greater;
          SkipUntil(tok::greater, StopAtSemi | StopBeforeMatch);
          if (Tok.is(tok::greater))
            RAngle = ConsumeToken();
        }
      }
      for (const auto &Prime : Primes)
        if (llvm::none_of(TParams, [&](NamedDecl *P) {
              return P->getIdentifier() == Prime.first;
            }))
          if (NamedDecl *P = Actions.ActOnTypeParameter(
                  getCurScope(), /*Typename=*/true, SourceLocation(),
                  Prime.second, Prime.first, Prime.second, Depth,
                  TParams.size(), SourceLocation(), ParsedType(),
                  /*HasTypeConstraint=*/false))
            TParams.push_back(P);
      ParamLists.push_back(Actions.ActOnTemplateParameterList(
          Depth, SourceLocation(), NameLoc, LAngle, TParams, RAngle,
          /*RequiresClause=*/nullptr));
      ++DepthTracker;
    }

    // The function: `auto name(params) -> R`, its return type deduced where
    // none is said.
    ParsingDeclSpec FDS(*this);
    SetConciseAuto(FDS, NameLoc);
    FDS.Finish(Actions, Policy);
    ParsedAttributes DAttrs(AttrFactory);
    ParsingDeclarator D(*this, FDS, DAttrs,
                        DeclaratorContext::File);
    if (!ParamLists.empty())
      D.setTemplateParameterLists(ParamLists);
    D.SetIdentifier(Name, NameLoc);
    {
      ParseScope PrototypeScope(this, Scope::FunctionPrototypeScope |
                                          Scope::DeclScope |
                                          Scope::FunctionDeclarationScope);
      const bool Parens = Tok.is(tok::l_paren);
      BalancedDelimiterTracker T(*this, tok::l_paren);
      const SourceLocation LParen = Tok.getLocation();
      SourceLocation RParen;
      if (Parens)
        T.consumeOpen();
      Actions.ActOnStartFunctionDeclarationDeclarator(D, TemplateParameterDepth);
      SmallVector<DeclaratorChunk::ParamInfo, 8> ParamInfo;
      while (Tok.isNot(tok::eof)) {
        if (Parens ? Tok.is(tok::r_paren)
                   : Tok.isOneOf(tok::equal, tok::l_brace, tok::question,
                                 tok::kw_requires, tok::arrow, tok::semi))
          break;
        // `a: T`, a bare `a` (without parentheses: auto), or a C++ one.
        const bool Concise =
            Tok.is(tok::identifier) && NextToken().is(tok::colon);
        const bool Bare = !Parens && !Concise && Tok.is(tok::identifier);
        if (!Parens && !Concise && !Bare) {
          Diag(Tok, diag::err_expected) << tok::identifier;
          SkipUntil(tok::equal, tok::l_brace, StopAtSemi | StopBeforeMatch);
          break;
        }
        IdentifierInfo *PII = nullptr;
        const SourceLocation PLoc = Tok.getLocation();
        if (Concise || Bare) {
          PII = Tok.getIdentifierInfo();
          ConsumeToken();
        }
        DeclSpec PDS(AttrFactory);
        if (Concise) {
          const SourceLocation ColonLoc = ConsumeToken();
          ParseConciseType(PDS, DeclSpecContext::DSC_normal, ColonLoc);
        } else if (Bare) {
          SetConciseAuto(PDS, PLoc);
          PDS.Finish(Actions, Policy);
        } else {
          ParsedTemplateInfo TI;
          ParseDeclarationSpecifiers(PDS, TI, AS_none,
                                     DeclSpecContext::DSC_normal);
        }
        Declarator PD(PDS, ParsedAttributesView::none(),
                      DeclaratorContext::Prototype);
        if (Concise)
          ParseConciseDeclarator(PD, PII, PLoc);
        else if (Bare)
          PD.SetIdentifier(PII, PLoc);
        else
          ParseDeclarator(PD);
        Decl *Param = Actions.ActOnParamDeclarator(getCurScope(), PD);
        if (Tok.is(tok::equal) && (Parens || isConciseUnparenDefault())) {
          const SourceLocation EqLoc = ConsumeToken();
          DelayTemplateIdDestructionRAII DontDestruct(*this, true);
          EnterExpressionEvaluationContext Eval(
              Actions,
              Sema::ExpressionEvaluationContext::PotentiallyEvaluatedIfUsed,
              Param);
          ExprResult Default;
          if (Tok.is(tok::l_brace))
            Default = ParseBraceInitializer();
          else if (Parens)
            Default = ParseAssignmentExpression();
          else // up to the next parameter or the body's `=`
            Default = ParseRHSOfBinaryExpression(
                ParseCastExpression(CastParseKind::AnyCastExpr),
                prec::Conditional);
          if (Default.isInvalid())
            Actions.ActOnParamDefaultArgumentError(Param, EqLoc, nullptr);
          else
            Actions.ActOnParamDefaultArgument(Param, EqLoc, Default.get());
        }
        ParamInfo.push_back(DeclaratorChunk::ParamInfo(
            PD.getIdentifier(), PD.getIdentifierLoc(), Param));
        if (!Parens) {
          TryConsumeToken(tok::comma);
        } else if (!TryConsumeToken(tok::comma) && Tok.isNot(tok::r_paren)) {
          Diag(Tok, diag::err_expected) << tok::r_paren;
          SkipUntil(tok::r_paren, StopAtSemi | StopBeforeMatch);
          break;
        }
      }
      if (Parens) {
        T.consumeClose();
        RParen = T.getCloseLocation();
      } else {
        RParen = PrevTokLocation;
      }
      SourceLocation EndLoc = RParen;
      TypeResult TrailingReturn;
      SourceLocation TrailingLoc;
      if (Tok.is(tok::arrow)) {
        SourceRange Range;
        TrailingReturn =
            ParseTrailingReturnType(Range, /*MayBeFollowedByDirectInit=*/false);
        TrailingLoc = Range.getBegin();
        EndLoc = Range.getEnd();
      }
      D.AddTypeInfo(
          DeclaratorChunk::getFunction(
              /*HasProto=*/true, /*IsAmbiguous=*/false, LParen,
              ParamInfo.data(), ParamInfo.size(), SourceLocation(), RParen,
              /*RefQualifierIsLvalueRef=*/true, SourceLocation(),
              SourceLocation(), EST_None, SourceRange(), nullptr, nullptr, 0,
              nullptr, nullptr, {}, LParen, EndLoc, D, TrailingReturn,
              TrailingLoc),
          ParsedAttributes(AttrFactory), EndLoc);
      Actions.ActOnFinishFunctionDeclarationDeclarator(D);
    }

    // `? C<T>` (or `requires C<T>`): its trailing requires-clause.
    if (Tok.isOneOf(tok::question, tok::kw_requires)) {
      TemplateParameterDepthRAII RequiresDepth(TemplateParameterDepth);
      if (ParamLists.empty() && D.getInventedTemplateParameterList())
        ++RequiresDepth;
      ParseScope ParamScope(this, Scope::DeclScope |
                                      Scope::FunctionDeclarationScope |
                                      Scope::FunctionPrototypeScope);
      ConsumeToken();
      Actions.ActOnStartTrailingRequiresClause(getCurScope(), D);
      ExprResult Clause = Actions.ActOnFinishTrailingRequiresClause(
          ParseConstraintLogicalOrExpression(
              /*IsTrailingRequiresClause=*/true));
      if (Clause.isUsable())
        D.setTrailingRequiresClause(Clause.get());
      else
        SkipUntil(tok::equal, tok::l_brace, StopAtSemi | StopBeforeMatch);
    }

    const ParsedTemplateInfo TemplateInfo =
        ParamLists.empty()
            ? ParsedTemplateInfo()
            : ParsedTemplateInfo(&ParamLists, /*isSpecialization=*/false);
    // `= { ... }` is a block too.
    if (Tok.is(tok::equal) && NextToken().is(tok::l_brace))
      ConsumeToken();
    if (Tok.is(tok::l_brace)) {
      LateParsedAttrList LateAttrs(/*PSoon=*/true);
      Fn = ParseFunctionDefinition(D, TemplateInfo, &LateAttrs);
      TryConsumeToken(tok::semi);
    } else if (Tok.is(tok::equal)) {
      Fn = ParseFunctionExpressionBody(D, TemplateInfo);
    } else {
      Diag(Tok, diag::err_expected_fn_body);
      SkipUntil(tok::semi);
      return nullptr;
    }
    CutLoc = PrevTokLocation;
  }
  DeclEnd = PrevTokLocation;
  if (!Fn)
    return nullptr;

  SmallVector<Decl *, 2> Decls{Fn};
  if (Forward)
    if (FunctionDecl *Pattern = Fn->getAsFunction())
      if (FunctionTemplateDecl *Template =
              Pattern->getDescribedFunctionTemplate())
        if (Decl *Forwarder = ParseConciseForwarder(Name, NameLoc, CutLoc,
                                                    Template, ForwardArgs))
          Decls.push_back(Forwarder);
  return Actions.BuildDeclaratorGroup(Decls);
}

// `auto name() { using T = default; auto n = default; ...
//                return name<T, n, ...>(); }`
// -- each default parsed here, from its kept tokens, in the order given.
Decl *Parser::ParseConciseForwarder(IdentifierInfo *Name, SourceLocation Loc,
                                    SourceLocation CutLoc, Decl *Template,
                                    MutableArrayRef<ConciseForwardArg> Args) {
  ASTContext &Context = Actions.getASTContext();
  const PrintingPolicy &Policy = Context.getPrintingPolicy();
  ParsingDeclSpec DS(*this);
  SetConciseAuto(DS, Loc);
  DS.Finish(Actions, Policy);
  ParsedAttributes DAttrs(AttrFactory);
  ParsingDeclarator D(*this, DS, DAttrs,
                      DeclaratorContext::File);
  D.SetIdentifier(Name, Loc);
  {
    ParseScope PrototypeScope(this, Scope::FunctionPrototypeScope |
                                        Scope::DeclScope |
                                        Scope::FunctionDeclarationScope);
    D.AddTypeInfo(DeclaratorChunk::getFunction(
                      /*HasProto=*/true, /*IsAmbiguous=*/false, Loc, nullptr,
                      0, SourceLocation(), Loc,
                      /*RefQualifierIsLvalueRef=*/true, SourceLocation(),
                      SourceLocation(), EST_None, SourceRange(), nullptr,
                      nullptr, 0, nullptr, nullptr, {}, Loc, Loc, D),
                  ParsedAttributes(AttrFactory), Loc);
  }
  ParseScope BodyScope(this, Scope::FnScope | Scope::DeclScope |
                                 Scope::CompoundStmtScope);
  Sema::FPFeaturesStateRAII SaveFPFeatures(Actions);
  Decl *Fn = Actions.ActOnStartOfFunctionDef(getCurScope(), D,
                                             MultiTemplateParamsArg());
  D.complete(Fn);
  D.getMutableDeclSpec().abort();

  StmtResult Body;
  {
    Sema::CompoundScopeRAII CompoundScope(Actions);
    SmallVector<Stmt *, 8> Stmts;
    TemplateArgumentListInfo TemplateArgs(Loc, Loc);
    // The call again as the text of a continuation, where it is cut at
    // (the continuations are text yet).
    std::string Rest = "return " + Name->getName().str() + "<";
    bool Ok = true;
    for (ConciseForwardArg &A : Args) {
      if (&A != &Args.front())
        Rest += ", ";
      if (A.IsType) {
        ConciseReplay(A.Default, &A);
        TypeResult Ty = ParseTypeName();
        ConciseEndReplay(&A);
        if (Ty.isInvalid()) {
          Ok = false;
          continue;
        }
        TypeSourceInfo *TSI = nullptr;
        QualType QT = Sema::GetTypeFromParser(Ty.get(), &TSI);
        if (!TSI)
          TSI = Context.getTrivialTypeSourceInfo(QT, A.Loc);
        TemplateArgs.addArgument(TemplateArgumentLoc(TemplateArgument(QT), TSI));
        // Named in the defaults after it.
        UnqualifiedId AliasName;
        AliasName.setIdentifier(A.II, A.Loc);
        if (Decl *Alias = Actions.ActOnAliasDeclaration(
                getCurScope(), AS_none, MultiTemplateParamsArg(), A.Loc,
                AliasName, ParsedAttributesView::none(), Ty, nullptr)) {
          StmtResult S = Actions.ActOnDeclStmt(
              Actions.ConvertDeclToDeclGroup(Alias), A.Loc, A.Loc);
          if (S.isUsable())
            Stmts.push_back(S.get());
        }
        Rest += TypeName::getFullyQualifiedName(QT, Context, Policy,
                                                /*WithGlobalNsPrefix=*/true);
        continue;
      }
      // `Type n = default;`, auto where no type is said.
      CachedTokens Toks(A.Type);
      Toks.append(A.Default.begin(), A.Default.end());
      ConciseReplay(Toks, &A);
      ParsingDeclSpec VDS(*this);
      if (A.Type.empty()) {
        SetConciseAuto(VDS, A.Loc);
        VDS.Finish(Actions, Policy);
      } else {
        ParseConciseType(VDS, DeclSpecContext::DSC_normal, A.Loc);
      }
      ParsedAttributes VDAttrs(AttrFactory);
      ParsingDeclarator VD(*this, VDS, VDAttrs,
                           DeclaratorContext::Block);
      ParseConciseDeclarator(VD, A.II, A.Loc);
      Decl *Var = ParseDeclarationAfterDeclaratorAndAttributes(VD);
      VD.complete(Var);
      ConciseEndReplay(&A);
      SmallVector<Decl *, 1> Group;
      if (Var)
        Group.push_back(Var);
      StmtResult S = Actions.ActOnDeclStmt(
          Actions.FinalizeDeclaratorGroup(getCurScope(), VDS, Group), A.Loc,
          A.Loc);
      if (S.isUsable())
        Stmts.push_back(S.get());
      auto *V = dyn_cast_or_null<VarDecl>(Var);
      if (!V) {
        Ok = false;
        continue;
      }
      Expr *Ref = Actions.BuildDeclRefExpr(
          V, V->getType().getNonReferenceType(), VK_LValue, A.Loc);
      TemplateArgs.addArgument(TemplateArgumentLoc(
          TemplateArgument(Ref, /*IsCanonical=*/false), Ref));
      Rest += A.II->getName().str();
    }
    Rest += ">();";
    if (Ok) {
      LookupResult R(Actions, DeclarationNameInfo(Name, Loc),
                     Sema::LookupOrdinaryName);
      R.addDecl(cast<NamedDecl>(Template));
      R.resolveKind();
      CppshBuiltBody Saved = CppshBeginBuiltReturn(Loc);
      CXXScopeSpec SS;
      ExprResult Callee = Actions.BuildTemplateIdExpr(
          SS, SourceLocation(), R, /*RequiresADL=*/false, &TemplateArgs);
      ExprResult Call =
          Callee.isUsable()
              ? Actions.ActOnCallExpr(getCurScope(), Callee.get(), Loc,
                                      MultiExprArg(), Loc)
              : ExprError();
      CppshFinishBuiltReturn(Saved, Stmts, Call, CutLoc, Rest);
    }
    Body = Actions.ActOnCompoundStmt(Loc, Loc, Stmts, /*isStmtExpr=*/false);
  }
  BodyScope.Exit();
  return Actions.ActOnFinishFunctionBody(Fn, Body.get());
}
