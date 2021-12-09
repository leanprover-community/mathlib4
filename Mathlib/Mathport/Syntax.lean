/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Elab.Quotation
import Mathlib.Tactic.Core
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ShowTerm
import Mathlib.Tactic.Simps
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.ToAdditive

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Lean

namespace Parser.Command

elab (name := include) "include " ident+ : command => ()
elab (name := omit) "omit " ident+ : command => ()
syntax (name := parameter) "parameter " bracketedBinder+ : command

syntax (name := noncomputableTheory) (docComment)? "noncomputable " "theory" : command

syntax bindersItem := "(" "..." ")"

syntax identScope := ":" "(" "scoped " ident " => " term ")"

syntax notation3Item := strLit <|> bindersItem <|> (ident (identScope)?)

macro ak:Term.attrKind "notation3 "
  prec:optPrecedence name:optNamedName prio:optNamedPrio
  lits:((ppSpace notation3Item)+) " => " val:term : command => do
  let args ← lits.getArgs.mapM fun lit =>
    let k := lit[0].getKind
    if k == strLitKind then `(macroArg| $(lit[0]):strLit)
    else if k == ``bindersItem then withFreshMacroScope `(macroArg| bi:explicitBinders)
    else withFreshMacroScope `(macroArg| $(lit[0]):ident:term)
  `($ak:attrKind macro
    $[$(prec.getOptional?):precedence]?
    $[$(name.getOptional?):namedName]?
    $[$(prio.getOptional?):namedPrio]?
    $(args[0]):macroArg $[$(args[1:].toArray):macroArg]* : term =>
    `(sorry))

end Parser.Command

namespace Parser.Term

syntax "quoteₓ " term : term
syntax "pquoteₓ " term : term
syntax "ppquoteₓ " term : term
syntax "%%ₓ" term : term

end Term

namespace Tactic

syntax tactic " <;> " "[" tactic,* "]" : tactic

end Tactic

namespace Tactic

syntax (name := propagateTags) "propagateTags " tacticSeq : tactic
syntax (name := fapply) "fapply " term : tactic
syntax (name := eapply) "eapply " term : tactic
syntax (name := applyWith) "apply " term " with " term : tactic
syntax (name := mapply) "mapply " term : tactic
syntax (name := toExpr') "toExpr' " term : tactic
syntax (name := withCases) "withCases " tacticSeq : tactic
syntax (name := induction') "induction' " casesTarget,+ (" using " ident)?
  (" with " (colGt binderIdent)+)? (" generalizing " (colGt ident)+)? : tactic
syntax caseArg := binderIdent,+ (" :" (ppSpace (ident <|> "_"))+)?
syntax (name := case') "case' " (("[" caseArg,* "]") <|> caseArg) " => " tacticSeq : tactic
syntax "destruct " term : tactic
syntax (name := cases') "cases' " casesTarget,+ (" using " ident)?
  (" with " (colGt binderIdent)+)? : tactic
syntax (name := casesM) "casesM" "*"? ppSpace term,* : tactic
syntax (name := casesType) "casesType" "*"? ppSpace ident* : tactic
syntax (name := casesType!) "casesType!" "*"? ppSpace ident* : tactic
syntax (name := abstract) "abstract" (ppSpace ident)? ppSpace tacticSeq : tactic

-- unstructured have/let/suffices
syntax (name := have'') "have " Term.haveIdLhs : tactic
syntax (name := let'') "let " Term.haveIdLhs : tactic
syntax (name := suffices') "suffices " Term.haveIdLhs : tactic

syntax (name := trace) "trace " term : tactic
syntax (name := existsi) "exists " term,* : tactic
syntax (name := eConstructor) "econstructor" : tactic
syntax (name := left) "left" : tactic
syntax (name := right) "right" : tactic
syntax (name := constructorM) "constructorM" "*"? ppSpace term,* : tactic
syntax (name := injections') "injections" (" with " (colGt (ident <|> "_"))+)? : tactic
syntax (name := simp') "simp'" "*"? (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := simpIntro) "simpIntro" (" (" &"config" " := " term ")")?
  (ppSpace (colGt (ident <|> "_")))* (&" only")? (" [" simpArg,* "]")? (" with " ident+)? : tactic
syntax (name := dsimp) "dsimp" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := symm) "symm" : tactic
syntax (name := trans) "trans" (ppSpace (colGt term))? : tactic
syntax (name := acRfl) "acRfl" : tactic
syntax (name := cc) "cc" : tactic
syntax (name := substVars) "substVars" : tactic
syntax (name := dUnfold) "dunfold" (" (" &"config" " := " term ")")?
  (ppSpace (colGt ident))* (ppSpace location)? : tactic
syntax (name := delta') "delta'" (colGt ident)* (ppSpace location)? : tactic
syntax (name := unfoldProjs) "unfoldProjs" (" (" &"config" " := " term ")")?
  (ppSpace location)? : tactic
syntax (name := unfold) "unfold" (" (" &"config" " := " term ")")?
  (ppSpace (colGt ident))* (ppSpace location)? : tactic
syntax (name := unfold1) "unfold1" (" (" &"config" " := " term ")")?
  (ppSpace (colGt ident))* (ppSpace location)? : tactic
syntax (name := inferOptParam) "inferOptParam" : tactic
syntax (name := inferAutoParam) "inferAutoParam" : tactic
syntax (name := guardExprEq) "guardExpr " term:51 " =ₐ " term : tactic -- alpha equality
syntax (name := guardTarget) "guardTarget" " =ₐ " term : tactic -- alpha equality

-- There is already a `byCases` tactic in core (in `src/init/classical.lean`)
-- so for now we add a primed version to support the optional identifier,
-- and available `decidable` instances.
syntax (name := byCases') "byCases' " atomic(ident " : ")? term : tactic

syntax (name := typeCheck) "typeCheck " term : tactic
syntax (name := rsimp) "rsimp" : tactic
syntax (name := compVal) "compVal" : tactic
syntax (name := async) "async " tacticSeq : tactic

namespace Conv

open Tactic (simpArg rwRuleSeq)
syntax (name := «for») "for " term:max " [" num,* "]" " => " tacticSeq : conv
syntax (name := dsimp) "dsimp" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? : conv
syntax (name := guardLHS) "guardLHS " " =ₐ " term : conv

end Conv

syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic
syntax (name := obtain) "obtain" (ppSpace rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

syntax (name := rintro?) "rintro?" (" : " num)? : tactic
syntax (name := rintro) "rintro" (ppSpace rintroPat)* (" : " term)? : tactic

syntax (name := ext1) "ext1" (ppSpace rcasesPat)* : tactic
syntax (name := ext1?) "ext1?" (ppSpace rcasesPat)* : tactic
-- The current implementation of `ext` in mathlib4 does not support `rcasesPat`,
-- and will need to be updated.
syntax (name := ext) "ext" (ppSpace rcasesPat)* (" : " num)? : tactic
syntax (name := ext?) "ext?" (ppSpace rcasesPat)* (" : " num)? : tactic

syntax (name := apply') "apply' " term : tactic
syntax (name := fapply') "fapply' " term : tactic
syntax (name := eapply') "eapply' " term : tactic
syntax (name := applyWith') "applyWith' " ("(" &"config" " := " term ")")? term : tactic
syntax (name := mapply') "mapply' " term : tactic
syntax (name := rfl') "rfl'" : tactic
syntax (name := symm') "symm'" (ppSpace location)? : tactic
syntax (name := trans') "trans'" (ppSpace term)? : tactic

syntax (name := fsplit) "fsplit" : tactic
syntax (name := injectionsAndClear) "injectionsAndClear" : tactic

syntax (name := fconstructor) "fconstructor" : tactic
syntax (name := tryFor) "tryFor " term:max tacticSeq : tactic
syntax (name := substs) "substs" (ppSpace ident)* : tactic
syntax (name := unfoldCoes) "unfoldCoes" (ppSpace location)? : tactic
syntax (name := unfoldWf) "unfoldWf" : tactic
syntax (name := unfoldAux) "unfoldAux" : tactic
syntax (name := recover) "recover" : tactic
syntax (name := «continue») "continue " tacticSeq : tactic
syntax (name := swap) "swap" (ppSpace num)? : tactic
syntax (name := rotate) "rotate" (ppSpace num)? : tactic
syntax (name := clear_) "clear_" : tactic
syntax (name := replace) "replace " Term.haveDecl : tactic
syntax (name := replace') "replace " Term.haveIdLhs : tactic
syntax (name := classical) "classical" : tactic
syntax (name := generalizeHyp) "generalize " atomic(ident " : ")? term:51 " = " ident
  ppSpace location : tactic
syntax (name := clean) "clean " term : tactic
syntax (name := refineStruct) "refineStruct " term : tactic
syntax (name := matchHyp) "matchHyp " ("(" &"m" " := " term ") ")? ident " : " term : tactic
syntax (name := guardHypNums) "guardHypNums " num : tactic
syntax (name := guardTags) "guardTags" (ppSpace ident)* : tactic
syntax (name := guardProofTerm) "guardProofTerm " tactic:51 " => " term : tactic
syntax (name := failIfSuccess?) "failIfSuccess? " str ppSpace tacticSeq : tactic
syntax (name := field) "field " ident " => " tacticSeq : tactic
syntax (name := haveField) "haveField" : tactic
syntax (name := applyField) "applyField" : tactic
syntax (name := applyRules) "applyRules" (" (" &"config" " := " term ")")?
  " [" term,* "]" (ppSpace num)? : tactic
syntax (name := hGeneralize) "hGeneralize " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := hGeneralize!) "hGeneralize! " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := guardExprEq') "guardExpr " term:51 " = " term : tactic -- definitional equality
syntax (name := guardTarget') "guardTarget" " = " term : tactic -- definitional equality
syntax (name := triv) "triv" : tactic
syntax (name := use) "use " term,+ : tactic
syntax (name := clearAuxDecl) "clearAuxDecl" : tactic
syntax (name := set) "set " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := set!) "set! " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := clearExcept) "clear " "*" " - " ident* : tactic
syntax (name := extractGoal) "extractGoal" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
syntax (name := extractGoal!) "extractGoal!" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic
syntax (name := revertDeps) "revertDeps" (ppSpace (colGt ident))* : tactic
syntax (name := revertAfter) "revertAfter " ident : tactic
syntax (name := revertTargetDeps) "revertTargetDeps" : tactic
syntax (name := clearValue) "clearValue" (ppSpace (colGt ident))* : tactic

syntax (name := applyAssumption) "applyAssumption" : tactic

syntax (name := hint) "hint" : tactic

syntax (name := clear!) "clear!" (ppSpace ident)* : tactic

syntax (name := choose) "choose" (ppSpace ident)+ (" using " term)? : tactic
syntax (name := choose!) "choose!" (ppSpace ident)+ (" using " term)? : tactic

syntax (name := congr) "congr" (ppSpace (colGt num))?
  (" with " (colGt rcasesPat)* (" : " num)?)? : tactic
syntax (name := rcongr) "rcongr" (ppSpace (colGt rcasesPat))* : tactic
syntax (name := convert) "convert " "← "? term (" using " num)? : tactic
syntax (name := convertTo) "convertTo " term (" using " num)? : tactic
syntax (name := acChange) "acChange " term (" using " num)? : tactic

syntax (name := decide!) "decide!" : tactic

syntax (name := deltaInstance) "deltaInstance" (ppSpace ident)* : tactic

syntax (name := elide) "elide " num (ppSpace location)? : tactic
syntax (name := unelide) "unelide" (ppSpace location)? : tactic

syntax (name := clarify) "clarify" (" (" &"config" " := " term ")")?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := safe) "safe" (" (" &"config" " := " term ")")?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := finish) "finish" (" (" &"config" " := " term ")")?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic

syntax generalizesArg := (ident " : ")? term:51 " = " ident
syntax (name := generalizes) "generalizes " "[" generalizesArg,* "]" : tactic

syntax (name := generalizeProofs) "generalizeProofs"
  (ppSpace (colGt binderIdent))* (ppSpace location)? : tactic

syntax (name := itauto) "itauto" : tactic

syntax (name := lift) "lift " term " to " term
  (" using " term)? (" with " binderIdent+)? : tactic

syntax (name := pushCast) "pushCast"
  (" [" Parser.Tactic.simpArg,* "]")? (ppSpace location)? : tactic
syntax (name := normCast) "normCast" (ppSpace location)? : tactic
syntax (name := rwModCast) "rwModCast " rwRuleSeq (ppSpace location)? : tactic
syntax (name := exactModCast) "exactModCast " term : tactic
syntax (name := applyModCast) "applyModCast " term : tactic
syntax (name := assumptionModCast) "assumptionModCast" : tactic

syntax (name := obviously) "obviously" : tactic

syntax (name := prettyCases) "prettyCases" : tactic

syntax (name := pushNeg) "pushNeg" (ppSpace location)? : tactic

syntax (name := contrapose) "contrapose" (ppSpace ident (" with " ident)?)? : tactic
syntax (name := contrapose!) "contrapose!" (ppSpace ident (" with " ident)?)? : tactic

syntax (name := renameVar) "renameVar " ident " → " ident (ppSpace location)? : tactic

syntax (name := assocRw) "assocRw " rwRuleSeq (ppSpace location)? : tactic

syntax (name := simpRw) "simpRw " rwRuleSeq (ppSpace location)? : tactic

syntax (name := dsimpResult) "dsimpResult " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic
syntax (name := simpResult) "simpResult " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic

syntax (name := simpa) "simpa" (" (" &"config" " := " term ")")? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa!) "simpa!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa?) "simpa?" (" (" &"config" " := " term ")")? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa!?) "simpa!?" (" (" &"config" " := " term ")")? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic

syntax (name := splitIfs) "splitIfs" (ppSpace location)? (" with " binderIdent+)? : tactic

syntax (name := squeezeScope) "squeezeScope " tacticSeq : tactic
syntax (name := squeezeSimp) "squeezeSimp" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeSimp?) "squeezeSimp?" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeSimp!) "squeezeSimp!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeSimp?!) "squeezeSimp?!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeSimpa) "squeezeSimpa" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa?) "squeezeSimpa?" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa!) "squeezeSimpa!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa?!) "squeezeSimpa?!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeDSimp) "squeezeDSimp" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeDSimp?) "squeezeDSimp?" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeDSimp!) "squeezeDSimp!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := squeezeDSimp?!) "squeezeDSimp?!" (" (" &"config" " := " term ")")? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic

syntax (name := suggest) "suggest" (" (" &"config" " := " term ")")? (ppSpace num)?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " (colGt ident)+)? : tactic
syntax (name := librarySearch!) "librarySearch!" (" (" &"config" " := " term ")")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " (colGt ident)+)? : tactic

syntax (name := tauto) "tauto" (" (" &"config" " := " term ")")? : tactic
syntax (name := tauto!) "tauto!" (" (" &"config" " := " term ")")? : tactic

syntax (name := truncCases) "truncCases " term (" with " (colGt binderIdent)+)? : tactic

syntax (name := normNum1) "normNum1" (ppSpace location)? : tactic
syntax (name := applyNormed) "applyNormed " term : tactic

syntax (name := abel1) "abel1" : tactic
syntax (name := abel) "abel" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic
syntax (name := abel!) "abel!" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic

syntax (name := ring1) "ring1" : tactic
syntax (name := ring1!) "ring1!" : tactic

syntax ringMode := &"SOP" <|> &"raw" <|> &"horner"
syntax (name := ringNF) "ringNF" (ppSpace ringMode)? (ppSpace location)? : tactic
syntax (name := ringNF!) "ringNF!" (ppSpace ringMode)? (ppSpace location)? : tactic
syntax (name := ring!) "ring!" : tactic

syntax (name := ringExpEq) "ringExpEq" : tactic
syntax (name := ringExpEq!) "ringExpEq!" : tactic
syntax (name := ringExp) "ringExp" (ppSpace location)? : tactic
syntax (name := ringExp!) "ringExp!" (ppSpace location)? : tactic

syntax (name := noncommRing) "noncommRing" : tactic

syntax (name := linarith) "linarith" (" (" &"config" " := " term ")")?
  (&" only")? (" [" term,* "]")? : tactic
syntax (name := linarith!) "linarith!" (" (" &"config" " := " term ")")?
  (&" only")? (" [" term,* "]")? : tactic
syntax (name := nlinarith) "nlinarith" (" (" &"config" " := " term ")")?
  (&" only")? (" [" term,* "]")? : tactic
syntax (name := nlinarith!) "nlinarith!" (" (" &"config" " := " term ")")?
  (&" only")? (" [" term,* "]")? : tactic

syntax (name := omega) "omega" (&" manual")? (&" nat" <|> &" int")? : tactic

syntax (name := tfaeHave) "tfaeHave " (ident " : ")? num (" → " <|> " ↔ " <|> " ← ") num : tactic
syntax (name := tfaeFinish) "tfaeFinish" : tactic

syntax mono.side := &"left" <|> &"right" <|> &"both"
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

syntax (name := acMono) "acMono" ("*" <|> ("^" num))?
  (" (" &"config" " := " term ")")? ((" : " term) <|> (" := " term))? : tactic

syntax (name := applyFun) "applyFun " term (ppSpace location)? (" using " term)? : tactic

syntax (name := finCases) "finCases " ("*" <|> (term,+)) (" with " term)? : tactic

syntax (name := intervalCases) "intervalCases" (ppSpace (colGt term))?
  (" using " term ", " term)? (" with " ident)? : tactic

syntax (name := reassoc) "reassoc" (ppSpace (colGt ident))* : tactic
syntax (name := reassoc!) "reassoc!" (ppSpace (colGt ident))* : tactic
syntax (name := deriveReassocProof) "deriveReassocProof" : tactic

syntax (name := sliceLHS) "sliceLHS " num num " => " Conv.convSeq : tactic
syntax (name := sliceRHS) "sliceRHS " num num " => " Conv.convSeq : tactic

syntax (name := subtypeInstance) "subtypeInstance" : tactic

syntax (name := group) "group" (ppSpace location)? : tactic

syntax (name := cancelDenoms) "cancelDenoms" (ppSpace location)? : tactic

syntax (name := zify) "zify" (" [" simpArg,* "]")? (ppSpace location)? : tactic

syntax (name := transport) "transport" (ppSpace term)? " using " term : tactic

syntax (name := unfoldCases) "unfoldCases " tacticSeq : tactic

syntax (name := fieldSimp) "fieldSimp" (" (" &"config" " := " term ")")? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic

syntax (name := equivRw) "equivRw " ("(" &"config" " := " term ") ")?
  term (ppSpace location)? : tactic
syntax (name := equivRwType) "equivRwType " ("(" &"config" " := " term ") ")? term : tactic

syntax (name := nthRw) "nthRw " num rwRuleSeq (ppSpace location)? : tactic
syntax (name := nthRwLHS) "nthRwLHS " num rwRuleSeq (ppSpace location)? : tactic
syntax (name := nthRwRHS) "nthRwRHS " num rwRuleSeq (ppSpace location)? : tactic

syntax (name := rwSearch) "rwSearch " ("(" &"config" " := " term ") ")? rwRuleSeq : tactic
syntax (name := rwSearch?) "rwSearch? " ("(" &"config" " := " term ") ")? rwRuleSeq : tactic

syntax (name := piInstanceDeriveField) "piInstanceDeriveField" : tactic
syntax (name := piInstance) "piInstance" : tactic

syntax (name := tidy) "tidy" (" (" &"config" " := " term ")")? : tactic
syntax (name := tidy?) "tidy?" (" (" &"config" " := " term ")")? : tactic

syntax (name := wlog) "wlog" (" (" &"discharger" " := " term ")")?
  (ppSpace (colGt ident))? (" : " term)? (" := " term)? (" using " (ident*),+)? : tactic

syntax (name := elementwise) "elementwise" (ppSpace (colGt ident))* : tactic
syntax (name := elementwise!) "elementwise!" (ppSpace (colGt ident))* : tactic
syntax (name := deriveElementwiseProof) "deriveElementwiseProof" : tactic

syntax (name := mkDecorations) "mkDecorations" : tactic

syntax (name := nontriviality) "nontriviality"
  (ppSpace (colGt term))? (" using " simpArg,+)? : tactic

syntax (name := filterUpwards) "filterUpwards" " [" term,* "]" (ppSpace (colGt term))? : tactic

syntax (name := isBounded_default) "isBounded_default" : tactic

syntax (name := opInduction) "opInduction" (ppSpace (colGt term))? : tactic

syntax (name := mvBisim) "mvBisim" (ppSpace (colGt term))? (" with " binderIdent+)? : tactic

syntax (name := continuity) "continuity" (" (" &"config" " := " term ")")? : tactic
syntax (name := continuity!) "continuity!" (" (" &"config" " := " term ")")? : tactic
syntax (name := continuity?) "continuity?" (" (" &"config" " := " term ")")? : tactic
syntax (name := continuity!?) "continuity!?" (" (" &"config" " := " term ")")? : tactic

syntax (name := unitInterval) "unitInterval" : tactic
syntax (name := mfldSetTac) "mfldSetTac" : tactic

syntax (name := measurability) "measurability" (" (" &"config" " := " term ")")? : tactic
syntax (name := measurability!) "measurability!" (" (" &"config" " := " term ")")? : tactic
syntax (name := measurability?) "measurability?" (" (" &"config" " := " term ")")? : tactic
syntax (name := measurability!?) "measurability!?" (" (" &"config" " := " term ")")? : tactic
syntax (name := padicIndexSimp) "padicIndexSimp" " [" term,* "]" (ppSpace location)? : tactic

syntax (name := uniqueDiffWithinAt_Ici_Iic_univ) "uniqueDiffWithinAt_Ici_Iic_univ" : tactic

syntax (name := ghostFunTac) "ghostFunTac " term ", " term : tactic
syntax (name := ghostCalc) "ghostCalc" (ppSpace binderIdent)* : tactic
syntax (name := initRing) "initRing" (" using " term)? : tactic
syntax (name := ghostSimp) "ghostSimp" (" [" simpArg,* "]")? : tactic
syntax (name := wittTruncateFunTac) "wittTruncateFunTac" : tactic

namespace Conv

syntax (name := applyCongr) "applyCongr" (ppSpace (colGt term))? : conv
syntax (name := guardTarget) "guardTarget" " =ₐ " term : conv

syntax (name := normCast) "normCast" : conv

syntax (name := normNum1) "normNum1" : conv
syntax (name := normNum) "normNum" (" [" simpArg,* "]")? : conv

syntax (name := ringNF) "ringNF" (ppSpace ringMode)? : conv
syntax (name := ringNF!) "ringNF!" (ppSpace ringMode)? : conv
syntax (name := ring) "ring" : conv
syntax (name := ring!) "ring!" : conv

syntax (name := ringExp) "ringExp" : conv
syntax (name := ringExp!) "ringExp!" : conv

syntax (name := slice) "slice " num num : conv

end Conv
end Tactic

namespace Attr

syntax (name := intro) "intro" : attr
syntax (name := intro!) "intro!" : attr

syntax (name := ext) "ext" (ppSpace ident)? : attr

syntax (name := higherOrder) "higherOrder" (ppSpace ident)? : attr
syntax (name := interactive) "interactive" : attr

syntax (name := mkIff) "mkIff" (ppSpace ident)? : attr

syntax (name := normCast) "normCast" (ppSpace (&"elim" <|> &"move" <|> &"squash"))? : attr

syntax (name := protectProj) "protectProj" (&" without" (ppSpace ident)+)? : attr

syntax (name := notationClass) "notationClass" "*"? (ppSpace ident)? : attr

syntax (name := mono) "mono" (ppSpace Tactic.mono.side)? : attr

syntax (name := reassoc) "reassoc" (ppSpace ident)? : attr

syntax (name := ancestor) "ancestor" (ppSpace ident)* : attr

syntax (name := elementwise) "elementwise" (ppSpace ident)? : attr

end Attr

namespace Command

syntax (name := copyDocString) "copy_doc_string " ident " → " ident* : command
syntax (name := libraryNote) docComment "library_note " str : command
syntax (name := addTacticDoc) (docComment)? "add_tactic_doc " term : command
syntax (name := addDeclDoc) docComment "add_decl_doc " ident : command

syntax (name := setupTacticParser) "setup_tactic_parser" : command
syntax (name := mkSimpAttribute) "mk_simp_attribute " ident
  (" from" (ppSpace ident)+)? (" := " str)? : command

syntax (name := addHintTactic) "add_hint_tactic " tactic : command
syntax (name := alias) "alias " ident " ← " ident* : command
syntax (name := aliasLR) "alias " ident " ↔ " (".." <|> (binderIdent binderIdent)) : command

syntax (name := explode) "#explode " ident : command

syntax (name := open_locale) "open_locale" (ppSpace ident)* : command
syntax (name := localized) "localized " "[" ident "] " command : command

syntax (name := listUnusedDecls) "#list_unused_decls" : command
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop" ident ident : command

syntax (name := defReplacer) "def_replacer " ident Term.optType : command

syntax (name := restateAxiom) "restate_axiom " ident (ppSpace ident)? : command

syntax (name := simp) "#simp" (&" only")? (" [" Tactic.simpArg,* "]")?
  (" with " ident+)? " :"? ppSpace term : command

syntax (name := «where») "#where" : command

syntax (name := reassoc_axiom) "reassoc_axiom " ident : command

syntax (name := sample) "#sample " term : command

end Command
