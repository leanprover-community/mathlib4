/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Elab.Quotation
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Core
import Mathlib.Tactic.CommandQuote
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.RCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ShowTerm
import Mathlib.Tactic.Simps
import Mathlib.Tactic.SolveByElim
import Mathlib.Init.ExtendedBinder
import Mathlib.Util.WithWeakNamespace

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Lean

namespace Parser.Command
open Mathlib.ExtendedBinder

elab (name := include) "include " ident+ : command => pure ()
elab (name := omit) "omit " ident+ : command => pure ()
syntax (name := parameter) "parameter " bracketedBinder+ : command

/--
Expands binders into nested combinators.
For example, the familiar exists is given by:
`expandBinders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expandBinders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expandBinders% ($x => $term) $y:extBinder, $res) =>
    `(expandBinders% ($x => $term) ($y:extBinder), $res)
  | `(expandBinders% ($x => $term), $res) => pure res
macro_rules
  | `(expandBinders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident : $ty => expandBinders% ($x => $term) $[$binders]*, $res)
macro_rules
  | `(expandBinders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident => expandBinders% ($x => $term) (h : satisfiesBinderPred% $y $pred) $[$binders]*, $res)

macro (name := expandFoldl) "expandFoldl% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg => do
    term.replaceM fun e =>
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expandFoldr% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res => do
    term.replaceM fun e =>
      return if e == x then some arg else if e == y then some res else none

syntax bindersItem := atomic("(" "..." ")")
syntax foldRep := (strLit "*") <|> ",*"
syntax foldAction := "(" ident foldRep " => "
  (&"foldl" <|> &"foldr") " (" ident ident " => " term ") " term ")"
syntax identScope := ":" "(" "scoped " ident " => " term ")"
syntax notation3Item := strLit <|> bindersItem <|> (ident (identScope)?) <|> foldAction
macro ak:Term.attrKind "notation3"
    prec:optPrecedence name:optNamedName prio:optNamedPrio
    lits:((ppSpace notation3Item)+) " => " val:term : command => do
  let mut boundNames : Std.HashMap Name Syntax := {}
  let mut macroArgs := #[]
  for item in lits.getArgs do
    let lit := item[0]
    if let some _ := lit.isStrLit? then
      macroArgs := macroArgs.push (← `(macroArg| $lit:strLit))
    else if lit.isOfKind ``bindersItem then
      macroArgs := macroArgs.push (← `(macroArg| binders:extBinders))
    else if lit.isOfKind ``foldAction then
      let mut sep := lit[2][0]
      if sep.isAtom then sep := Syntax.mkStrLit ", "
      macroArgs := macroArgs.push (← `(macroArg| $(lit[1]):ident:sepBy(term, $sep:strLit)))
      let scopedTerm ← lit[9].replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let init ← lit[11].replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let id := lit[1]
      let args := Elab.Command.expandMacroArg.mkSplicePat
        `sepBy (← `(Syntax.SepArray.ofElems ($id:ident).getElems)) ",*"
      let args := #[
        Lean.mkAtom "(", lit[6], lit[7], Lean.mkAtom "=>", scopedTerm, Lean.mkAtom ")", init,
        Lean.mkAtom "[", args, Lean.mkAtom "]"]
      let stx ← match lit[4] with
        | Lean.Syntax.atom _ "foldl" =>
          pure $ mkNode ``expandFoldl (#[Lean.mkAtom "expandFoldl%"] ++ args)
        | Lean.Syntax.atom _ "foldr" =>
          pure $ mkNode ``expandFoldr (#[Lean.mkAtom "expandFoldr%"] ++ args)
        | _ => throw Lean.Macro.Exception.unsupportedSyntax
      boundNames := boundNames.insert id.getId stx
    else if let Syntax.ident _ _ id .. := lit then
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      if item[1].getNumArgs == 1 then
        let scopedId := item[1][0][3]
        let scopedTerm := item[1][0][5]
        let scopedTerm ← scopedTerm.replaceM fun
          | Syntax.ident _ _ id .. => pure $ boundNames.find? id
          | _ => pure none
        boundNames := boundNames.insert id <|
          ← `(expandBinders% ($scopedId:ident => $scopedTerm:term) $$binders:extBinders,
            $(lit.mkAntiquotNode))
      else
        boundNames := boundNames.insert id <| lit.mkAntiquotNode
  let val ← val.replaceM fun
    | Syntax.ident _ _ id .. => pure $ boundNames.find? id
    | _ => pure none
  `($ak:attrKind macro $[$(prec.getOptional?):precedence]? $[$(name.getOptional?):namedName]?
      $[$(prio.getOptional?):namedPrio]? $[$macroArgs:macroArg]* : term => do
    `($val:term))

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

syntax (name := propagateTags) "propagate_tags " tacticSeq : tactic
syntax (name := fapply) "fapply " term : tactic
syntax (name := eapply) "eapply " term : tactic
syntax (name := applyWith) "apply " term " with " term : tactic
syntax (name := mapply) "mapply " term : tactic
syntax (name := toExpr') "to_expr' " term : tactic
syntax (name := withCases) "with_cases " tacticSeq : tactic
syntax caseArg := binderIdent,+ (" :" (ppSpace (ident <|> "_"))+)?
syntax (name := case') "case' " (("[" caseArg,* "]") <|> caseArg) " => " tacticSeq : tactic
syntax "destruct " term : tactic
syntax (name := casesM) "casesm" "*"? ppSpace term,* : tactic
syntax (name := casesType) "cases_type" "*"? ppSpace ident* : tactic
syntax (name := casesType!) "cases_type!" "*"? ppSpace ident* : tactic
syntax (name := abstract) "abstract" (ppSpace ident)? ppSpace tacticSeq : tactic

syntax (name := trace) "trace " term : tactic
syntax (name := existsi) "exists " term,* : tactic
syntax (name := eConstructor) "econstructor" : tactic
syntax (name := left) "left" : tactic
syntax (name := right) "right" : tactic
syntax (name := constructorM) "constructorm" "*"? ppSpace term,* : tactic
syntax (name := injections') "injections" (" with " (colGt (ident <|> "_"))+)? : tactic
syntax (name := simp') "simp'" "*"? (config)? (discharger)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := simpIntro) "simp_intro" (config)?
  (ppSpace (colGt (ident <|> "_")))* (&" only")? (" [" simpArg,* "]")? (" with " ident+)? : tactic
syntax (name := dsimp) "dsimp" (config)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic
syntax (name := symm) "symm" : tactic
syntax (name := trans) "trans" (ppSpace (colGt term))? : tactic
syntax (name := acRfl) "ac_rfl" : tactic
syntax (name := cc) "cc" : tactic
syntax (name := substVars) "subst_vars" : tactic

-- builtin unfold only accepts single ident
syntax (name := unfold') (priority := low) "unfold" (config)? (ppSpace (colGt ident))* (ppSpace location)? : tactic
syntax (name := dUnfold) "dunfold" (config)? (ppSpace (colGt ident))* (ppSpace location)? : tactic
syntax (name := delta') "delta'" (colGt ident)* (ppSpace location)? : tactic
syntax (name := unfoldProjs) "unfold_projs" (config)? (ppSpace location)? : tactic
syntax (name := unfold1) "unfold1" (config)? (ppSpace (colGt ident))* (ppSpace location)? : tactic

syntax (name := inferOptParam) "infer_opt_param" : tactic
syntax (name := inferAutoParam) "infer_auto_param" : tactic
syntax (name := guardExprEq) "guard_expr " term:51 " =ₐ " term : tactic -- alpha equality
syntax (name := guardTarget) "guard_target" " =ₐ " term : tactic -- alpha equality

-- There is already a `by_cases` tactic in core (in `src/init/classical.lean`)
-- so for now we add a primed version to support the optional identifier,
-- and available `decidable` instances.
syntax (name := byCases') "by_cases' " atomic(ident " : ")? term : tactic

syntax (name := typeCheck) "type_check " term : tactic
syntax (name := rsimp) "rsimp" : tactic
syntax (name := compVal) "comp_val" : tactic
syntax (name := async) "async " tacticSeq : tactic

namespace Conv

open Tactic (simpArg rwRuleSeq)
syntax (name := «for») "for " term:max " [" num,* "]" " => " tacticSeq : conv
syntax (name := simp') "simp'" (config)? (discharger)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? : conv
syntax (name := dsimp) "dsimp" (config)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? : conv
syntax (name := guardLHS) "guard_lhs " " =ₐ " term : conv

end Conv

syntax (name := apply') "apply' " term : tactic
syntax (name := fapply') "fapply' " term : tactic
syntax (name := eapply') "eapply' " term : tactic
syntax (name := applyWith') "apply_with' " (config)? term : tactic
syntax (name := mapply') "mapply' " term : tactic
syntax (name := rfl') "rfl'" : tactic
syntax (name := symm') "symm'" (ppSpace location)? : tactic
syntax (name := trans') "trans'" (ppSpace term)? : tactic

syntax (name := fsplit) "fsplit" : tactic
syntax (name := injectionsAndClear) "injections_and_clear" : tactic

syntax (name := fconstructor) "fconstructor" : tactic
syntax (name := tryFor) "try_for " term:max tacticSeq : tactic
syntax (name := substs) "substs" (ppSpace ident)* : tactic
syntax (name := unfoldCoes) "unfold_coes" (ppSpace location)? : tactic
syntax (name := unfoldWf) "unfold_wf" : tactic
syntax (name := unfoldAux) "unfold_aux" : tactic
syntax (name := recover) "recover" : tactic
syntax (name := «continue») "continue " tacticSeq : tactic
syntax (name := clear_) "clear_" : tactic
syntax (name := replace') "replace " Term.haveIdLhs : tactic
syntax (name := generalizeHyp) "generalize " atomic(ident " : ")? term:51 " = " ident
  ppSpace location : tactic
syntax (name := clean) "clean " term : tactic
syntax (name := refineStruct) "refine_struct " term : tactic
syntax (name := matchHyp) "match_hyp " ("(" &"m" " := " term ") ")? ident " : " term : tactic
syntax (name := guardHypNums) "guard_hyp_nums " num : tactic
syntax (name := guardTags) "guard_tags" (ppSpace ident)* : tactic
syntax (name := guardProofTerm) "guard_proof_term " tactic:51 " => " term : tactic
syntax (name := failIfSuccess?) "fail_if_success? " str ppSpace tacticSeq : tactic
syntax (name := field) "field " ident " => " tacticSeq : tactic
syntax (name := haveField) "have_field" : tactic
syntax (name := applyField) "apply_field" : tactic
syntax (name := applyRules) "apply_rules" (config)? " [" term,* "]" (ppSpace num)? : tactic
syntax (name := hGeneralize) "h_generalize " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := hGeneralize!) "h_generalize! " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := guardExprEq') "guard_expr " term:51 " = " term : tactic -- definitional equality
syntax (name := guardTarget') "guard_target" " = " term : tactic -- definitional equality
syntax (name := triv) "triv" : tactic
syntax (name := clearAuxDecl) "clear_aux_decl" : tactic
syntax (name := set) "set " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := set!) "set! " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := clearExcept) "clear " "*" " - " ident* : tactic
syntax (name := extractGoal) "extract_goal" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
syntax (name := extractGoal!) "extract_goal!" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic
syntax (name := revertDeps) "revert_deps" (ppSpace (colGt ident))* : tactic
syntax (name := revertAfter) "revert_after " ident : tactic
syntax (name := revertTargetDeps) "revert_target_deps" : tactic
syntax (name := clearValue) "clear_value" (ppSpace (colGt ident))* : tactic

syntax (name := applyAssumption) "apply_assumption" : tactic

syntax (name := hint) "hint" : tactic

syntax (name := clear!) "clear!" (ppSpace ident)* : tactic

syntax (name := choose) "choose" (ppSpace ident)+ (" using " term)? : tactic
syntax (name := choose!) "choose!" (ppSpace ident)+ (" using " term)? : tactic

syntax (name := congr) "congr" (ppSpace (colGt num))?
  (" with " (colGt rcasesPat)* (" : " num)?)? : tactic
syntax (name := rcongr) "rcongr" (ppSpace (colGt rcasesPat))* : tactic
syntax (name := convert) "convert " "← "? term (" using " num)? : tactic
syntax (name := convertTo) "convert_to " term (" using " num)? : tactic
syntax (name := acChange) "ac_change " term (" using " num)? : tactic

syntax (name := decide!) "decide!" : tactic

syntax (name := deltaInstance) "delta_instance" (ppSpace ident)* : tactic

syntax (name := elide) "elide " num (ppSpace location)? : tactic
syntax (name := unelide) "unelide" (ppSpace location)? : tactic

syntax (name := clarify) "clarify" (config)?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := safe) "safe" (config)?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := finish) "finish" (config)?
  (" [" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic

syntax generalizesArg := (ident " : ")? term:51 " = " ident
syntax (name := generalizes) "generalizes " "[" generalizesArg,* "]" : tactic

syntax (name := generalizeProofs) "generalize_proofs"
  (ppSpace (colGt binderIdent))* (ppSpace location)? : tactic

syntax withPattern := "-" <|> "_" <|> ident
syntax (name := cases'') "cases''" casesTarget (" with " (colGt withPattern)+)? : tactic
syntax fixingClause := " fixing" (" *" <|> (ppSpace ident)+)
syntax generalizingClause := " generalizing" (ppSpace ident)+
syntax (name := induction'') "induction''" casesTarget
  (fixingClause <|> generalizingClause)? (" with " (colGt withPattern)+)? : tactic

syntax termList := " [" term,* "]"
syntax (name := itauto) "itauto" (" *" <|> termList)? : tactic
syntax (name := itauto!) "itauto!" (" *" <|> termList)? : tactic

syntax (name := lift) "lift " term " to " term
  (" using " term)? (" with " binderIdent+)? : tactic

syntax (name := obviously) "obviously" : tactic

syntax (name := prettyCases) "pretty_cases" : tactic

syntax (name := pushNeg) "push_neg" (ppSpace location)? : tactic

syntax (name := contrapose) "contrapose" (ppSpace ident (" with " ident)?)? : tactic
syntax (name := contrapose!) "contrapose!" (ppSpace ident (" with " ident)?)? : tactic

syntax (name := byContra') "by_contra'" (ppSpace ident)? Term.optType : tactic

syntax (name := renameVar) "rename_var " ident " → " ident (ppSpace location)? : tactic

syntax swapVarArg := ident " ↔ "? ident
syntax (name := swapVar) "swap_var " (colGt swapVarArg),+ : tactic

syntax (name := assocRw) "assoc_rw " rwRuleSeq (ppSpace location)? : tactic

syntax (name := dsimpResult) "dsimp_result " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic
syntax (name := simpResult) "simp_result " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic

syntax (name := splitIfs) "split_ifs" (ppSpace location)? (" with " binderIdent+)? : tactic

syntax (name := squeezeScope) "squeeze_scope " tacticSeq : tactic

syntax squeezeSimpArgsRest := (config)? (discharger)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)?
syntax "squeeze_simp" "!"? "?"? squeezeSimpArgsRest : tactic
macro "squeeze_simp?" rest:squeezeSimpArgsRest : tactic =>
  `(tactic| squeeze_simp ? $rest:squeezeSimpArgsRest)
macro "squeeze_simp!" rest:squeezeSimpArgsRest : tactic =>
  `(tactic| squeeze_simp ! $rest:squeezeSimpArgsRest)
macro "squeeze_simp!?" rest:squeezeSimpArgsRest : tactic =>
  `(tactic| squeeze_simp !? $rest:squeezeSimpArgsRest)

syntax squeezeDSimpArgsRest := (config)? (&" only")?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)?
syntax "squeeze_dsimp" "!"? "?"? squeezeDSimpArgsRest : tactic
macro "squeeze_dsimp?" rest:squeezeDSimpArgsRest : tactic =>
  `(tactic| squeeze_dsimp ? $rest:squeezeDSimpArgsRest)
macro "squeeze_dsimp!" rest:squeezeDSimpArgsRest : tactic =>
  `(tactic| squeeze_dsimp ! $rest:squeezeDSimpArgsRest)
macro "squeeze_dsimp!?" rest:squeezeDSimpArgsRest : tactic =>
  `(tactic| squeeze_dsimp !? $rest:squeezeDSimpArgsRest)

syntax (name := suggest) "suggest" (config)? (ppSpace num)?
  (" [" simpArg,* "]")? (" with " (colGt ident)+)? (" using " (colGt binderIdent)+)? : tactic

syntax (name := tauto) "tauto" (config)? : tactic
syntax (name := tauto!) "tauto!" (config)? : tactic

syntax (name := truncCases) "trunc_cases " term (" with " (colGt binderIdent)+)? : tactic

syntax (name := normNum1) "norm_num1" (ppSpace location)? : tactic
syntax (name := applyNormed) "apply_normed " term : tactic

syntax (name := abel1) "abel1" : tactic
syntax (name := abel1!) "abel1!" : tactic
syntax (name := abel) "abel" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic
syntax (name := abel!) "abel!" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic

syntax (name := ring1) "ring1" : tactic
syntax (name := ring1!) "ring1!" : tactic

syntax ringMode := &"SOP" <|> &"raw" <|> &"horner"
syntax (name := ringNF) "ring_nf" (ppSpace ringMode)? (ppSpace location)? : tactic
syntax (name := ringNF!) "ring_nf!" (ppSpace ringMode)? (ppSpace location)? : tactic
syntax (name := ring!) "ring!" : tactic

syntax (name := ringExpEq) "ring_exp_eq" : tactic
syntax (name := ringExpEq!) "ring_exp_eq!" : tactic
syntax (name := ringExp) "ring_exp" (ppSpace location)? : tactic
syntax (name := ringExp!) "ring_exp!" (ppSpace location)? : tactic

syntax (name := noncommRing) "noncomm_ring" : tactic

syntax nameAndTerm := term:71 " * " term:66
syntax (name := linearCombination) "linear_combination" (config)?
  sepBy(atomic(nameAndTerm) <|> term:66, " + ") : tactic

syntax (name := linarith) "linarith" (config)? (&" only")? (" [" term,* "]")? : tactic
syntax (name := linarith!) "linarith!" (config)? (&" only")? (" [" term,* "]")? : tactic
syntax (name := nlinarith) "nlinarith" (config)? (&" only")? (" [" term,* "]")? : tactic
syntax (name := nlinarith!) "nlinarith!" (config)? (&" only")? (" [" term,* "]")? : tactic

syntax (name := omega) "omega" (&" manual")? (&" nat" <|> &" int")? : tactic

syntax (name := tfaeHave) "tfae_have " (ident " : ")? num (" → " <|> " ↔ " <|> " ← ") num : tactic
syntax (name := tfaeFinish) "tfae_finish" : tactic

syntax mono.side := &"left" <|> &"right" <|> &"both"
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

syntax (name := acMono) "ac_mono" ("*" <|> ("^" num))?
  (config)? ((" : " term) <|> (" := " term))? : tactic

syntax (name := applyFun) "apply_fun " term (ppSpace location)? (" using " term)? : tactic

syntax (name := finCases) "fin_cases " ("*" <|> (term,+)) (" with " term)? : tactic

syntax (name := intervalCases) "interval_cases" (ppSpace (colGt term))?
  (" using " term ", " term)? (" with " ident)? : tactic

syntax (name := reassoc) "reassoc" (ppSpace (colGt ident))* : tactic
syntax (name := reassoc!) "reassoc!" (ppSpace (colGt ident))* : tactic
syntax (name := deriveReassocProof) "derive_reassoc_proof" : tactic

syntax (name := sliceLHS) "slice_lhs " num num " => " Conv.convSeq : tactic
syntax (name := sliceRHS) "slice_rhs " num num " => " Conv.convSeq : tactic

syntax (name := subtypeInstance) "subtype_instance" : tactic

syntax (name := group) "group" (ppSpace location)? : tactic

syntax (name := cancelDenoms) "cancel_denoms" (ppSpace location)? : tactic

syntax (name := zify) "zify" (" [" simpArg,* "]")? (ppSpace location)? : tactic

syntax (name := transport) "transport" (ppSpace term)? " using " term : tactic

syntax (name := unfoldCases) "unfold_cases " tacticSeq : tactic

syntax (name := fieldSimp) "field_simp" (config)? (discharger)? (&" only")?
  (" [" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (ppSpace location)? : tactic

syntax (name := equivRw) "equiv_rw" (config)? (termList <|> term) (ppSpace location)? : tactic
syntax (name := equivRwType) "equiv_rw_type" (config)? term : tactic

syntax (name := nthRw) "nth_rw " num rwRuleSeq (ppSpace location)? : tactic
syntax (name := nthRwLHS) "nth_rw_lhs " num rwRuleSeq (ppSpace location)? : tactic
syntax (name := nthRwRHS) "nth_rw_rhs " num rwRuleSeq (ppSpace location)? : tactic

syntax (name := rwSearch) "rw_search " (config)? rwRuleSeq : tactic
syntax (name := rwSearch?) "rw_search? " (config)? rwRuleSeq : tactic

syntax (name := piInstanceDeriveField) "pi_instance_derive_field" : tactic
syntax (name := piInstance) "pi_instance" : tactic

syntax (name := tidy) "tidy" (config)? : tactic
syntax (name := tidy?) "tidy?" (config)? : tactic

syntax (name := wlog) "wlog" (" (" &"discharger" " := " term ")")?
  (ppSpace (colGt ident))? (" : " term)? (" := " term)? (" using " (ident*),+)? : tactic

syntax (name := elementwise) "elementwise" (ppSpace (colGt ident))* : tactic
syntax (name := elementwise!) "elementwise!" (ppSpace (colGt ident))* : tactic
syntax (name := deriveElementwiseProof) "derive_elementwise_proof" : tactic

syntax (name := mkDecorations) "mk_decorations" : tactic

syntax (name := nontriviality) "nontriviality"
  (ppSpace (colGt term))? (" using " simpArg,+)? : tactic

syntax (name := filterUpwards) "filter_upwards" (termList)?
  (" with" term:max*)? (" using" term)? : tactic

syntax (name := isBounded_default) "isBounded_default" : tactic

syntax (name := opInduction) "op_induction" (ppSpace (colGt term))? : tactic

syntax (name := mvBisim) "mv_bisim" (ppSpace (colGt term))? (" with " binderIdent+)? : tactic

syntax (name := continuity) "continuity" (config)? : tactic
syntax (name := continuity!) "continuity!" (config)? : tactic
syntax (name := continuity?) "continuity?" (config)? : tactic
syntax (name := continuity!?) "continuity!?" (config)? : tactic

syntax (name := unitInterval) "unit_interval" : tactic
syntax (name := mfldSetTac) "mfld_set_tac" : tactic

syntax (name := measurability) "measurability" (config)? : tactic
syntax (name := measurability!) "measurability!" (config)? : tactic
syntax (name := measurability?) "measurability?" (config)? : tactic
syntax (name := measurability!?) "measurability!?" (config)? : tactic
syntax (name := padicIndexSimp) "padic_index_simp" " [" term,* "]" (ppSpace location)? : tactic

syntax (name := uniqueDiffWithinAt_Ici_Iic_univ) "uniqueDiffWithinAt_Ici_Iic_univ" : tactic

syntax (name := ghostFunTac) "ghost_fun_tac " term ", " term : tactic
syntax (name := ghostCalc) "ghost_calc" (ppSpace binderIdent)* : tactic
syntax (name := initRing) "init_ring" (" using " term)? : tactic
syntax (name := ghostSimp) "ghost_simp" (" [" simpArg,* "]")? : tactic
syntax (name := wittTruncateFunTac) "witt_truncate_fun_tac" : tactic

namespace Conv

-- https://github.com/leanprover-community/mathlib/issues/2882
syntax (name := applyCongr) "apply_congr" (ppSpace (colGt term))? : conv

syntax (name := guardTarget) "guard_target" " =ₐ " term : conv

syntax (name := normNum1) "norm_num1" : conv
syntax (name := normNum) "norm_num" (" [" simpArg,* "]")? : conv

syntax (name := ringNF) "ring_nf" (ppSpace ringMode)? : conv
syntax (name := ringNF!) "ring_nf!" (ppSpace ringMode)? : conv
syntax (name := ring) "ring" : conv
syntax (name := ring!) "ring!" : conv

syntax (name := ringExp) "ring_exp" : conv
syntax (name := ringExp!) "ring_exp!" : conv

syntax (name := slice) "slice " num num : conv

end Conv
end Tactic

namespace Attr

syntax (name := intro) "intro" : attr
syntax (name := intro!) "intro!" : attr

syntax (name := ext) "ext" (ppSpace ident)? : attr

syntax (name := higherOrder) "higher_order" (ppSpace ident)? : attr
syntax (name := interactive) "interactive" : attr

syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

syntax (name := protectProj) "protect_proj" (&" without" (ppSpace ident)+)? : attr

syntax (name := notationClass) "notation_class" "*"? (ppSpace ident)? : attr

syntax (name := mono) "mono" (ppSpace Tactic.mono.side)? : attr

syntax (name := reassoc) "reassoc" (ppSpace ident)? : attr

syntax (name := ancestor) "ancestor" (ppSpace ident)* : attr

syntax (name := elementwise) "elementwise" (ppSpace ident)? : attr

syntax (name := toAdditiveIgnoreArgs) "to_additive_ignore_args" num* : attr
syntax (name := toAdditiveRelevantArg) "to_additive_relevant_arg" num : attr
syntax (name := toAdditiveReorder) "to_additive_reorder" num* : attr
syntax (name := toAdditive) "to_additive" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!) "to_additive!" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive?) "to_additive?" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!?) "to_additive!?" (ppSpace ident)? (ppSpace str)? : attr

end Attr

namespace Command

syntax (name := copyDocString) "copy_doc_string " ident " → " ident* : command
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
macro_rules | `(open_locale $ids:ident*) => `(command| open $[$ids:ident]*)

syntax (name := localized) "localized " "[" ident "] " command : command
-- The implementation completely ignores the namespace argument, let's just
-- hope that localized is only used the corresponding namespace. :shrug:
macro_rules
  | `(localized [$ns] notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]? $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(localized [$ns] $attrKind:attrKind $mixfixKind $prec:precedence $[$n:namedName]? $[$prio:namedPrio]? $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped $mixfixKind $prec:precedence $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(localized [$ns] attribute [$attr:attr] $ids*) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns attribute [scoped $attr:attr] $ids*)

syntax (name := listUnusedDecls) "#list_unused_decls" : command
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop" ident ident : command

syntax (name := defReplacer) "def_replacer " ident Term.optType : command

syntax (name := simp) "#simp" (&" only")? (" [" Tactic.simpArg,* "]")?
  (" with " ident+)? " :"? ppSpace term : command

syntax (name := «where») "#where" : command

syntax (name := reassoc_axiom) "reassoc_axiom " ident : command

syntax (name := sample) "#sample " term : command

end Command
