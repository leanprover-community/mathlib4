/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Lean.Expr
import Mathlib.Util.Syntax

/-!
# The notation3 macro, simulating Lean 3's notation.
-/

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Lean

namespace Parser.Command
open Std.ExtendedBinder

/--
Expands binders into nested combinators.
For example, the familiar exists is given by:
`expand_binders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expand_binders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expand_binders% ($x => $term) $y:extBinder, $res) =>
    `(expand_binders% ($x => $term) ($y:extBinder), $res)
  | `(expand_binders% ($_ => $_), $res) => pure res
macro_rules
  | `(expand_binders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident : $ty ↦ expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident ↦ expand_binders% ($x => $term) (h : satisfies_binder_pred% $y $pred)
        $[$binders]*, $res)

macro (name := expandFoldl) "expand_foldl% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg ↦ do
    term.replaceM fun e ↦
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expand_foldr% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res ↦ do
    term.replaceM fun e ↦
      return if e == x then some arg else if e == y then some res else none

/-- Keywording indicating whether to use a left- or right-fold. -/
syntax foldKind := &"foldl" <|> &"foldr"
/-- `notation3` argument matching `extBinders`. -/
syntax bindersItem := atomic("(" "..." ")")
/-- `notation3` argument simulating a Lean 3 fold notation. -/
syntax foldAction := "(" ident ppSpace strLit "*" " => " foldKind
  " (" ident ppSpace ident " => " term ") " term ")"
/-- `notation3` argument binding a name. -/
syntax identOptScoped := ident (":" "(" "scoped " ident " => " term ")")?
/-- `notation3` argument. -/
-- Note: there is deliberately no ppSpace between items
-- so that the space in the literals themselves stands out
syntax notation3Item := strLit <|> bindersItem <|> identOptScoped <|> foldAction
/--
`notation3` declares notation using Lean 3-style syntax. This command can be used in mathlib4
but it has an uncertain future and exists primarily for backward compatibility.
-/
macro doc:(docComment)? attrs:(Parser.Term.attributes)? ak:Term.attrKind
    "notation3" prec:(precedence)? name:(namedName)? prio:(namedPrio)? ppSpace
    lits:(notation3Item)+ " => " val:term : command => do
  let mut boundNames : Lean.HashMap Name Syntax := {}
  let mut macroArgs := #[]
  for lit in lits do
    match (lit : TSyntax ``notation3Item) with
    | `(notation3Item| $lit:str) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:str))
    | `(notation3Item| $_:bindersItem) =>
      -- HACK: Lean 3 traditionally puts a space after the main binder atom, resulting in
      -- notation3 "∑ "(...)", "r:(scoped f => sum f) => r
      -- but extBinders already has a space before it so we strip the trailing space of "∑ "
      if let `(macroArg| $lit:str) := macroArgs.back then
        macroArgs := macroArgs.pop.push (← `(macroArg| $(quote lit.getString.trimRight):str))
      macroArgs := macroArgs.push (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* => $kind ($x $y => $scopedTerm) $init)) =>
      macroArgs := macroArgs.push (← `(macroArg| $id:ident:sepBy(term, $sep:str)))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let init ← init.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let stx ← match kind with
        | `(foldKind| foldl) => `(expand_foldl% ($x $y => $scopedTerm) $init [$$(.ofElems $id),*])
        | `(foldKind| foldr) => `(expand_foldr% ($x $y => $scopedTerm) $init [$$(.ofElems $id),*])
        | _ => Macro.throwUnsupported
      boundNames := boundNames.insert id.getId stx
    | `(notation3Item| $lit:ident : (scoped $scopedId:ident => $scopedTerm)) =>
      let id := lit.getId
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      boundNames := boundNames.insert id <|
        ← `(expand_binders% ($scopedId => $scopedTerm) $$binders:extBinders,
          $(⟨lit.1.mkAntiquotNode `term⟩):term)
    | `(notation3Item| $lit:ident) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      boundNames := boundNames.insert lit.getId <| lit.1.mkAntiquotNode `term
    | stx => Macro.throwUnsupported
  let val ← val.replaceM fun
    | Syntax.ident _ _ id .. => pure $ boundNames.find? id
    | _ => pure none
  `($[$doc]? $(attrs)? $ak macro $(prec)? $(name)? $(prio)? $[$macroArgs]* : term => do `($val))

end Parser.Command
