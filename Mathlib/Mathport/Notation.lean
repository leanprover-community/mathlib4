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
`expandBinders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expandBinders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expandBinders% ($x => $term) $y:extBinder, $res) =>
    `(expandBinders% ($x => $term) ($y:extBinder), $res)
  | `(expandBinders% ($_ => $_), $res) => pure res
macro_rules
  | `(expandBinders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident : $ty ↦ expandBinders% ($x => $term) $[$binders]*, $res)
  | `(expandBinders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident ↦ expandBinders% ($x => $term) (h : satisfies_binder_pred% $y $pred)
        $[$binders]*, $res)

macro (name := expandFoldl) "expandFoldl% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg ↦ do
    term.replaceM fun e ↦
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expandFoldr% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res ↦ do
    term.replaceM fun e ↦
      return if e == x then some arg else if e == y then some res else none

/-- Keywording indicating whether to use a left- or right-fold. -/
syntax foldKind := &"foldl" <|> &"foldr"
/-- `notation3` argument matching `extBinders`. -/
syntax bindersItem := atomic("(" "..." ")")
/-- `notation3` argument simulating a Lean 3 fold notation. -/
syntax foldAction := "(" ident strLit "*" " => " foldKind " (" ident ident " => " term ") " term ")"
/-- `notation3` argument binding a name. -/
syntax identOptScoped := ident (":" "(" "scoped " ident " => " term ")")?
/-- `notation3` argument. -/
syntax notation3Item := strLit <|> bindersItem <|> identOptScoped <|> foldAction
/--
`notation3` declares notation using Lean 3-style syntax.
Only to be used for mathport.
-/
macro doc:(docComment)? ak:Term.attrKind "notation3"
    prec:(precedence)? name:(namedName)? prio:(namedPrio)?
    lits:(notation3Item)+ " => " val:term : command => do
  let mut boundNames : Lean.HashMap Name Syntax := {}
  let mut macroArgs := #[]
  for lit in lits do
    match (lit : TSyntax ``notation3Item) with
    | `(notation3Item| $lit:str) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:str))
    | `(notation3Item| $_:bindersItem) =>
      macroArgs := macroArgs.push (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* => $kind ($x $y => $scopedTerm) $init)) =>
      macroArgs := macroArgs.push (← `(macroArg| $id:ident:sepBy(term, $sep:str)))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let init ← init.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let args := mkNullNode #[.mkAntiquotSuffixSpliceNode `sepBy
        (.mkAntiquotNode `term (← `(Syntax.TSepArray.ofElems ($id:ident).getElems))) ",*"]
      let args := #[
        Lean.mkAtom "(", x, y, Lean.mkAtom "=>", scopedTerm, Lean.mkAtom ")", init,
        Lean.mkAtom "[", args, Lean.mkAtom "]"]
      let stx ← show MacroM Syntax.Term from match kind with
        | `(foldKind| foldl) => pure ⟨mkNode ``expandFoldl (#[Lean.mkAtom "expandFoldl%"] ++ args)⟩
        | `(foldKind| foldr) => pure ⟨mkNode ``expandFoldr (#[Lean.mkAtom "expandFoldr%"] ++ args)⟩
        | _ => Macro.throwUnsupported
      boundNames := boundNames.insert id.getId stx
    | `(notation3Item| $lit:ident : (scoped $scopedId:ident => $scopedTerm)) =>
      let id := lit.getId
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      boundNames := boundNames.insert id <|
        ← `(expandBinders% ($scopedId => $scopedTerm) $$binders:extBinders,
          $(⟨lit.1.mkAntiquotNode `term⟩):term)
    | `(notation3Item| $lit:ident) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      boundNames := boundNames.insert lit.getId <| lit.1.mkAntiquotNode `term
    | stx => Macro.throwUnsupported
  let val ← val.replaceM fun
    | Syntax.ident _ _ id .. => pure $ boundNames.find? id
    | _ => pure none
  `($[$doc:docComment]? $ak:attrKind macro $[$prec]? $[$name]? $[$prio]? $[$macroArgs]* : term => do
    `($val:term))

end Parser.Command
