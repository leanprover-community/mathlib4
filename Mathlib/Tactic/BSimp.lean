import Mathlib.Tactic.SplitIfs

meta section -- public meta section

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic
open Mathlib.Tactic

#check Lean.Core.mkFreshUserName
namespace Meta.BSimp

syntax branch_discharger :=
  atomic(" (" patternIgnore(&"branch_discharger" <|> &"branch_disch")) " := "
    withoutPosition(tacticSeq) ")"

syntax (name := bsimp)
  "bsimp" optConfig (branch_discharger)? (discharger)? (simpArgs)? (location)? : tactic

@[tactic bsimp]
partial def bsimpTac : Tactic
  | `(tactic| bsimp $[$d]? $[$sd]? $[[$simpArgs,*]]? $[at $location]?) => do
    let location' := match location with
    | none => Location.targets #[] true
    | some location' => expandLocation location'
    let args := simpArgs.map (·.getElems) |>.getD #[]
    evalTactic (← `(tactic|
      simp $[$sd]? only [reduceIte, $args,*] $[at $location]?))
    if let some ⟨_, cond⟩ ← findIfCondAt location' then
      let hName ← mkFreshUserName `test
      let hIdent := mkIdent hName
      let splitCases :=
        evalTactic (← `(tactic| by_cases $hIdent : $(← Elab.Term.exprToSyntax cond)))
      let bsimpCase :=
        evalTactic
          (← `(tactic| simp $[$sd]? only [reduceIte, $hIdent:ident, $args,*] $[at $location]?))
        -- evalTactic
        --   (← `(tactic| bsimp $[$d]? $[$sd]? [$hIdent:ident, $args,*] $[at $location]?))
      andThenOnSubgoals splitCases bsimpCase
  | _ => Lean.Elab.throwUnsupportedSyntax


end Meta.BSimp

section TestCases

theorem sub_ite (a b : Nat) : ((a - b : Nat) : Int) =
  if b ≤ a then (a : Int) - (b : Int) else 0 := by sorry

-- (hab : b ≤ a)
example (a b : Nat) : (a - b : Nat) = (a : Int) - (b : Int) := by
  bsimp [sub_ite]




end TestCases
