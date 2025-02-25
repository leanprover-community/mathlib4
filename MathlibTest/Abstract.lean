import Mathlib.Tactic.Abstract
import Mathlib.Tactic.Core
import Mathlib.Lean.Name

open Lean

theorem foo (x : Fin 1) : x = ⟨0, by abstract omega⟩ := Subsingleton.elim ..

-- We don't test the precise type of `foo`, since I don't know how robust
-- the generated unique number is (currently 87)
run_cmd do
  let some t := (← getEnv).find? `foo | unreachable!
  if !t.type.foldConsts false (fun n b ↦ b || n matches .num _ _) then
    throwError "no aux-lemma in the type of foo"

/-- error: Abstract failed. The current goal is not propositional. -/
#guard_msgs in
example (n : Nat) : n = by abstract exact 0 := sorry

/-- error: Abstract failed. There are 2 goals. Expected exactly 1 goal. -/
#guard_msgs in
example (f : True ∧ True → Nat) (n : Nat) :
  n = f (by constructor; abstract trivial; trivial) := sorry
