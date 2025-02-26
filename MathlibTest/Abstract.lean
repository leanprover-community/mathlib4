import Mathlib.Tactic.Abstract
import Mathlib.Tactic.Core
import Mathlib.Lean.Name

open Lean

theorem foo (x : Fin 1) : x = ⟨0, by abstract omega⟩ := Subsingleton.elim ..

/--
info: theorem foo : ∀ (x : Fin 1), x = ⟨0, foo.abstract_1⟩ :=
fun x => Subsingleton.elim x ⟨0, foo.abstract_1⟩
-/
#guard_msgs in
#print foo

/-- error: Abstract failed. The current goal is not propositional. -/
#guard_msgs in
example (n : Nat) : n = by abstract exact 0 := sorry

/-- error: Abstract failed. There are 2 goals. Expected exactly 1 goal. -/
#guard_msgs in
example (f : True ∧ True → Nat) (n : Nat) :
  n = f (by constructor; abstract trivial; trivial) := sorry

/-- error: unsolved goals
case left
f : True ∧ True → Nat
n : Nat
⊢ True

case right
f : True ∧ True → Nat
n : Nat
⊢ True -/
#guard_msgs in
example (f : True ∧ True → Nat) (n : Nat) :
  n = f (by abstract constructor) := sorry
