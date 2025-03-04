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

/-- error: Abstract failed. The current goal is not a proposition. -/
#guard_msgs in
example (n : Nat) : n = by abstract exact 0 := sorry

/-- error: Abstract failed. There are 2 goals. Expected exactly 1 goal. -/
#guard_msgs in
example (f : True ∧ True → Nat) (n : Nat) :
  n = f (by constructor; abstract trivial; trivial) := sorry

/-- error: Abstract failed. There are unsolved goals
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


def bar : Function.const (∀ α : Type _, ∀ a : α, a = a) 1 (by abstract simp) = 1 := rfl

/--
info: def bar.{u_1} : Function.const (∀ (α : Type u_1) (a : α), a = a) 1 bar.abstract_1 = 1 :=
rfl
-/
#guard_msgs in
#print bar

def baz : Function.const (∀ α : Type u, ∀ a : α, a = a) 1 (by abstract simp) = 1 := rfl

/--
info: def baz.{u} : Function.const (∀ (α : Type u) (a : α), a = a) 1 baz.abstract_1 = 1 :=
rfl
-/
#guard_msgs in
#print baz
