import Mathlib.Tactic.Relation.Rfl

example (a : ℕ) : a = a := rfl

example (a : ℕ) : a = a := by rfl

open Setoid

variable {α : Sort u} [Setoid α]

@[refl] def iseqv_refl (a : α) : a ≈ a :=
  iseqv.refl a

example (a : α) : a ≈ a := by rfl

example (a : Nat) : a ≤ a := by (fail_if_success rfl); apply Nat.le_refl

attribute [refl] Nat.le_refl

example (a : Nat) : a ≤ a := by rfl

structure Foo

instance : LE Foo where le _a _b := ∀ _x : Unit, True

@[refl] theorem foo_refl : ∀ (a : Foo), a ≤ a := fun _ _ => trivial

example : ∀ (a : Foo), a ≤ a := by intro a; rfl
