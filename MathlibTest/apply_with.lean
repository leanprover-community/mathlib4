import Mathlib.Tactic.ApplyWith

set_option autoImplicit true
example (f : ∀ x : Nat, x = x → α) : α := by
  apply (config := {}) f
  apply rfl
  apply 1

example (f : ∀ x : Nat, x = x → α) : α := by
  apply (config := { newGoals := .nonDependentOnly }) f
  apply @rfl _ 1

example (f : ∀ x : Nat, x = x → α) : α := by
  apply (config := { newGoals := .all }) f
  apply 1
  apply rfl
