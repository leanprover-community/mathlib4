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

class Foo where
  val : Nat

def foo : Foo where
  val := 37

def takeImplicit [f : Foo] : Nat :=
  f.val

example : Nat := by
  fail_if_success apply takeImplicit -- Default behaviour is `-allowSynthFailures`
  fail_if_success apply -allowSynthFailures takeImplicit
  apply +allowSynthFailures takeImplicit
  apply foo
