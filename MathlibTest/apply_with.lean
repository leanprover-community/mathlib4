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

section

/-! Making sure we have useful error reporting. -/

def MyProp (n : Nat) : Prop := n = n

theorem MyProp.mk (n : Nat) : MyProp n := by rw [MyProp]

/--
error: Application type mismatch: The argument
  "foo"
has type
  String
but is expected to have type
  Nat
in the application
  MyProp.mk "foo"
-/
#guard_msgs in
example : MyProp 1337 := by
  apply MyProp.mk "foo"
  exact "qed"

end
