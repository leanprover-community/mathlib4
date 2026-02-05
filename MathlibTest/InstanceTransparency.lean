import Mathlib.Data.Real.Basic

/-! # Test transparency level of `Div` field in `DivInvMonoid`

It is desirable that particular `DivInvMonoid`s have their `Div` instance not unfold at `.instance`
transparency level, in the same way that the `Div` field of a generic `DivInvMonoid` does not.

To ensure this, in examples where the `Div` field is defined as `fun a b ↦ a * b⁻¹`, we hide this
under one layer of other function (so for example the `Div` instance for `Rat` is defined to be
`⟨Rat.div⟩`, where `Rat.div` is defined to be `fun a b ↦ a * b⁻¹`).

This file checks that this and similar tricks have had the desired effect:
`with_reducible_and_instances apply mul_le_mul` fails although `apply mul_le_mul` succeeds.
-/

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

example {a b : α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] : a / 2 ≤ b / 2 := by
  fail_if_success with_reducible_and_instances apply mul_le_mul -- fails, as desired
  exact test_sorry

example {a b : ℚ} : a / 2 ≤ b / 2 := by
  fail_if_success with_reducible_and_instances apply mul_le_mul -- fails, as desired
  apply mul_le_mul
  repeat exact test_sorry

example {a b : ℝ} : a / 2 ≤ b / 2 := by
  fail_if_success with_reducible_and_instances apply mul_le_mul -- fails, as desired
  apply mul_le_mul
  repeat exact test_sorry
