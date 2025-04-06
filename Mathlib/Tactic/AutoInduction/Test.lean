import Mathlib.Tactic.AutoInduction.AutoInduction
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff


/-!

## TODOS

- check if variable name exists in `autoinduction` attribute

-/

set_option autoImplicit false
set_option linter.unusedTactic false

/--
warning: declaration uses 'sorry'
---
error: unexpected eliminator resulting type
  foo = bla
-/
#guard_msgs in
@[autoinduction (foo := by omega) (bla := by simp)]
theorem foobar (foo bla : Nat) : foo = bla :=
  sorry

attribute [autoinduction (C := by simp) (add := by simp)] Polynomial.induction_on

example {R : Type*} [Ring R] : ∀ p : Polynomial R, p.eval 0 = p.coeff 0 := fun p => by
  autoinduction h:p with
  -- | add l r hl hr => sorry
  | monomial n r hi =>
    rw [pow_succ,← mul_assoc,Polynomial.eval_mul_X,hi _]
    · simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Polynomial.coeff_X_zero]
    sorry



#autoindprinciples
