import Mathlib.Tactic.AutoInduction.AutoInduction
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff


/-!

## TODOS

- add code to the attribute to allow marking of `inductive` definitions
  - this should mark the natural induction principle for the definition as an autoinduction tactic
- fix error location when tactic doesn't close goal
- change error to be more informative in `where` case; suggest fix

## Nice-To-Haves

- code action to insert missing branches
- code action to insert a branch that's failing
- improve syntax for the attribute;
  - right now, if you want to give some tactic sequence, it makes the attribute take multiple lines

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

attribute [autoinduction (C := by simp) (add := by sorry)] Polynomial.induction_on

example {R : Type*} [Ring R] : ∀ p : Polynomial R, p.eval 0 = p.coeff 0 := fun p => by
  -- induction h:p using Polynomial.induction_on with
  autoinduction h:p with
  -- · simp_all
  --   sorry
  -- sorry
  -- case ofFinsupp =>
  --   sorry
  -- sorry
  -- case monomial =>
  | monomial n r hi =>
    rw [pow_succ,← mul_assoc,Polynomial.eval_mul_X]
    · simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Polynomial.coeff_X_zero]


#autoindprinciples
