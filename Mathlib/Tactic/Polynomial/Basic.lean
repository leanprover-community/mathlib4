/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Polynomial.Core
import Mathlib.Tactic.Algebra.Basic

/-!
# Polynomial
An extensible tactic for proving equality of polynomial expressions implemented using `algebra`.
To add support for a new polynomial-like type, one needs to do three things:
* Implment a polynomial extension that lets `polynomial` infer the base ring from the algebraic
  type. For example:
```
@[polynomial Polynomial _]
def polynomialInferBase : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure
```
* Tag any preprocessing lemmas with @[polynomial_pre]. This would include a lemma saying that
`C = algebraMap _ _` so that `algebra` knows how to normalize it.
* Tag any postprocessing lemmas with @[polynomial_post], so that `polynomial_nf` produces a pretty
expression.
-/

open Lean Mathlib.Tactic Mathlib.Tactic.Algebra Parser.Tactic Elab Meta Qq

namespace Mathlib.Tactic.Polynomial

section extension

end extension

/-- Infer base ring for `Polynomial R` -/
@[infer_polynomial_base]
def polynomialInferBase : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure

/-- Infer base ring for `MvPolynomial _ R` -/
@[infer_polynomial_base]
def mvPolynomialInferBaseImpl : PolynomialExt where
  infer := fun e ↦ do
  match_expr e with
  | MvPolynomial _ R _ => pure R
  | _ => failure

section Lemmas
variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[polynomial_post]
theorem _root_.Polynomial.algebraMap_eq_C : algebraMap R _ = Polynomial.C := rfl

@[polynomial_post]
theorem _root_.MvPolynomial.algebraMap_eq_C :
    algebraMap R (MvPolynomial σ R) = MvPolynomial.C := rfl

@[polynomial_pre]
theorem _root_.MvPolynomial.C_eq_algebraMap :
    MvPolynomial.C = algebraMap R (MvPolynomial σ R) := rfl

@[polynomial_pre]
theorem monomial_eq_smul (a : R) (n : ℕ) : Polynomial.monomial n a = a • (.X ^ n) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.smul_eq_C_mul]

-- polynomial_pre contains a lemma sending C -> algebraMap, so C is not simp normal form.
@[polynomial_pre]
theorem map_algebraMap (r : R) :
    Polynomial.map (algebraMap R A) (algebraMap R (Polynomial R) r) =
    algebraMap A (Polynomial A) (algebraMap R A r) := by
  simp

end Lemmas

open Mathlib.Meta AtomM

attribute [polynomial_pre] Polynomial.C_eq_algebraMap
  Polynomial.monomial_eq_smul Polynomial.map_add Polynomial.map_mul Polynomial.map_pow
  Polynomial.map_X Polynomial.map_natCast Polynomial.map_intCast

/- TODO: we don't currently have a good way to normalize monomials of MvPolynomials. These are
indexed by finsupps, making it difficult to turn into the appropriate normal form. -/
/-- Run the `polynomial_pre` simpset to turn nonstandard spellings of `algebraMap` such as
`Polynomial.C` into `algebraMap` -/
def preprocess (mvarId : MVarId) : MetaM MVarId := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  let preThms ← polynomialPreExt.getTheorems
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[preThms, thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in polynomial tactic: preprocessing should not close goals"
  return r

open Tactic

/-- Prove equality of polynomials allowing for variables in the exponent.
`example (a : ℚ) : (X + C a) * (X - C a) = X^2 + C (a^2) := by polynomial`
See also:
* `polynomial_nf` for normalizing polynomial expressions into sum-of-monomial form.
* `match_coefficients` for creating side goals equating matching coefficients. -/
elab (name := polynomial) "polynomial":tactic =>
  withMainContext do
    let g ← preprocess (← getMainGoal)
    let some (α, _, _) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let mut β : Expr := default
    try
      β ← Polynomial.inferBase α
    catch _ =>
      throwError "polynomial failed: not an equality of (mv)polynomials"
    AtomM.run .default (Algebra.proveEq (some (← getLevelQ' β)) g)

end Mathlib.Tactic.Polynomial
