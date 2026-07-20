/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Disproof of the Jacobian conjecture

The Jacobian conjecture asserts that a polynomial self-map of `Kⁿ`, for `K` a field of
characteristic zero, whose Jacobian determinant is a nonzero constant is injective. We formalize
a counterexample in three variables due to Levent Alpöge and Fable, valid over every field.

The map `F : K³ → K³` given by
```
F (x, y, z) = ((1 + 2xy)³z + 4y²(1 + 2xy)(2 + 3xy),
               y + 3x(1 + 2xy)²z + 12xy²(2 + 3xy),
               -x + 3x²y + x³z)
```
has Jacobian determinant `1` (`jacobianDet_F`) but is not injective (`not_injective_evalMap_F`):
it identifies `(1, -3/4, 13/4)` and `(-1, 3/4, 13/4)` when `2 ≠ 0` in `K`, and in characteristic
two it identifies `(0, 1, 0)` and `(1, 1, 0)`. The disproof of the conjecture is stated in
`jacobian_conjecture_false`. We use a rescaled variant of the map in the reference, with Jacobian
determinant `1` rather than `-2`.

## References

<https://x.com/__alpoge__/status/2079028340955197566>
-/

namespace Counterexample

namespace JacobianConjecture

open Matrix Function MvPolynomial

variable {R : Type*} {σ : Type*}

/-- The Jacobian matrix of a family of multivariate polynomials, with `(i, j)` entry
`pderiv j (F i)`. -/
noncomputable def jacobianMatrix [CommSemiring R] (F : σ → MvPolynomial σ R) :
    Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j ↦ pderiv j (F i)

/-- The Jacobian determinant of a family of multivariate polynomials. -/
noncomputable def jacobianDet [CommRing R] [Fintype σ] [DecidableEq σ]
    (F : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  (jacobianMatrix F).det

/-- The polynomial self-map induced by a family of multivariate polynomials. -/
noncomputable def evalMap [CommSemiring R] (F : σ → MvPolynomial σ R) (p : σ → R) : σ → R :=
  fun i ↦ eval p (F i)

variable (K : Type*) [Field K]

/-- The three components of the counterexample. -/
noncomputable def F : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + C 2 * X 0 * X 1) ^ 3 * X 2
      + C 4 * X 1 ^ 2 * (1 + C 2 * X 0 * X 1) * (C 2 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + C 2 * X 0 * X 1) ^ 2 * X 2
      + C 12 * X 0 * X 1 ^ 2 * (C 2 + C 3 * (X 0 * X 1)),
    -X 0 + C 3 * X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2]

theorem jacobianDet_F : jacobianDet (F K) = 1 := by
  simp only [jacobianDet, jacobianMatrix, det_fin_three, of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_neg, Derivation.map_one_eq_zero, pderiv_mul,
    pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_ofNat]
  ring

variable {K}

theorem evalMap_F_char_ne_two (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![1, -(3 / 4), 13 / 4] = evalMap (F K) ![-1, 3 / 4, 13 / 4] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;>
    simp only [evalMap, F, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, map_add, map_mul, map_pow, map_neg, map_one,
      eval_C, eval_X] <;>
    field_simp [h4] <;> ring

theorem evalMap_F_char_two (h2 : (2 : K) = 0) :
    evalMap (F K) ![0, 1, 0] = evalMap (F K) ![1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp only [evalMap, F, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, map_add, map_mul, map_pow, map_neg, map_one,
      eval_C, eval_X]
  · linear_combination (-26 : K) * h2
  · linear_combination (-30 : K) * h2
  · linear_combination (-1 : K) * h2

variable (K)

theorem not_injective_evalMap_F : ¬ Injective (evalMap (F K)) := by
  intro h
  by_cases h2 : (2 : K) = 0
  · exact zero_ne_one (congrFun (h (evalMap_F_char_two h2)) 0)
  · have h0 : (1 : K) = -1 := congrFun (h (evalMap_F_char_ne_two h2)) 0
    exact h2 (by linear_combination h0)

/-- The Jacobian conjecture fails over every field `K`: there is a polynomial self-map of `K³`
with Jacobian determinant `1` which is not injective. -/
theorem jacobian_conjecture_false :
    ¬ ∀ G : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet G) → Injective (evalMap G) :=
  fun h ↦ not_injective_evalMap_F K (h (F K) (jacobianDet_F K ▸ isUnit_one))

end JacobianConjecture

end Counterexample
