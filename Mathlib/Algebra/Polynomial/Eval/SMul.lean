/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluating polynomials and scalar multiplication

## Main results
* `eval₂_smul`, `eval_smul`, `map_smul`, `comp_smul`: the functions preserve scalar multiplication
* `Polynomial.leval`: `Polynomial.eval` as linear map

-/

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R →+* S) (x : S)

@[simp]
theorem eval₂_smul (g : R →+* S) (p : R[X]) (x : S) {s : R} :
    eval₂ g x (s • p) = g s * eval₂ g x p := by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

end

section Eval

variable {x : R}

@[simp]
theorem eval_smul [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X])
    (x : R) : (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p, eval, eval₂_smul, RingHom.id_apply, smul_one_mul, eval₂_id]

/-- `Polynomial.eval` as linear map -/
@[simps]
def leval {R : Type*} [Semiring R] (r : R) : R[X] →ₗ[R] R where
  toFun f := f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

end Eval

section Comp

@[simp]
theorem smul_comp [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
    (s • p).comp q = s • p.comp q := by
  rw [← smul_one_smul R s p, comp, comp, eval₂_smul, ← smul_eq_C_mul, smul_assoc, one_smul]

end Comp

section Map

variable [Semiring S]
variable (f : R →+* S)

@[simp]
protected theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map, eval₂_smul, RingHom.comp_apply, C_mul']

end Map

end Semiring

end Polynomial
