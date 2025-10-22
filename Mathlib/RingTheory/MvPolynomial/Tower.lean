/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`MvPolynomial σ R`.

This structure itself is provided elsewhere as `MvPolynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.Polynomial.Tower`.
-/


variable (R A B : Type*) {σ : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

theorem aeval_map_algebraMap (x : σ → B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {R A}

theorem aeval_algebraMap_apply (x : σ → A) (p : MvPolynomial σ R) :
    aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p) := by
  rw [aeval_def, aeval_def, ← coe_eval₂Hom, ← coe_eval₂Hom, map_eval₂Hom, ←
    IsScalarTower.algebraMap_eq, Function.comp_def]

theorem aeval_algebraMap_eq_zero_iff [NoZeroSMulDivisors A B] [Nontrivial B] (x : σ → A)
    (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false]

theorem aeval_algebraMap_eq_zero_iff_of_injective {x : σ → A} {p : MvPolynomial σ R}
    (h : Function.Injective (algebraMap A B)) :
    aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, ← (algebraMap A B).map_zero, h.eq_iff]

end CommSemiring

end MvPolynomial

namespace Subalgebra

open MvPolynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
theorem mvPolynomial_aeval_coe (S : Subalgebra R A) (x : σ → S) (p : MvPolynomial σ R) :
    aeval (fun i => (x i : A)) p = aeval x p := by convert aeval_algebraMap_apply A x p

end CommSemiring

end Subalgebra
