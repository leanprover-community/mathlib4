/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
See also `Data/Polynomial/Inductions.lean` (with an `s`!).

The main result is `Polynomial.induction_on`.
-/


noncomputable section

open Finsupp Finset

namespace Polynomial

open Polynomial

universe u v w x y z

variable {R : Type u}

section Semiring

variable [Semiring R]

open Submodule Polynomial Set

variable {f : R[X]} {I : Ideal R[X]}

/-- If the coefficients of a polynomial belong to an ideal, then that ideal contains
the ideal spanned by the coefficients of the polynomial. -/
theorem span_le_of_C_coeff_mem (cf : ∀ i : ℕ, C (f.coeff i) ∈ I) :
    Ideal.span { g | ∃ i, g = C (f.coeff i) } ≤ I := by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf

theorem mem_span_C_coeff : f ∈ Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) } := by
  let p := Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) ∈ p := by
    apply subset_span
    rw [mem_setOf_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n) ∈ p := p.smul_mem _ this
  convert this using 1
  simp only [monomial_mul_C, one_mul, smul_eq_mul]
  rw [← C_mul_X_pow_eq_monomial]

theorem exists_C_coeff_not_mem : f ∉ I → ∃ i : ℕ, C (coeff f i) ∉ I :=
  Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

end Semiring

end Polynomial
