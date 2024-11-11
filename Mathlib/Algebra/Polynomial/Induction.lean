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

@[elab_as_elim]
protected theorem induction_on {M : R[X] → Prop} (p : R[X]) (h_C : ∀ a, M (C a))
    (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (C a * X ^ n) → M (C a * X ^ (n + 1))) : M p := by
  have A : ∀ {n : ℕ} {a}, M (C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact h_C a
    | succ n ih => exact h_monomial _ _ ih
  have B : ∀ s : Finset ℕ, M (s.sum fun n : ℕ => C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert h_C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact h_add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (support p)

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {M : R[X] → Prop} (p : R[X]) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (monomial n a)) : M p :=
  Polynomial.induction_on p (h_monomial 0) h_add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact h_monomial _ _

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
