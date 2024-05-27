/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Basic

#align_import data.polynomial.induction from "leanprover-community/mathlib"@"63417e01fbc711beaf25fa73b6edb395c0cfddd0"

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

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R}
  {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

@[elab_as_elim]
protected theorem induction_on {M : R[X] → Prop} (p : R[X]) (h_C : ∀ a, M (C a))
    (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (C a * X ^ n) → M (C a * X ^ (n + 1))) : M p := by
  have A : ∀ {n : ℕ} {a}, M (C a * X ^ n) := by
    intro n a
    induction' n with n ih
    · rw [pow_zero, mul_one]; exact h_C a
    · exact h_monomial _ _ ih
  have B : ∀ s : Finset ℕ, M (s.sum fun n : ℕ => C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert h_C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact h_add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (support p)
#align polynomial.induction_on Polynomial.induction_on

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {M : R[X] → Prop} (p : R[X]) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (monomial n a)) : M p :=
  Polynomial.induction_on p (h_monomial 0) h_add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact h_monomial _ _
#align polynomial.induction_on' Polynomial.induction_on'

open Submodule Polynomial Set

variable {f : R[X]} {I : Ideal R[X]}

/-- If the coefficients of a polynomial belong to an ideal, then that ideal contains
the ideal spanned by the coefficients of the polynomial. -/
theorem span_le_of_C_coeff_mem (cf : ∀ i : ℕ, C (f.coeff i) ∈ I) :
    Ideal.span { g | ∃ i, g = C (f.coeff i) } ≤ I := by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf
set_option linter.uppercaseLean3 false in
#align polynomial.span_le_of_C_coeff_mem Polynomial.span_le_of_C_coeff_mem

theorem mem_span_C_coeff : f ∈ Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) } := by
  let p := Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) }
  nth_rw 1 [(sum_C_mul_X_pow_eq f).symm]
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
set_option linter.uppercaseLean3 false in
#align polynomial.mem_span_C_coeff Polynomial.mem_span_C_coeff

theorem exists_C_coeff_not_mem : f ∉ I → ∃ i : ℕ, C (coeff f i) ∉ I :=
  Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff
set_option linter.uppercaseLean3 false in
#align polynomial.exists_C_coeff_not_mem Polynomial.exists_C_coeff_not_mem

end Semiring

end Polynomial
