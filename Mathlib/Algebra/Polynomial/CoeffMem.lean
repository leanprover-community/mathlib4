/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.Div

/-!
# Bounding the coefficients of the quotient and remainder of polynomials

This file proves that, for polynomials `p q : R[X]`, the coefficients of `p /ₘ q` and `p %ₘ q` can
be written as sums of products of coefficients of `p` and `q`.

Precisely, we show that each summand needs at most one coefficient of `p` and `deg p` coefficients
of `q`.
-/

namespace Polynomial
variable {R : Type*} [Ring R]

local notation "deg("p")" => natDegree p
local notation3 "coeffs("p")" => Set.range (coeff p)
local notation3 "spanCoeffs("p")" => 1 ⊔ Submodule.span ℤ coeffs(p)

open Submodule Set in
lemma coeff_divModByMonicAux_mem_span_pow_mul_span : ∀ (p q : R[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) ∧
    (p.divModByMonicAux hq).2.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
      refine Submodule.mul_le_mul_left (pow_le_pow_left' le_sup_left _) ?_
      simp only [one_pow, one_mul]
      exact SetLike.le_def.mp le_sup_right (subset_span (mem_range_self i))
    split_ifs with hpq; swap
    · simpa using H₀ _
    simp only [coeff_add, coeff_C_mul, coeff_X_pow]
    generalize hr : (p - q * (C p.leadingCoeff * X ^ (deg(p) - deg(q)))) = r
    by_cases hr' : r = 0
    · simp only [mul_ite, mul_one, mul_zero, hr', divModByMonicAux, degree_zero, le_bot_iff,
        degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, Prod.mk_zero_zero,
        Prod.fst_zero, coeff_zero, add_zero, Prod.snd_zero, Submodule.zero_mem, and_true]
      split_ifs
      exacts [H₀ _, zero_mem _]
    have H : span ℤ coeffs(r) ≤ span ℤ coeffs(p) ⊔ span ℤ coeffs(q) * span ℤ coeffs(p) := by
      rw [span_le, ← hr]
      rintro _ ⟨i, rfl⟩
      rw [coeff_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
      apply sub_mem
      · exact SetLike.le_def.mp le_sup_left (subset_span (mem_range_self _))
      · split_ifs
        · refine SetLike.le_def.mp le_sup_right (mul_mem_mul ?_ ?_) <;> exact subset_span ⟨_, rfl⟩
        · exact zero_mem _
    have deg_r_lt_deg_p : deg(r) < deg(p) := natDegree_lt_natDegree hr' (hr ▸ div_wf_lemma hpq hq)
    have H'' := calc
      spanCoeffs(q) ^ deg(r) * spanCoeffs(r)
      _ ≤ spanCoeffs(q) ^ deg(r) *
          (1 ⊔ (span ℤ coeffs(p) ⊔ span ℤ coeffs(q) * span ℤ coeffs(p))) := by gcongr
      _ ≤ spanCoeffs(q) ^ deg(r) * (spanCoeffs(q) * spanCoeffs(p)) := by
        gcongr
        simp only [sup_le_iff]
        refine ⟨one_le_mul le_sup_left le_sup_left, ?_, mul_le_mul' le_sup_right le_sup_right⟩
        rw [Submodule.sup_mul, one_mul]
        exact le_sup_of_le_left le_sup_right
      _ = spanCoeffs(q) ^ (deg(r) + 1) * spanCoeffs(p) := by rw [pow_succ, mul_assoc]
      _ ≤ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by gcongr; exacts [le_sup_left, deg_r_lt_deg_p]
    refine ⟨add_mem ?_ ?_, ?_⟩
    · split_ifs <;> simp only [mul_one, mul_zero]
      exacts [H₀ _, zero_mem _]
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span r _ hq i).1
    · exact H'' (coeff_divModByMonicAux_mem_span_pow_mul_span _ _ hq i).2
  termination_by p => deg(p)

/-- For polynomials `p q : R[X]`, the coefficients of `p %ₘ q` can be written as sums of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coefficients of `q`. -/
lemma coeff_modByMonic_mem_span_pow_mul_span (p q : R[X]) (i : ℕ) :
    (p %ₘ q).coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
  delta modByMonic
  split_ifs with H
  · exact (coeff_divModByMonicAux_mem_span_pow_mul_span p q H i).2
  · refine Submodule.mul_le_mul_left (pow_le_pow_left' le_sup_left _) ?_
    simp only [one_pow, one_mul]
    exact SetLike.le_def.mp le_sup_right (Submodule.subset_span (Set.mem_range_self i))

/-- For polynomials `p q : R[X]`, the coefficients of `p /ₘ q` can be written as sums of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coefficients of `q`. -/
lemma coeff_divByMonic_mem_span_pow_mul_span (p q : R[X]) (i : ℕ) :
    (p /ₘ q).coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by
  delta divByMonic
  split_ifs with H
  · exact (coeff_divModByMonicAux_mem_span_pow_mul_span p q H i).1
  · simp

end Polynomial
