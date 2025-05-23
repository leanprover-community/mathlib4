/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Span

/-!
# Bounding the coefficients of the quotient and remainder of polynomials

This file proves that, for polynomials `p q : R[X]`, the coefficients of `p /ₘ q` and `p %ₘ q` can
be written as sums of products of coefficients of `p` and `q`.

Precisely, we show that each summand needs at most one coefficient of `p` and `deg p` coefficients
of `q`.
-/

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

local notation "deg("p")" => natDegree p
local notation3 "coeffs("p")" => Set.range (coeff p)
local notation3 "spanCoeffs("p")" => 1 ⊔ Submodule.span R coeffs(p)

open Submodule Set in
lemma coeff_divModByMonicAux_mem_span_pow_mul_span : ∀ (p q : S[X]) (hq : q.Monic) (i),
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
        degree_eq_bot, ne_eq, not_true_eq_false, and_false, ↓reduceDIte,
        Prod.fst_zero, coeff_zero, add_zero, Prod.snd_zero, Submodule.zero_mem, and_true]
      split_ifs
      exacts [H₀ _, zero_mem _]
    have H : span R coeffs(r) ≤ span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p) := by
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
          (1 ⊔ (span R coeffs(p) ⊔ span R coeffs(q) * span R coeffs(p))) := by gcongr
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
lemma coeff_modByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p %ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by
  delta modByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).2
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · rw [← one_mul (p.coeff i), ← one_pow p.natDegree]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow Mq hq' _) (hp i)

/-- For polynomials `p q : R[X]`, the coefficients of `p /ₘ q` can be written as sums of products of
coefficients of `p` and `q`.

Precisely, each summand needs at most one coefficient of `p` and `deg p` coefficients of `q`. -/
lemma coeff_divByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p /ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by
  delta divByMonic
  split_ifs with H
  · refine SetLike.le_def.mp ?_ (coeff_divModByMonicAux_mem_span_pow_mul_span (R := R) p q H i).1
    gcongr <;> exact sup_le (by simpa) (by simpa [Submodule.span_le, Set.range_subset_iff])
  · simp

variable [DecidableEq ι] {i j : ι}

open Function Ideal in
lemma idealSpan_range_update_divByMonic (hij : i ≠ j) (v : ι → R[X]) (hi : (v i).Monic) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by
  rw [modByMonic_eq_sub_mul_div _ hi, mul_comm, ← smul_eq_mul, Ideal.span, Ideal.span,
    Submodule.span_range_update_sub_smul hij]

end Polynomial
