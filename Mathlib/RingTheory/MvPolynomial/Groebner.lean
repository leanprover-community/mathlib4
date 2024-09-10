/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.Data.Finsupp.Lex
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Monomial orders, division algorithm, examples, Dickson orders

Reference : [Becker-Weispfenning1993] -/

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

/-- Delete the leading term in a multivariate polynomial (for some monomial order) -/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.lCoeff f)

theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f ≠ 0) :
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f ≠ 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m), hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, lCoeff]

/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.lCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
 f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.lCoeff f) * b

theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.lCoeff b))
    (hbf : m.degree b ≤ m.degree f) (hf : m.degree f ≠ 0) :
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f =
    m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.lCoeff f)) +
      m.degree b := by
    classical
    rw [degree_monomial, if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, lCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [lCoeff_mul' (m := m), lCoeff_monomial]
    rw [mul_comm, ← mul_assoc]
    simp only [IsUnit.mul_val_inv, one_mul]
    rfl
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    change lCoeff m _ = 0 at H'
    rw [lCoeff_eq_zero_iff] at H'
    rw [H', degree_zero] at K
    exact hf K.symm

theorem monomialOrderDiv (B : Set (MvPolynomial σ R)) (hB : ∀ b ∈ B, IsUnit (m.lCoeff b))
    (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) := by
  by_cases hB' : ∃ b ∈ B, m.degree b = 0
  · obtain ⟨b, hb, hb0⟩ := hB'
    use Finsupp.single ⟨b, hb⟩ ((hB b hb).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm, smul_eq_C_mul]
    constructor
    · intro c
      by_cases hc : c = ⟨b, hb⟩
      · apply le_trans degree_mul_le
        simp only [hc, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne (Ne.symm hc), mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  push_neg at hB'
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases hf : ∃ b ∈ B, m.degree b ≤ m.degree f
  · obtain ⟨b, hb, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hB b hb) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hB b hb) hf
      intro hf0'
      apply hB' b hb
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := monomialOrderDiv B hB (m.reduce (hB b hb) f)
    use g' +
      Finsupp.single ⟨b, hb⟩ (monomial (m.degree f - m.degree b) ((hB b hb).unit⁻¹ * m.lCoeff f))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro c
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · apply le_trans degree_mul_le
          simp only [map_add]
          apply le_of_le_of_eq (add_le_add_left (degree_monomial_le _) _)
          simp only [← hc]
          rw [← map_add, m.toSyn.injective.eq_iff]
          rw [add_tsub_cancel_of_le]
          exact hf
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · push_neg at hf
    suffices ∃ (g' : B →₀ MvPolynomial σ R), ∃ r',
        (m.subLTerm f = (Finsupp.linearCombination (MvPolynomial σ R) fun b ↦ ↑b) g' + r') ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g' b)) ≼[m] m.degree (m.subLTerm f)) ∧
        (∀ c ∈ r'.support, ∀ b ∈ B, ¬ m.degree b ≤ c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' +  monomial (m.degree f) (m.lCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc b hb
        by_cases hc' : c ∈ r'.support
        · exact H'.2.2 c hc' b hb
        · classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union, Classical.or_iff_not_imp_left] at this
          specialize this hc'
          simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
            coeff_degree_eq_zero_iff, Classical.not_imp] at this
          rw [← this.1]
          exact hf b hb
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · apply monomialOrderDiv B hB
termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
decreasing_by
· exact deg_reduce
· apply degree_sub_LTerm_lt
  intro hf0
  apply hf'0
  simp only [subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
  simp

end MonomialOrder


