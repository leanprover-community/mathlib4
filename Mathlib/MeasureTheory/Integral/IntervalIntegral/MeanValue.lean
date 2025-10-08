/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# First mean value theorem for integrals

We prove versions of the first mean value theorem for (unordered) interval integrals
w.r.t. an arbitrary measure in `ℝ`

One assuming almost-every where non-negativity of `g` under an arbitrary measure,
and one assuming point-wise non-negativity together with continuity of `g`.

## Main statements

- `exists_eq_const_mul_interval_integral_of_continuous_on_of_ae_nonneg`:
    **First mean value theorem for integrals** for (unordered) interval integrals when
    `g` is interval integrable on `a..b` w.r.t. an arbitrary measure `μ` and satisfies
    `g ≥ 0` almost everywhere on `uIcc a b`.
- `exists_eq_const_mul_interval_integral_of_continuous_on_of_nonneg`:
    **First mean value theorem for integrals** for (unordered) interval integrals when
    `g` is continuous on `uIcc a b` and nonnegative there (Lebesgue measure).

## References

* [V. A. Zorich, *Mathematical Analysis I*][zorich2016],
    Thm. 5 (First mean-value theorem for the integral).
* <https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization>

## Tags

mean value theorem, interval integral, measure, nonnegative, continuous, integrable
-/

open MeasureTheory Set intervalIntegral Filter

/-- **First mean value theorem for integrals (interval integral, arbitrary measure).**
Let `μ` be a measure on `ℝ`. If `f : ℝ → ℝ` is continuous on `uIcc a b` and
`g : ℝ → ℝ` is interval integrable on `a..b` w.r.t. `μ`, and `g ≥ 0` almost
everywhere on `uIcc a b`, then there exists `c ∈ uIcc a b` such that
`∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ`. -/
theorem exists_eq_const_mul_interval_integral_of_continuous_on_of_ae_nonneg
    {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ᵐ x ∂(μ.restrict (uIcc a b)), 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  wlog a_b_case : a ≤ b generalizing a b
  · simp at a_b_case
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this
        (a := b) (b := a) (by rwa [uIcc_comm])
        hg.symm (by rwa [uIcc_comm])
        a_b_case.le
    refine ⟨c, ?_, ?_⟩
    · rwa [uIcc_comm]
    · calc
        _ = - ∫ x in b..a, f x * g x ∂μ := by
          exact integral_symm b a
        _ = - (f c * ∫ x in b..a, g x ∂μ) := by
          rw [that]
      simp [integral_symm b a]
  · have is_compact_uIcc_a_b : IsCompact (uIcc a b) := by
      exact isCompact_uIcc
    obtain ⟨x_f_min, x_f_min_in_uIcc_a_b, f_min⟩ := by
      exact IsCompact.exists_isMinOn
        is_compact_uIcc_a_b nonempty_uIcc hf
    obtain ⟨x_f_max, x_f_max_in_uIcc_a_b, f_max⟩ := by
      exact IsCompact.exists_isMaxOn
        is_compact_uIcc_a_b nonempty_uIcc hf
    let m := f x_f_min
    let M := f x_f_max
    have m_le_f_x : ∀ x ∈ uIcc a b, m ≤ f x := by
      simpa
    have f_x_le_M : ∀ x ∈ uIcc a b, f x ≤ M := by
      simpa
    have f_g_int_μ_a_b : IntervalIntegrable (fun x ↦ f x * g x) μ a b := by
      exact IntervalIntegrable.continuousOn_mul hg hf
    have m_g_int_μ_a_b : IntervalIntegrable (fun x ↦ m * g x) μ a b := by
      unfold m
      exact hg.const_mul m
    have M_g_int_μ_a_b : IntervalIntegrable (fun x ↦ M * g x) μ a b := by
      unfold M
      exact hg.const_mul M
    have ae_left_uIcc : ∀ᵐ x ∂(μ.restrict (uIcc a b)), m * g x ≤ f x * g x := by
      rw [ae_restrict_iff' measurableSet_uIcc]
      have hg0' : ∀ᵐ x ∂μ, x ∈ uIcc a b → 0 ≤ g x := by
        rwa [← ae_restrict_iff' measurableSet_uIcc]
      have m_le_f_x_ae : ∀ᵐ x ∂μ, x ∈ uIcc a b → m ≤ f x := by
        apply Eventually.of_forall
        exact fun x a ↦ f_min a
      filter_upwards [m_le_f_x_ae, hg0'] with x h_m_le_f_x g_x_nonneg
      exact fun a ↦ mul_le_mul_of_nonneg_right (f_min a) (g_x_nonneg a)
    have ae_right_uIcc : ∀ᵐ x ∂(μ.restrict (uIcc a b)), f x * g x ≤ M * g x := by
      rw [ae_restrict_iff' measurableSet_uIcc]
      have hg0' : ∀ᵐ x ∂μ, x ∈ uIcc a b → 0 ≤ g x := by
        rwa [← ae_restrict_iff' measurableSet_uIcc]
      have m_le_f_x_ae : ∀ᵐ x ∂μ, x ∈ uIcc a b → m ≤ f x := by
        apply Eventually.of_forall
        exact fun x a ↦ f_min a
      filter_upwards [m_le_f_x_ae, hg0'] with x h_m_le_f_x g_x_nonneg
      exact fun a ↦ mul_le_mul_of_nonneg_right (f_max a) (g_x_nonneg a)
    have ae_left_Icc : ∀ᵐ x ∂(μ.restrict (Icc a b)), m * g x ≤ f x * g x := by
      simpa [a_b_case] using ae_left_uIcc
    have ae_right_Icc : ∀ᵐ x ∂(μ.restrict (Icc a b)), f x * g x ≤ M * g x := by
      simpa [a_b_case] using ae_right_uIcc
    have int_f_g_bounds :
        m * (∫ x in a..b, g x ∂μ) ≤ (∫ x in a..b, f x * g x ∂μ)
        ∧ (∫ x in a..b, f x * g x ∂μ) ≤ M * (∫ x in a..b, g x ∂μ) := by
      constructor
      · calc
          _ = (∫ x in a..b, m * g x ∂μ) := by
            simp
          _ ≤ (∫ x in a..b, f x * g x ∂μ) := by
            exact integral_mono_ae_restrict a_b_case m_g_int_μ_a_b f_g_int_μ_a_b ae_left_Icc
      · calc
          _ ≤ (∫ x in a..b, M * g x ∂μ) := by
            exact integral_mono_ae_restrict a_b_case f_g_int_μ_a_b M_g_int_μ_a_b ae_right_Icc
          _ = M * (∫ x in a..b, g x ∂μ) := by simp
    by_cases int_g_case : (∫ x in a..b, g x ∂μ) = 0
    · refine ⟨x_f_min, x_f_min_in_uIcc_a_b, ?_⟩
      have : 0 ≤ (∫ x in a..b, f x * g x ∂μ) ∧ (∫ x in a..b, f x * g x ∂μ) ≤ 0 := by
        simpa [int_g_case] using int_f_g_bounds
      have int_f_g_eq_zero : (∫ x in a..b, f x * g x ∂μ) = 0 := by
        exact le_antisymm this.2 this.1
      simp [int_g_case, int_f_g_eq_zero]
    · let r := (∫ x in a..b, f x * g x ∂μ) / (∫ x in a..b, g x ∂μ)
      have g_nonneg_Icc_a_b_ae : ∀ᵐ x ∂(μ.restrict (Icc a b)), 0 ≤ g x := by
        simpa [a_b_case] using hg0
      have int_g_nonneg : 0 ≤ ∫ x in a..b, g x ∂μ := by
        exact integral_nonneg_of_ae_restrict a_b_case g_nonneg_Icc_a_b_ae
      have int_g_pos : 0 < ∫ x in a..b, g x ∂μ := by
        have int_g_neq_zero : (∫ x in a..b, g x ∂μ) ≠ 0 := by
          exact int_g_case
        exact lt_of_le_of_ne int_g_nonneg int_g_neq_zero.symm
      have m_le_r : m ≤ r := by
        have left_bound :
            m ≤ (∫ x in a..b, f x * g x ∂μ) / (∫ x in a..b, g x ∂μ) := by
          simpa [le_div_iff₀ int_g_pos] using int_f_g_bounds.1
        simpa [r] using left_bound
      have r_le_M : r ≤ M := by
        have right_bound :
            (∫ x in a..b, f x * g x ∂μ) / (∫ x in a..b, g x ∂μ) ≤ M := by
          simpa [div_le_iff₀ int_g_pos] using int_f_g_bounds.2
        simpa [r] using right_bound
      have r_in_Icc_m_M : r ∈ Icc m M := ⟨m_le_r, r_le_M⟩
      have ivt :
          uIcc (f x_f_min) (f x_f_max) ⊆ f '' uIcc x_f_min x_f_max := by
        have f_cont_uIcc_x_f_min_x_f_max :
            uIcc x_f_min x_f_max ⊆ uIcc a b := by
          intro x hx
          have hx' : min x_f_min x_f_max ≤ x ∧ x ≤ max x_f_min x_f_max := by
            simpa [uIcc] using hx
          have a_b_le_min : min a b ≤ min x_f_min x_f_max :=
            le_min x_f_min_in_uIcc_a_b.1 x_f_max_in_uIcc_a_b.1
          have max_le_a_b : max x_f_min x_f_max ≤ max a b :=
            max_le x_f_min_in_uIcc_a_b.2 x_f_max_in_uIcc_a_b.2
          exact ⟨a_b_le_min.trans hx'.1, hx'.2.trans max_le_a_b⟩
        intro x hx
        apply intermediate_value_uIcc
        apply ContinuousOn.mono hf f_cont_uIcc_x_f_min_x_f_max
        assumption
      rw [subset_image_iff] at ivt
      rcases ivt with ⟨u, u_subset_uIcc, f_eq_image_uIcc⟩
      have m_le_M : m ≤ M := by
        exact f_min x_f_max_in_uIcc_a_b
      have r_in_f_image : r ∈ f '' u := by
        simpa [m, M, m_le_M, f_eq_image_uIcc] using r_in_Icc_m_M
      rw [mem_image] at r_in_f_image
      rcases r_in_f_image with ⟨c, c_in_u, f_c_eq_r⟩
      have c_in_uIcc : c ∈ uIcc x_f_min x_f_max := by
        exact u_subset_uIcc c_in_u
      have a_le_x : a ≤ min x_f_min x_f_max := by
        apply le_min
        · simpa [a_b_case] using x_f_min_in_uIcc_a_b.1
        · simpa [a_b_case] using x_f_max_in_uIcc_a_b.1
      have x_le_b : max x_f_min x_f_max ≤ b := by
        apply max_le
        · simpa [a_b_case] using x_f_min_in_uIcc_a_b.2
        · simpa [a_b_case] using x_f_max_in_uIcc_a_b.2
      have c_in_uIcc_x_f_min_max : c ∈ uIcc x_f_min x_f_max := by
        simp [uIcc]
        rw [uIcc] at c_in_uIcc
        rcases c_in_uIcc with ⟨left, right⟩
        constructor
        · exact inf_le_iff.mp left
        · exact le_sup_iff.mp right
      have c_in_uIcc_a_b : c ∈ uIcc a b := by
        simp [uIcc]
        rw [uIcc] at c_in_uIcc
        rcases c_in_uIcc with ⟨left, right⟩
        constructor
        · left
          exact le_trans a_le_x left
        · right
          exact le_trans right x_le_b
      have int_f_g_eq_r_mul_int_g :
          (∫ x in a..b, f x * g x ∂μ) = r * (∫ x in a..b, g x ∂μ) := by
        have r_eq :
            r = (∫ x in a..b, f x * g x ∂μ) / (∫ x in a..b, g x ∂μ) := by
          simp [r]
        rw [r_eq]
        field_simp
      refine ⟨c, c_in_uIcc_a_b, ?_⟩
      simpa [f_c_eq_r]

/-- **First mean value theorem for integrals (interval integral).**
Let `f g : ℝ → ℝ` be continuous on `uIcc a b`. If `g ≥ 0` on `uIcc a b`,
then there exists `c ∈ uIcc a b` such that
`∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x`. -/
theorem exists_eq_const_mul_interval_integral_of_continuous_on_of_nonneg
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hg : ContinuousOn g (uIcc a b))
    (hg0 : ∀ x ∈ uIcc a b, 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x) = f c * (∫ x in a..b, g x) := by
  have hg0_ae : ∀ᵐ x ∂(volume.restrict (uIcc a b)), 0 ≤ g x := by
    rw [ae_restrict_iff' measurableSet_uIcc]
    exact ae_of_all volume hg0
  exact exists_eq_const_mul_interval_integral_of_continuous_on_of_ae_nonneg
    hf hg.intervalIntegrable hg0_ae
