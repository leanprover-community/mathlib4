/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Vector measure with density with respect to a vector measure

-/

open Set Filter
open scoped Topology ENNReal

namespace MeasureTheory.VectorMeasure

local infixr:25 " →ₛ " => SimpleFunc

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X F} {f g : X → E} {B : E →L[ℝ] F →L[ℝ] G} {s : Set X}

open scoped Classical in
/-- The vector measure with density `f` with respect to a vector measure `μ`, associating to a
measurable set the mass `∫ᵛ x in s, f x ∂[B; μ]`.
If `f` is not integrable, we use the junk value `0`. -/
noncomputable def withDensity (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X G :=
  if h : μ.Integrable f B then
    { measureOf' s := ∫ᵛ x in s, f x ∂[B; μ]
      empty' := by simp
      not_measurable' s hs := setIntegral_eq_zero_of_not_measurableSet hs
      m_iUnion' s s_meas s_disj := hasSum_setIntegral_iUnion s_meas s_disj h.integrableOn }
  else 0

lemma withDensity_apply (hf : μ.Integrable f B) :
    μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ] := by
  simp [withDensity, hf]

lemma withDensity_apply_univ : μ.withDensity f B univ = ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hf : μ.Integrable f B
  · simp [withDensity_apply hf]
  · simp [withDensity, hf, integral_undef]

@[simp]
lemma withDensity_zero_vectorMeasure : (0 : VectorMeasure X F).withDensity f B = 0 := by
  ext s hs
  simp [withDensity_apply]

@[simp]
lemma withDensity_zero : μ.withDensity 0 B = 0 := by
  ext s hs
  simp [withDensity_apply]

lemma withDensity_congr (h : f =ᵐ[(μ.transpose B).variation] g) :
    μ.withDensity f B = μ.withDensity g B := by
  by_cases hf : μ.Integrable f B
  · simp only [withDensity, hf, ↓reduceDIte, Integrable.congr hf h, mk.injEq]
    ext s
    apply setIntegral_congr_ae
    filter_upwards [h] with x hx xs using hx
  · have : ¬(μ.Integrable g B) := by simpa [← integrable_congr h] using hf
    simp [withDensity, hf, this]

lemma restrict_withDensity (hf : μ.Integrable f B) :
    (μ.withDensity f B).restrict s = (μ.restrict s).withDensity f B := by
  by_cases hs : MeasurableSet s; swap
  · simp [restrict_not_measurable _ hs]
  · ext t ht
    simp only [hs, ht, restrict_apply]
    rw [withDensity_apply hf, withDensity_apply hf.restrict, restrict_restrict _ ht hs]

#check Finset.sum_sigma

lemma variation_withDensity (hf : μ.Integrable f B) :
    (μ.withDensity f B).variation = (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    rw [withDensity_apply hf, MeasureTheory.withDensity_apply _ hs]
    apply enorm_setIntegral_le_lintegral_enorm
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  rw [MeasureTheory.withDensity_apply _ hs]
  apply ENNReal.le_of_forall_pos_le_add
  rintro ε εpos -
  let δ := ε / 10
  have δpos : 0 < δ := div_pos εpos (by norm_num)
  obtain ⟨g, hg, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 (μ.transpose B).variation < δ
      ∧ MemLp (⇑g) 1 (μ.transpose B).variation :=
    (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt (by simp)
      (by simpa using δpos.ne')
  have I1 : ∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation
        ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := calc
    _ ≤ ∫⁻ a in s, ‖f a - g a‖ₑ + ‖g a‖ₑ ∂(μ.transpose B).variation := by
      gcongr with a
      nth_rw 1 [show f a = (f a - g a) + g a by abel]
      exact enorm_add_le (f a - g a) (g a)
    _ = ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation +
          ∫⁻ a in s, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by
      rw [lintegral_add_right, add_comm]
      exact g.stronglyMeasurable.enorm
    _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation +
          ∫⁻ a, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by
      gcongr
      exact Measure.restrict_le_self
    _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := by
      rw [eLpNorm_one_eq_lintegral_enorm] at hg
      gcongr
      exact hg.le
  have I2 : ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation =
      ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := calc
    _ = (g.map (‖·‖ₑ)).lintegral ((μ.transpose B).variation.restrict s) :=
      SimpleFunc.lintegral_eq_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * (μ.transpose B).variation.restrict s (g ⁻¹' {i}) :=
      SimpleFunc.map_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := by
      simp_rw [variation_restrict hs]
  obtain ⟨ρ,ρpos, hρ⟩ : ∃ ρ > 0, ∑ i ∈ g.range, ‖i‖ₑ * ρ ≤ δ := by
    refine ⟨δ * (∑ i ∈ g.range, ‖i‖ₑ)⁻¹, by simp [δpos], ?_⟩
    grw [← Finset.sum_mul, mul_comm (δ : ℝ≥0∞), ← mul_assoc, ENNReal.mul_inv_le_one, one_mul]
  have C i : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i})
      ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧
      ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
        ‖i‖ₑ * (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) := by
    rcases eq_or_ne i 0 with rfl | hi
    · exact ⟨∅, by simp⟩
    suffices ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i})
        ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧ (∀ t ∈ P, MeasurableSet t) ∧
        ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
        (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) by
      obtain ⟨P, hP, h'P, h''P, h'''P⟩ := this
      exact ⟨P, hP, h'P, h''P, by gcongr⟩
    apply exists_variation_le_add' _ (g.measurableSet_fiber i) ρpos
    rw [variation_restrict hs]
    exact (g.integrable_iff.1 (memLp_one_iff_integrable.1 gmem).restrict i hi).ne
  choose P Pg Pdisj Pmeas hP using C
  have I3 : ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤
      ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ := calc
    ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i})
    _ ≤ ∑ i ∈ g.range, ‖i‖ₑ * ((∑ p ∈ P i, ‖(μ.transpose B).restrict s p‖ₑ) + ρ) := by
      gcongr 1 with i hi
      exact hP i
    _ ≤ ∑ i ∈ g.range, ∑ p ∈ P i, ‖i‖ₑ * ‖(μ.transpose B).restrict s p‖ₑ + δ := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      gcongr
    _ = ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ := by
      rw [Finset.sum_sigma']
  have I4 : ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
      ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := calc
    ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, i.1 ∂[B; μ.restrict s]‖ₑ := by
      congr! with ⟨i, p⟩ hi
      rw [setIntegral_const]


    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, g x ∂[B; μ.restrict s]‖ₑ := by
      congr! with i hi
      sorry
    _ ≤ _ := sorry












end MeasureTheory.VectorMeasure
