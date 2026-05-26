/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Vector measure with density with respect to a vector measure

-/

open Set Filter
open scoped Topology ENNReal

@[expose] public section

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

lemma variation_WithDensity_le :
    (μ.withDensity f B).variation ≤ (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  by_cases hf : μ.Integrable f B
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    rw [withDensity_apply hf, MeasureTheory.withDensity_apply _ hs]
    apply enorm_setIntegral_le_lintegral_enorm
  · simp [withDensity, hf, Measure.zero_le ]

/-- If `‖B x y‖ = ‖B · y‖ * ‖x‖` for all `x, y`, then the variation of a vector measure with
density `f` wrt `μ` is the measure with density `‖f‖ₑ` with respect to the variation of `μ`.

The condition on `B` is necessary: for a counterexample without it, let `B` be the scalar
product in `ℝ²` and `f x` everywhere horizontal and `μ s` everywhere vertical.
Then `μ.withDensity f B = 0` so its variation is zero, while the integral of `‖f‖ₑ` is not.
-/
lemma variation_withDensity [CompleteSpace G]
    (hf : μ.Integrable f B) (hB : ∀ x y, ‖B x y‖₊ = ‖B.flip y‖₊ * ‖x‖₊) :
    (μ.withDensity f B).variation = (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  apply le_antisymm variation_WithDensity_le
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  /- For the nontrivial direction, we have to show that for each measurable set `s`,
  `∫⁻ (a : X) in s, ‖f a‖ₑ ∂(μ.transpose B).variation ≤ (μ.withDensity f B).variation s`.
  As the variation is a supremum over finite partitions, we need to exhibit a partition. For this,
  we approximate `f` by a simple function `g`. Then the left term is approximately
  `∑ i, ‖g i‖ₑ * (μ.transpose B).variation (g ⁻¹' {i})`.
  By definition, the variation of `g ⁻¹' {i}` is close to a sum `∑ j, ‖(μ.transpose B) Pᵢⱼ‖ₑ` over
  a partition `Pᵢⱼ` of `g ⁻¹' {i}`. Putting all these together, one gets the desired
  partition of `s`, for which `∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation` is close to
  `∑ i j, ‖∫ x in Pᵢⱼ, f x ∂[B; μ]‖ₑ`, i.e., `∑ i j, ‖(μ.withDensity f B) Pᵢⱼ‖ₑ`. The latter sum
  is bounded by `(μ.withDensity f B).variation s` as desired. -/
  rw [MeasureTheory.withDensity_apply _ hs]
  apply ENNReal.le_of_forall_pos_le_add
  rintro ε εpos -
  let δ := ε / 3
  have δpos : 0 < δ := div_pos εpos (by norm_num)
  -- first step: approximate `f` by a simple function `g`.
  obtain ⟨g, hg, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 (μ.transpose B).variation < δ
      ∧ MemLp (⇑g) 1 (μ.transpose B).variation :=
    (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt (by simp)
      (by simpa using δpos.ne')
  -- the integral of `‖f‖ₑ` is approximated up to `δ` by that of `‖g‖ₑ`.
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
  -- the integral of `‖g‖ₑ` can be rewritten as a weighted sum of measures, as `g` is a simple
  -- function.
  have I2 : ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation =
      ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := calc
    _ = (g.map (‖·‖ₑ)).lintegral ((μ.transpose B).variation.restrict s) :=
      SimpleFunc.lintegral_eq_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * (μ.transpose B).variation.restrict s (g ⁻¹' {i}) :=
      SimpleFunc.map_lintegral _ _
    _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := by
      simp_rw [variation_restrict hs]
  -- For each `i`, choose a partition `P i` of `g ⁻¹' {i}` such that the sum of the enorms
  -- of their measures approximates well enough the variation, by definition of the variation.
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
  -- rewrite everything in terms of the global partition made by putting together the `Pᵢ`,
  -- and register that the resulting error is bounded by `δ`.
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
  -- in the above sum, replace the values of `g` by `f`, as these two functions are close
  -- in `L^1` norm.
  have I4 : ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
      ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := calc
    ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, i.1 ∂[B; μ.restrict s]‖ₑ := by
      congr! with ⟨i, p⟩ hi
      rcases eq_or_ne i 0 with rfl | h'i
      · simp
      simp only [Finset.mem_sigma] at hi
      have pmeas : MeasurableSet p := Pmeas i _ hi.2
      have : IsFiniteMeasure (((μ.restrict s).restrict p).transpose B).variation := by
        constructor
        rw [restrict_restrict _ pmeas hs, transpose_restrict, variation_restrict (pmeas.inter hs),
          MeasureTheory.Measure.restrict_apply_univ]
        apply lt_of_le_of_lt ?_ (g.integrable_iff.1 (memLp_one_iff_integrable.1 gmem) i h'i)
        exact measure_mono (inter_subset_left.trans (Pg i _ hi.2))
      rw [setIntegral_const, restrict_apply _ hs pmeas, restrict_apply _ hs pmeas]
      simp [transpose, hB, enorm_eq_nnnorm, mul_comm]
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, g x ∂[B; μ.restrict s]‖ₑ := by
      congr! 2 with ⟨i, p⟩ hi
      simp only [Finset.mem_sigma] at hi
      apply setIntegral_congr_ae
      filter_upwards with x hx using (Pg i _ hi.2 hx).symm
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) + f x ∂[B; μ.restrict s]‖ₑ := by simp
    _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]
          + ∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      congr! with i hi
      rw [integral_fun_add]
      · apply Integrable.restrict
        apply Integrable.restrict
        apply Integrable.sub (memLp_one_iff_integrable.1 gmem) hf
      · apply hf.restrict.restrict
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]‖ₑ
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      rw [← Finset.sum_add_distrib]
      gcongr with i hi
      apply enorm_add_le
    _ ≤ ∑ i ∈ g.range.sigma P, ∫⁻ x in i.2, ‖g x - f x‖ₑ ∂(μ.transpose B).variation
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      gcongr with i hi
      grw [enorm_setIntegral_le_lintegral_enorm]
      apply lintegral_mono' _ le_rfl
      apply Measure.restrict_mono le_rfl
      rw [transpose_restrict, variation_restrict hs]
      apply Measure.restrict_le_self
    _ = ∫⁻ x in (⋃ i ∈ g.range.sigma P, i.2), ‖g x - f x‖ₑ ∂(μ.transpose B).variation
        + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by
      rw [lintegral_biUnion_finset]
      · rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq
        simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range,
          SetLike.mem_coe] at hi hj
        rcases eq_or_ne i j with rfl | hij
        · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
          exact Pdisj i hi.2 hj.2 hijpq
        · have : Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by grind
          exact this.mono (Pg i p hi.2) (Pg j q hj.2)
      · rintro ⟨i, p⟩ hip
        simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hip
        exact Pmeas i p hip.2
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ +
        ∫⁻ x, ‖g x - f x‖ₑ ∂(μ.transpose B).variation := by
      rw [add_comm]
      gcongr
      apply Measure.restrict_le_self
    _ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := by
      gcongr
      simp_rw [enorm_sub_rev, ← eLpNorm_one_eq_lintegral_enorm]
      exact hg.le
  -- register that the sum of the enorms of the integrals of `f` over the pieces `Pᵢⱼ` of the
  -- partition is bounded by the variation of `μ.withDensity f B`, by definition of the variation.
  have I5 : ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ
      ≤ (μ.withDensity f B).variation s := by
    let Q : Finset (Set X) := (g.range.sigma P).image (fun p ↦ p.2 ∩ s)
    calc ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ
    _ = ∑ j ∈ Q, ‖∫ᵛ x in j, f x ∂[B; μ]‖ₑ := by
      simp only [Q]
      rw [Finset.sum_image_of_pairwise_eq_zero]; swap
      · rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq h'ij
        simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range,
          SetLike.mem_coe] at hi hj
        suffices H : Disjoint p q by
          have : Disjoint (p ∩ s) (q ∩ s) := H.mono inter_subset_left inter_subset_left
          rw [← h'ij, disjoint_self] at this
          simp [this]
        rcases eq_or_ne i j with rfl | hij
        · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
          exact Pdisj i hi.2 hj.2 hijpq
        · have : Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by grind
          exact this.mono (Pg i p hi.2) (Pg j q hj.2)
      apply Finset.sum_congr rfl
      rintro ⟨i, p⟩ hi
      simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hi
      rw [restrict_restrict _ (Pmeas i p hi.2) hs]
    _ = ∑ j ∈ Q, ‖μ.withDensity f B j‖ₑ :=
      Finset.sum_congr rfl (fun t ht ↦ by rw [withDensity_apply hf])
    _ ≤ (μ.withDensity f B).variation s := by
      apply le_variation _ hs
      · intro t ht
        simp only [Finset.mem_image, Finset.mem_sigma, SimpleFunc.mem_range, mem_range,
          Sigma.exists, ↓existsAndEq, true_and, exists_and_right, Q] at ht
        rcases ht with ⟨p, -, rfl⟩
        exact inter_subset_right
      · intro t ht u hu htu
        simp only [Finset.coe_image, Finset.coe_sigma, SimpleFunc.coe_range, mem_image,
          mem_sigma_iff, mem_range, SetLike.mem_coe, Sigma.exists, ↓existsAndEq, true_and,
          exists_and_right, Q] at ht hu
        rcases ht with ⟨p, ⟨i, hi⟩, rfl⟩
        rcases hu with ⟨q, ⟨j, hj⟩, rfl⟩
        have hpq : p ≠ q := by grind only
        suffices H : Disjoint p q from H.mono inter_subset_left inter_subset_left
        rcases eq_or_ne (g i) (g j) with hij | hij
        · rw [← hij] at hj
          exact Pdisj (g i) hi hj hpq
        · have : Disjoint (g ⁻¹' {g i}) (g ⁻¹' {g j}) := by grind
          exact this.mono (Pg (g i) p hi) (Pg (g j) q hj)
  -- finally, put together the above inequalities, and argue that the overall error `3δ` is
  -- bounded by `ε` by design.
  calc ∫⁻ (a : X) in s, ‖f a‖ₑ ∂(μ.transpose B).variation
  _ ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := I1
  _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) + δ := by rw [I2]
  _ ≤ (∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ) + δ := by gcongr
  _ ≤ ((∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ) + δ) + δ := by gcongr
  _ = (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + 3 * δ := by ring
  _ ≤ (μ.withDensity f B).variation s + 3 * δ := by gcongr
  _ ≤ (μ.withDensity f B).variation s + ε := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat, δ]
    rw [ENNReal.mul_div_cancel (by simp) (by simp)]

#where

lemma variation_withDensityᵥ {μ : Measure X} {f : X → E} (hf : Integrable f μ) :
    (μ.withDensityᵥ f).variation = μ.withDensity (fun x ↦ ‖f x‖ₑ) := by
  have : μ.withDensityᵥ f = (μ.withDensity (‖f ·‖ₑ)).withDensityᵥ (fun x ↦ ‖f x‖⁻¹ • f x) := by
    ext s hs
    rw [withDensityᵥ_apply hf hs, withDensityᵥ_apply _ hs]; swap
    · have : IsFiniteMeasure (μ.withDensity fun x ↦ ‖f x‖ₑ) := ⟨by simpa using hf.2⟩
      apply Integrable.of_bound (C := 1)
      · have W := hf.aestronglyMeasurable.norm.inv



end MeasureTheory.VectorMeasure
