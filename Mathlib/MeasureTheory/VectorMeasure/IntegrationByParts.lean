/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Integration by parts for vector measures associated to bounded variation functions

-/


@[expose] public section

open Filter Set MeasureTheory MeasurableSpace MeasureTheory
open scoped Topology NNReal ENNReal

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {f : α → E} {g : α → F}

namespace MeasureTheory.VectorMeasure

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Two vector measures which agree on closed intervals are equal. -/
theorem VectorMeasure.ext_of_Icc {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α]
    (μ ν : VectorMeasure α E) (hμ : ∀ ⦃a b⦄, a ≤ b → μ (Icc a b) = ν (Icc a b)) : μ = ν := by
  rcases isEmpty_or_nonempty α with hα | hα
  · ext s hs
    have : s = ∅ := Subsingleton.elim _ _
    simp [this]
  apply VectorMeasure.ext_of_generateFrom _ _
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Icc α)) (isPiSystem_Icc id id); swap
  · rintro s ⟨l, u, hlu, rfl⟩
    exact hμ hlu
  obtain ⟨u, u_mono, hu⟩ : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop _
  obtain ⟨v, v_mono, hv⟩ : ∃ v : ℕ → α, Antitone v ∧ Tendsto v atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot _
  have : ⋃ n, Icc (v n) (u n) = univ := by
    apply eq_univ_iff_forall.2 (fun x ↦ ?_)
    simp only [mem_iUnion, mem_Icc]
    exact ((tendsto_atBot.1 hv x).and (tendsto_atTop.1 hu x)).exists
  rw [← this]
  have M : Monotone (fun n ↦ Icc (v n) (u n)) := by
    intro m n hmn x hx
    grind [Monotone, Antitone]
  apply tendsto_nhds_unique (VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat M (v := μ)
    (fun n ↦ measurableSet_Icc))
  have A a b : μ (Icc a b) = ν (Icc a b) := by
    rcases lt_or_ge b a with hab | hab
    · simp [hab]
    · exact hμ hab
  simp only [A]
  exact VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat M (fun n ↦ measurableSet_Icc)

omit [CompleteSpace G] in
lemma glouk (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (B : E →L[ℝ] F →L[ℝ] G) (a b : α) :
    ∫ᵛ x in Icc a b, g.rightLim x - g.leftLim a ∂[B.flip; hf.vectorMeasure]
      = ∫ᵛ y in Icc a b, f.rightLim b - f.leftLim y ∂[B; hg.vectorMeasure] := calc
  ∫ᵛ x in Icc a b, g.rightLim x - g.leftLim a ∂[B.flip; hf.vectorMeasure]
  _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, (Icc a x).indicator 1 y ∂•hg.vectorMeasure)
      ∂[B.flip; hf.vectorMeasure] := by
    apply setIntegral_congr_ae
    filter_upwards with x hx
    rw [setIntegral_indicator measurableSet_Icc measurableSet_Icc,
      show Icc a b ∩ Icc a x = Icc a x by grind]
    simp [hx.1]
  _ = ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Icc a x).indicator 1 y ∂•hf.vectorMeasure)
      ∂[B; hg.vectorMeasure] := by
    apply (integral_integral_smul_swap _).symm
    apply Integrable.of_bound _ 1
    · filter_upwards with ⟨x, y⟩
      simp only [indicator, mem_Icc, Pi.one_apply, Function.uncurry_apply_pair, Real.norm_eq_abs]
      grind
    · apply Measurable.aestronglyMeasurable
      simp only [indicator, mem_Icc, Pi.one_apply]
      apply Measurable.piecewise ?_ (by fun_prop) (by fun_prop)
      apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) (by fun_prop)
  _ = ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Icc y b).indicator 1 x ∂•hf.vectorMeasure)
      ∂[B; hg.vectorMeasure]:= by
    apply setIntegral_congr_ae
    filter_upwards with y hy
    apply setIntegral_congr_ae
    filter_upwards with x hx
    simp only [indicator, Pi.one_apply]
    grind
  _ = ∫ᵛ y in Icc a b, f.rightLim b - f.leftLim y ∂[B; hg.vectorMeasure] := by
    apply setIntegral_congr_ae
    filter_upwards with y hy
    rw [setIntegral_indicator measurableSet_Icc measurableSet_Icc,
      show Icc a b ∩ Icc y b = Icc y b by grind]
    simp [hy.2]

#check Continuous.stronglyMeasurable

#check Continuous.measurable

#check Measurable.dite

#check measurable_of_continuousOn_compl_singleton

#check measurable_of_measurable_on_compl_countable

#check ContinuousOn.measurable_of_countable_compl

lemma foo (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} :
    (hf.bilinear_comp hg B).vectorMeasure = hf.vectorMeasure.withDensity g.rightLim B.flip
      + hg.vectorMeasure.withDensity f.leftLim B := by
  apply VectorMeasure.ext_of_Icc _ _ (fun a b hab ↦ ?_)
  have := glouk hf hg B a b
  rw [integral_fun_sub] at this







#exit



  have I : Integrable (fun p ↦ (Icc a p.1).indicator (1 : α → ℝ) p.2)
      ((hg.vectorMeasure.restrict (Icc a b)).variation.prod
        (hf.vectorMeasure.restrict (Icc a b)).variation) := by
    apply Integrable.of_bound _ 1
    · filter_upwards with p
      grw [norm_indicator_le_norm_self]
      simp
    · apply Measurable.aestronglyMeasurable
      simp only [indicator, mem_Icc, Pi.one_apply]
      apply Measurable.piecewise ?_ (by fun_prop) (by fun_prop)
      apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) (by fun_prop)
  have J :  Integrable (fun p ↦ (Ioc p.1 b).indicator (1 : α → ℝ) p.2)
      ((hg.vectorMeasure.restrict (Icc a b)).variation.prod
        (hf.vectorMeasure.restrict (Icc a b)).variation) := by
    apply Integrable.of_bound _ 1
    · filter_upwards with p
      grw [norm_indicator_le_norm_self]
      simp
    · apply Measurable.aestronglyMeasurable
      simp only [indicator, mem_Ioc, Pi.one_apply]
      apply Measurable.piecewise ?_ (by fun_prop) (by fun_prop)
      apply MeasurableSet.inter
      · exact measurableSet_lt (by fun_prop) (by fun_prop)
      · exact measurableSet_le (by fun_prop) (by fun_prop)
  have : B (f.rightLim b - f.leftLim a) (g.rightLim b - g.leftLim a) = 0 := calc
    B (f.rightLim b - f.leftLim a) (g.rightLim b - g.leftLim a)
    _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, 1 ∂•hf.vectorMeasure) ∂[B; hg.vectorMeasure] := by
      rw [VectorMeasure.setIntegral_const]
      simp [hab]
    _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a x, 1 ∂•hf.vectorMeasure
        + ∫ᵛ y in Ioc x b, 1 ∂•hf.vectorMeasure) ∂[B; hg.vectorMeasure] := by
      apply setIntegral_congr_ae
      filter_upwards with x hx
      rw [show Icc a b = Icc a x ∪ Ioc x b by grind, setIntegral_union (by grind)
        measurableSet_Icc measurableSet_Ioc (integrable_const _) (integrable_const _)]
    _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, (Icc a x).indicator 1 y ∂•hf.vectorMeasure
        + ∫ᵛ y in Icc a b, (Ioc x b).indicator 1 y ∂•hf.vectorMeasure) ∂[B; hg.vectorMeasure] := by
      apply setIntegral_congr_ae
      filter_upwards with x hx
      rw [setIntegral_indicator measurableSet_Icc measurableSet_Ioc,
        setIntegral_indicator measurableSet_Icc measurableSet_Icc]
      congr <;> grind
    _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, (Icc a x).indicator 1 y ∂•hf.vectorMeasure)
          ∂[B; hg.vectorMeasure]
        + ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, (Ioc x b).indicator 1 y ∂•hf.vectorMeasure)
          ∂[B; hg.vectorMeasure] := by
      rw [integral_fun_add]
      · exact Integrable.integral_vectorMeasure_prod_left I
      · exact Integrable.integral_vectorMeasure_prod_left J
    _ = ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Icc a x).indicator 1 y ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure]
        + ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Ioc x b).indicator 1 y ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure] := by
      congr 1
      · apply (integral_integral_smul_swap _).symm
        exact I.swap
      · apply (integral_integral_smul_swap _).symm
        exact J.swap
    _ = ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Icc y b).indicator 1 x ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure]
        + ∫ᵛ y in Icc a b, (∫ᵛ x in Icc a b, (Ico a y).indicator 1 x ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure] := by
      congr 1
      · apply setIntegral_congr_ae
        filter_upwards with y hy
        apply setIntegral_congr_ae
        filter_upwards with x hx
        simp only [indicator, Pi.one_apply]
        grind
      · apply setIntegral_congr_ae
        filter_upwards with y hy
        apply setIntegral_congr_ae
        filter_upwards with x hx
        simp only [indicator, Pi.one_apply]
        grind
    _ = ∫ᵛ y in Icc a b, (∫ᵛ x in Icc y b, 1 ∂•hg.vectorMeasure) ∂[B.flip; hf.vectorMeasure]
        + ∫ᵛ y in Icc a b, (∫ᵛ x in Ico a y, 1 ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure] := by
      congr 1
      · apply setIntegral_congr_ae
        filter_upwards with y hy
        rw [setIntegral_indicator measurableSet_Icc measurableSet_Icc]
        congr 2
        grind
      · apply setIntegral_congr_ae
        filter_upwards with y hy
        rw [setIntegral_indicator measurableSet_Icc measurableSet_Ico]
        congr 2
        grind
    _ = ∫ᵛ y in Icc a b, (g.rightLim b - g.leftLim y) ∂[B.flip; hf.vectorMeasure]
        + ∫ᵛ y in Icc a b, (∫ᵛ x in Ico a y, 1 ∂•hg.vectorMeasure)
          ∂[B.flip; hf.vectorMeasure] := by











    _ = 0 := sorry





end MeasureTheory
