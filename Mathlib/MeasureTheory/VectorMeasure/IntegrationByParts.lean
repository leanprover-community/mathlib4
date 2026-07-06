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

namespace BoundedVariationOn

variable {α E M : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [hα : MeasurableSpace α] [BorelSpace α]
  [NormedAddCommGroup E] [PseudoEMetricSpace M]

theorem stronglyMeasurable {f : α → M} (hf : BoundedVariationOn f univ) :
    StronglyMeasurable f :=
  StronglyMeasurable.of_countable_not_continuousAt hf.countable_not_continuousAt

theorem measurable [MeasurableSpace M] [BorelSpace M] {f : α → M} (hf : BoundedVariationOn f univ) :
    Measurable f :=
  hf.stronglyMeasurable.measurable

variable {μ : Measure α} {f : α → E}

theorem memLp_top (hf : BoundedVariationOn f univ) : MemLp f ∞ μ := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x⟩⟩
  · simp only [MemLp.of_discrete]
  apply memLp_top_of_bound hf.stronglyMeasurable.aestronglyMeasurable
    (‖f x‖ + (eVariationOn f univ).toReal)
  filter_upwards with y
  grw [← hf.dist_le (mem_univ x) (mem_univ y), dist_comm, dist_eq_norm_sub]
  exact norm_le_norm_add_norm_sub' (f y) (f x)

theorem memLp [IsFiniteMeasure μ] {p : ℝ≥0∞} (hf : BoundedVariationOn f univ) : MemLp f p μ :=
  hf.memLp_top.mono_exponent le_top

theorem integrable [IsFiniteMeasure μ] (hf : BoundedVariationOn f univ) : Integrable f μ :=
  memLp_one_iff_integrable.1 hf.memLp

variable {F G : Type*} [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

@[simp] lemma rightLim_bilinear_comp
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {f : α → E} {g : α → F}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (B : E →L[ℝ] F →L[ℝ] G) :
    (fun x ↦ B (f x) (g x)).rightLim = fun x ↦ B (f.rightLim x) (g.rightLim x) := by
  ext x
  rcases eq_or_neBot (𝓝[>] x) with hx | hx
  · simp [rightLim_eq_of_eq_bot _ hx]
  apply rightLim_eq_of_tendsto
  suffices H : Tendsto (fun x ↦ (f x, g x)) (𝓝[>] x) (𝓝 (f.rightLim x, g.rightLim x)) by
    have : Continuous (fun (p : E × F) ↦ B p.1 p.2) := by fun_prop
    apply (this.continuousAt (x := (f.rightLim x, g.rightLim x))).tendsto.comp H
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_rightLim _) (hg.tendsto_rightLim _)

@[simp] lemma leftLim_bilinear_comp
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {f : α → E} {g : α → F}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (B : E →L[ℝ] F →L[ℝ] G) :
    (fun x ↦ B (f x) (g x)).leftLim = fun x ↦ B (f.leftLim x) (g.leftLim x) := by
  ext x
  rcases eq_or_neBot (𝓝[<] x) with hx | hx
  · simp [leftLim_eq_of_eq_bot _ hx]
  apply leftLim_eq_of_tendsto
  suffices H : Tendsto (fun x ↦ (f x, g x)) (𝓝[<] x) (𝓝 (f.leftLim x, g.leftLim x)) by
    have : Continuous (fun (p : E × F) ↦ B p.1 p.2) := by fun_prop
    apply (this.continuousAt (x := (f.leftLim x, g.leftLim x))).tendsto.comp H
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_leftLim _) (hg.tendsto_leftLim _)

end BoundedVariationOn

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
theorem ext_of_Icc {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
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
lemma setIntegral_Icc_rightLim_sub_leftLim_eq
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
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

/-- Given bounded variation functions, the measure associated to their product is given by
`d (f * g) = f⁻ dg + g⁺ df`. Version for a general pairing instead of multiplication. -/
theorem _root_.BoundedVariationOn.vectorMeasure_bilinear_comp_eq
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) {B : E →L[ℝ] F →L[ℝ] G} :
    (hf.bilinear_comp hg B).vectorMeasure = hf.vectorMeasure.withDensity g.rightLim B.flip
      + hg.vectorMeasure.withDensity f.leftLim B := by
  apply VectorMeasure.ext_of_Icc _ _ (fun a b hab ↦ ?_)
  have := setIntegral_Icc_rightLim_sub_leftLim_eq  hf hg B a b
  rw [integral_fun_sub hg.rightLim.integrable (integrable_const _),
    integral_fun_sub (integrable_const _) hf.leftLim.integrable, sub_eq_iff_eq_add] at this
  rw [add_apply, withDensity_apply hg.rightLim.integrable, withDensity_apply hf.leftLim.integrable,
    this]
  simp [hab, hf, hg]
  abel

end MeasureTheory.VectorMeasure
