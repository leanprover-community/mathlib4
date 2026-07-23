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

Consider two bounded variation functions `f` and `g`. We give several versions of the
integration by parts formula `∫_a^b f dg = f b * g b - f a * g a - ∫_a^b g df`.
Note that the formula as written is wrong in case of discontinuities : one should use left limits
and right limits, and pay attention as to whether `a` and `b` are included in the integrals.
Therefore, we give 4 versions, on `Icc` and `Ioc` and `Ico` and `Ioo`. They all follow
from a formula on a general set `s`, where the boundary contribution is the integral on `s`
of the vector measure associated to the bounded variation function `fg`.

## Main results

* `vectorMeasure_bilinear_comp_eq` states that `d(fg) = g⁺ df + f⁻ dg`, for a general pairing
  function
* `integral_Icc_leftLim_vectorMeasure_eq_sub` gives the equality
  `∫_[a, b] f⁻ dg = f⁺ b * g⁺ b - f⁻ a * g⁻ a - ∫_[a, b] g⁺ df`, for a general pairing function.
* There are also versions for `Ioc` and `Ico` and `Ioo`.
* There are also versions where the pairing is scalar multiplication. For instance, the `Icc`
  version is `integral_Icc_leftLim_smul_vectorMeasure_eq_sub`.
* There are versions of all the previous statements using `f⁺` and `g⁻` instead. The names
  are the same, modulo the replacement of `leftLim` with `rightLim`.

-/


@[expose] public section

open Filter Set MeasureTheory MeasurableSpace VectorMeasure
open scoped Topology NNReal ENNReal

namespace BoundedVariationOn

variable {α E F G M : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [hα : MeasurableSpace α] [BorelSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [PseudoEMetricSpace M]

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

/-- Two vector measures which agree on closed intervals are equal. -/
theorem _root_.MeasureTheory.VectorMeasure.ext_of_Icc
    {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
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

variable [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedSpace ℝ G]

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

variable [DenselyOrdered α] [CompactIccSpace α] {f : α → E} {g : α → F}

lemma setIntegral_Icc_rightLim_sub_leftLim_eq
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (B : E →L[ℝ] F →L[ℝ] G) (a b : α) :
    ∫ᵛ x in Icc a b, g.rightLim x - g.leftLim a ∂[B.flip; hf.vectorMeasure]
      = ∫ᵛ y in Icc a b, f.rightLim b - f.leftLim y ∂[B; hg.vectorMeasure] := calc
  ∫ᵛ x in Icc a b, g.rightLim x - g.leftLim a ∂[B.flip; hf.vectorMeasure]
  _ = ∫ᵛ x in Icc a b, (∫ᵛ y in Icc a b, (Icc a x).indicator 1 y ∂•hg.vectorMeasure)
      ∂[B.flip; hf.vectorMeasure] := by
    apply VectorMeasure.setIntegral_congr_ae
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
    apply VectorMeasure.setIntegral_congr_ae
    filter_upwards with y hy
    apply VectorMeasure.setIntegral_congr_ae
    filter_upwards with x hx
    simp only [indicator, Pi.one_apply]
    grind
  _ = ∫ᵛ y in Icc a b, f.rightLim b - f.leftLim y ∂[B; hg.vectorMeasure] := by
    apply VectorMeasure.setIntegral_congr_ae
    filter_upwards with y hy
    rw [setIntegral_indicator measurableSet_Icc measurableSet_Icc,
      show Icc a b ∩ Icc y b = Icc y b by grind]
    simp [hy.2]

variable [CompleteSpace G]

/-- Given bounded variation functions, the measure associated to their product is given by
`d (f * g) = f⁻ dg + g⁺ df`. Version for a general pairing instead of multiplication.
This is the most general version of the integration by parts formula for vector measures. -/
theorem vectorMeasure_bilinear_comp_eq
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) {B : E →L[ℝ] F →L[ℝ] G} :
    (hf.bilinear_comp hg B).vectorMeasure = hf.vectorMeasure.withDensity g.rightLim B.flip
      + hg.vectorMeasure.withDensity f.leftLim B := by
  apply VectorMeasure.ext_of_Icc _ _ (fun a b hab ↦ ?_)
  have := setIntegral_Icc_rightLim_sub_leftLim_eq  hf hg B a b
  rw [integral_fun_sub hg.rightLim.integrable (integrable_const _),
    integral_fun_sub (integrable_const _) hf.leftLim.integrable, sub_eq_iff_eq_add] at this
  rw [add_apply, VectorMeasure.withDensity_apply hg.rightLim.integrable,
    VectorMeasure.withDensity_apply hf.leftLim.integrable, this]
  simp [hab, hf, hg]
  abel

/-- Given bounded variation functions, the measure associated to their product is given by
`d (f * g) = f⁺ dg + g⁻ df`. Version for a general pairing instead of multiplication.
This is the most general version of the integration by parts formula for vector measures. -/
theorem vectorMeasure_bilinear_comp_eq'
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) {B : E →L[ℝ] F →L[ℝ] G} :
    (hf.bilinear_comp hg B).vectorMeasure = hf.vectorMeasure.withDensity g.leftLim B.flip
      + hg.vectorMeasure.withDensity f.rightLim B := by
  have : (hf.bilinear_comp hg B).vectorMeasure = (hg.bilinear_comp hf B.flip).vectorMeasure :=
    ext_of_Icc _ _ (fun a b hab ↦ by simp [hab])
  rw [this, hg.vectorMeasure_bilinear_comp_eq hf, add_comm]
  rw [ContinuousLinearMap.flip_flip]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version with a general pairing function `B`, and over a general integration set `s`. -/
theorem integral_leftLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {s : Set α} :
    ∫ᵛ x in s, f.leftLim x ∂[B; hg.vectorMeasure] = (hf.bilinear_comp hg B).vectorMeasure s
      - ∫ᵛ x in s, g.rightLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.vectorMeasure_bilinear_comp_eq hg]
  simp [VectorMeasure.withDensity_apply, hf.leftLim.integrable, hg.rightLim.integrable]

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version with a general pairing function `B`, and over a general integration set `s`. -/
theorem integral_rightLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {s : Set α} :
    ∫ᵛ x in s, f.rightLim x ∂[B; hg.vectorMeasure] = (hf.bilinear_comp hg B).vectorMeasure s
      - ∫ᵛ x in s, g.leftLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.vectorMeasure_bilinear_comp_eq' hg]
  simp [VectorMeasure.withDensity_apply, hf.rightLim.integrable, hg.leftLim.integrable]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version with a general pairing function `B`, over an interval `[a, b]`. -/
theorem integral_Icc_leftLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Icc a b, f.leftLim x ∂[B; hg.vectorMeasure] =
      B (f.rightLim b) (g.rightLim b) - B (f.leftLim a) (g.leftLim a)
      - ∫ᵛ x in Icc a b, g.rightLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_leftLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version with a general pairing function `B`, over an interval `[a, b]`. -/
theorem integral_Icc_rightLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Icc a b, f.rightLim x ∂[B; hg.vectorMeasure] =
      B (f.rightLim b) (g.rightLim b) - B (f.leftLim a) (g.leftLim a)
      - ∫ᵛ x in Icc a b, g.leftLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_rightLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version with a general pairing function `B`, over an interval `(a, b]`. -/
theorem integral_Ioc_leftLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ioc a b, f.leftLim x ∂[B; hg.vectorMeasure] =
      B (f.rightLim b) (g.rightLim b) - B (f.rightLim a) (g.rightLim a)
      - ∫ᵛ x in Ioc a b, g.rightLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_leftLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version with a general pairing function `B`, over an interval `(a, b]`. -/
theorem integral_Ioc_rightLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ioc a b, f.rightLim x ∂[B; hg.vectorMeasure] =
      B (f.rightLim b) (g.rightLim b) - B (f.rightLim a) (g.rightLim a)
      - ∫ᵛ x in Ioc a b, g.leftLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_rightLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version with a general pairing function `B`, over an interval `[a, b)`. -/
theorem integral_Ico_leftLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ico a b, f.leftLim x ∂[B; hg.vectorMeasure] =
      B (f.leftLim b) (g.leftLim b) - B (f.leftLim a) (g.leftLim a)
      - ∫ᵛ x in Ico a b, g.rightLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_leftLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version with a general pairing function `B`, over an interval `[a, b)`. -/
theorem integral_Ico_rightLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ico a b, f.rightLim x ∂[B; hg.vectorMeasure] =
      B (f.leftLim b) (g.leftLim b) - B (f.leftLim a) (g.leftLim a)
      - ∫ᵛ x in Ico a b, g.leftLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_rightLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version with a general pairing function `B`, over an interval `(a, b)`. -/
theorem integral_Ioo_leftLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a < b) :
    ∫ᵛ x in Ioo a b, f.leftLim x ∂[B; hg.vectorMeasure] =
      B (f.leftLim b) (g.leftLim b) - B (f.rightLim a) (g.rightLim a)
      - ∫ᵛ x in Ioo a b, g.rightLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_leftLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version with a general pairing function `B`, over an interval `(a, b)`. -/
theorem integral_Ioo_rightLim_vectorMeasure_eq_sub
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} {a b : α} (hab : a < b) :
    ∫ᵛ x in Ioo a b, f.rightLim x ∂[B; hg.vectorMeasure] =
      B (f.leftLim b) (g.leftLim b) - B (f.rightLim a) (g.rightLim a)
      - ∫ᵛ x in Ioo a b, g.leftLim x ∂[B.flip; hf.vectorMeasure] := by
  rw [hf.integral_rightLim_vectorMeasure_eq_sub hg]
  simp [hab, hf, hg]

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version for scalar multiplication, over an interval `[a, b]`. -/
theorem integral_Icc_leftLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Icc a b, f.leftLim x ∂•hg.vectorMeasure =
      f.rightLim b • g.rightLim b - f.leftLim a • g.leftLim a
      - ∫ᵛ x in Icc a b, g.rightLim x ∂<• hf.vectorMeasure :=
  integral_Icc_leftLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version for scalar multiplication, over an interval `[a, b]`. -/
theorem integral_Icc_rightLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Icc a b, f.rightLim x ∂•hg.vectorMeasure =
      f.rightLim b • g.rightLim b - f.leftLim a • g.leftLim a
      - ∫ᵛ x in Icc a b, g.leftLim x ∂<• hf.vectorMeasure :=
  integral_Icc_rightLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version for scalar multiplication, over an interval `(a, b]`. -/
theorem integral_Ioc_leftLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ioc a b, f.leftLim x ∂• hg.vectorMeasure =
      f.rightLim b • g.rightLim b - f.rightLim a • g.rightLim a
      - ∫ᵛ x in Ioc a b, g.rightLim x ∂<• hf.vectorMeasure :=
  integral_Ioc_leftLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version for scalar multiplication, over an interval `(a, b]`. -/
theorem integral_Ioc_rightLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ioc a b, f.rightLim x ∂• hg.vectorMeasure =
      f.rightLim b • g.rightLim b - f.rightLim a • g.rightLim a
      - ∫ᵛ x in Ioc a b, g.leftLim x ∂<• hf.vectorMeasure :=
  integral_Ioc_rightLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version for scalar multiplication, over an interval `[a, b)`. -/
theorem integral_Ico_leftLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ico a b, f.leftLim x ∂• hg.vectorMeasure =
      f.leftLim b • g.leftLim b - f.leftLim a • g.leftLim a
      - ∫ᵛ x in Ico a b, g.rightLim x ∂<• hf.vectorMeasure :=
  integral_Ico_leftLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version for scalar multiplication, over an interval `[a, b)`. -/
theorem integral_Ico_rightLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a ≤ b) :
    ∫ᵛ x in Ico a b, f.rightLim x ∂• hg.vectorMeasure =
      f.leftLim b • g.leftLim b - f.leftLim a • g.leftLim a
      - ∫ᵛ x in Ico a b, g.leftLim x ∂<• hf.vectorMeasure :=
  integral_Ico_rightLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.leftLim dg` and `g.rightLim df`.
Version for scalar multiplication, over an interval `(a, b)`. -/
theorem integral_Ioo_leftLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a < b) :
    ∫ᵛ x in Ioo a b, f.leftLim x ∂• hg.vectorMeasure =
      f.leftLim b • g.leftLim b - f.rightLim a • g.rightLim a
      - ∫ᵛ x in Ioo a b, g.rightLim x ∂<• hf.vectorMeasure :=
  integral_Ioo_leftLim_vectorMeasure_eq_sub hf hg hab

/-- *Integration by parts* for Stieltjes vector measure, between `f.rightLim dg` and `g.leftLim df`.
Version for scalar multiplication, over an interval `(a, b)`. -/
theorem integral_Ioo_rightLim_smul_vectorMeasure_eq_sub {f : α → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {a b : α} (hab : a < b) :
    ∫ᵛ x in Ioo a b, f.rightLim x ∂• hg.vectorMeasure =
      f.leftLim b • g.leftLim b - f.rightLim a • g.rightLim a
      - ∫ᵛ x in Ioo a b, g.leftLim x ∂<• hf.vectorMeasure :=
  integral_Ioo_rightLim_vectorMeasure_eq_sub hf hg hab

end BoundedVariationOn
