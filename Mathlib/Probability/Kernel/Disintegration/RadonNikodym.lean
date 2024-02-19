/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.KernelCDFReal
import Mathlib.Probability.Kernel.WithDensity

/-!
# Density

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

section aux

lemma MeasurableEmbedding.comap_add {β : Type*} {mβ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) {μ ν : Measure β} :
    (μ + ν).comap f = μ.comap f + ν.comap f := by
  ext s hs
  rw [← Measure.comapₗ_eq_comap _ hf.injective (fun s hs ↦ hf.measurableSet_image.mpr hs) _ hs,
    map_add]
  simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply]
  rw [← Measure.comapₗ_eq_comap _ hf.injective (fun s hs ↦ hf.measurableSet_image.mpr hs) _ hs,
    ← Measure.comapₗ_eq_comap _ hf.injective (fun s hs ↦ hf.measurableSet_image.mpr hs) _ hs]

@[simp]
lemma kernel.map_id {β : Type*} {_ : MeasurableSpace β} {κ : kernel α β} :
    kernel.map κ id measurable_id = κ := by ext a; rw [kernel.map_apply]; simp

@[simp]
lemma kernel.map_id' {β : Type*} {_ : MeasurableSpace β} {κ : kernel α β} :
    kernel.map κ (fun a ↦ a) measurable_id = κ := kernel.map_id

end aux

section withDensity

variable {β : Type*} {mβ : MeasurableSpace β} {κ : kernel α β}

@[simp]
lemma Measure.absolutelyContinuous_zero (μ : Measure α) : 0 ≪ μ :=
  Measure.absolutelyContinuous_of_le (Measure.zero_le μ)

nonrec lemma kernel.withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α → β → ℝ≥0∞) (a : α) :
    kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp

@[simp]
lemma kernel.withDensity_one [IsSFiniteKernel κ] :
    kernel.withDensity κ 1 = κ := by
  ext a
  rw [kernel.withDensity_apply _ measurable_const]
  simp

@[simp]
lemma kernel.withDensity_one' [IsSFiniteKernel κ] :
    kernel.withDensity κ (fun _ _ ↦ 1) = κ := kernel.withDensity_one

lemma kernel.withDensity_sub_add [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hg_int : ∀ a, ∫⁻ x, g a x ∂(κ a) ≠ ∞) (hfg : ∀ a, g a ≤ᵐ[κ a] f a) :
    kernel.withDensity κ (fun a x ↦ f a x - g a x) + kernel.withDensity κ g
      = kernel.withDensity κ f := by
  ext a s
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
  rw [kernel.withDensity_apply' _ hf, kernel.withDensity_apply' _ hg, kernel.withDensity_apply']
  swap; · exact hf.sub hg
  rw [lintegral_sub]
  · rw [tsub_add_cancel_iff_le]
    exact lintegral_mono_ae (ae_restrict_of_ae (hfg a))
  · exact hg.comp measurable_prod_mk_left
  · exact ((set_lintegral_le_lintegral _ _).trans_lt (hg_int a).lt_top).ne
  · exact ae_restrict_of_ae (hfg a)

nonrec lemma kernel.withDensity_mul [IsSFiniteKernel κ] {f : α → β → ℝ≥0} {g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    kernel.withDensity κ (fun a x ↦ f a x * g a x)
      = kernel.withDensity (kernel.withDensity κ fun a x ↦ f a x) fun a x ↦ g a x := by
  ext a : 1
  rw [kernel.withDensity_apply]
  swap; · exact (measurable_coe_nnreal_ennreal.comp hf).mul hg
  suffices (Measure.withDensity (κ a) ((fun x ↦ (f a x : ℝ≥0∞)) * (fun x ↦ (g a x : ℝ≥0∞)))) =
      (withDensity (withDensity κ fun a x ↦ f a x) fun a x ↦ g a x) a by
    convert this
  rw [withDensity_mul]
  · rw [kernel.withDensity_apply _ hg, kernel.withDensity_apply]
    exact measurable_coe_nnreal_ennreal.comp hf
  · rw [measurable_coe_nnreal_ennreal_iff]
    exact hf.comp measurable_prod_mk_left
  · exact hg.comp measurable_prod_mk_left

end withDensity

section Real

variable {κ ν : kernel α ℝ}

lemma fst_map_le_of_le (hκν : κ ≤ ν) :
    kernel.fst (kernel.map κ (fun a ↦ (a, ()))
      (@measurable_prod_mk_right ℝ Unit _ inferInstance _)) ≤ ν := by
  rwa [kernel.fst_map_prod _ measurable_id' measurable_const, kernel.map_id']

lemma todo (κ : kernel α ℝ) (ν : kernel α ℝ) : κ ≤ κ + ν := by
  -- todo improve this: `le_add_of_nonneg_right` should work on kernels
  intro a
  simp only [AddSubmonoid.coe_add, Pi.add_apply]
  exact le_add_of_nonneg_right (Measure.zero_le (ν a))

noncomputable
def g (κ ν : kernel α ℝ) (a : α) (x : ℝ) : ℝ :=
  MLimsup (kernel.map κ (fun a ↦ (a, ()))
    (@measurable_prod_mk_right ℝ Unit _ inferInstance _)) ν a x univ

lemma g_nonneg (hκν : κ ≤ ν) {a : α} {x : ℝ} : 0 ≤ g κ ν a x :=
  mLimsup_nonneg (fst_map_le_of_le hκν) _ _ _

lemma g_le_one (hκν : κ ≤ ν) {a : α} {x : ℝ} : g κ ν a x ≤ 1 :=
  mLimsup_le_one (fst_map_le_of_le hκν) _ _ _

lemma measurable_g (κ : kernel α ℝ) (ν : kernel α ℝ) :
    Measurable (fun p : α × ℝ ↦ g κ ν p.1 p.2) :=
  measurable_mLimsup _ ν MeasurableSet.univ

lemma measurable_g_right (κ : kernel α ℝ) (ν : kernel α ℝ) (a : α) :
    Measurable (fun x : ℝ ↦ g κ ν a x) := by
  change Measurable ((fun p : α × ℝ ↦ g κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_g _ _).comp measurable_prod_mk_left

noncomputable
def kernel.rnDerivReal (κ ν : kernel α ℝ) (a : α) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (g κ (κ + ν) a x) / ENNReal.ofReal (1 - g κ (κ + ν) a x)

lemma kernel.rnDerivReal_def (κ ν : kernel α ℝ) :
    kernel.rnDerivReal κ ν
      = fun a x ↦ ENNReal.ofReal (g κ (κ + ν) a x) / ENNReal.ofReal (1 - g κ (κ + ν) a x) := rfl

lemma measurable_rnDerivReal : Measurable (fun p : α × ℝ ↦ kernel.rnDerivReal κ ν p.1 p.2) :=
  (measurable_g κ _).ennreal_ofReal.div (measurable_const.sub (measurable_g κ _)).ennreal_ofReal

lemma measurable_rnDerivReal_right (κ ν : kernel α ℝ) (a : α) :
    Measurable (fun x : ℝ ↦ kernel.rnDerivReal κ ν a x) := by
  change Measurable ((fun p : α × ℝ ↦ kernel.rnDerivReal κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact measurable_rnDerivReal.comp measurable_prod_mk_left

lemma withDensity_g (κ ν : kernel α ℝ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (g κ (κ + ν) a x)) = κ := by
  have h_le : κ ≤ κ + ν := todo κ ν
  ext a s hs
  rw [kernel.withDensity_apply']
  swap; exact (measurable_g _ _).ennreal_ofReal
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · unfold g
    rw [set_integral_mLimsup (fst_map_le_of_le h_le) a MeasurableSet.univ hs,
      ENNReal.ofReal_toReal, kernel.map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
    · congr with x
      simp
    · exact measure_ne_top _ _
  · exact (integrable_mLimsup (fst_map_le_of_le h_le) a MeasurableSet.univ).restrict
  · exact ae_of_all _ (fun x ↦ mLimsup_nonneg (fst_map_le_of_le h_le) _ _ _)

lemma withDensity_one_sub_g (κ ν : kernel α ℝ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (1 - g κ (κ + ν) a x)) = ν := by
  have h_le : κ ≤ κ + ν := todo κ ν
  suffices kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (1 - g κ (κ + ν) a x))
      + kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (g κ (κ + ν) a x)) = κ + ν by
    ext a s
    have h : (kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (1 - g κ (κ + ν) a x))
        + kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (g κ (κ + ν) a x))) a s
        = κ a s + ν a s := by
      rw [this]
      simp
    simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
      at h
    rwa [withDensity_g, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have h_nonneg : ∀ a x, 0 ≤ g κ (κ + ν) a x :=
    fun _ _ ↦ mLimsup_nonneg (fst_map_le_of_le h_le) _ _ _
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (h_nonneg _ _), ENNReal.ofReal_one]
  rw [kernel.withDensity_sub_add]
  · rw [kernel.withDensity_one']
  · exact measurable_const
  · exact (measurable_g _ _).ennreal_ofReal
  · refine fun a ↦ ne_of_lt ?_
    calc ∫⁻ x, ENNReal.ofReal (g κ (κ + ν) a x) ∂(κ + ν) a
      ≤ ∫⁻ _, 1 ∂(κ + ν) a := by
          refine lintegral_mono (fun x ↦ ?_)
          simp [g_le_one (todo κ ν)]
    _ < ⊤ := by rw [MeasureTheory.lintegral_const, one_mul]; exact measure_lt_top _ _
  · refine fun a ↦ ae_of_all _ (fun x ↦ ?_)
    simp only [ENNReal.ofReal_le_one]
    exact mLimsup_le_one (fst_map_le_of_le h_le) _ _ _

noncomputable
def kernel.singularPartReal (κ ν : kernel α ℝ) [IsSFiniteKernel κ] [IsSFiniteKernel ν] :
    kernel α ℝ :=
    kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (g κ (κ + ν) a x)
      - Real.toNNReal (1 - g κ (κ + ν) a x) * kernel.rnDerivReal κ ν a x)

lemma kernel.mutuallySingular_singularPartReal (κ ν : kernel α ℝ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.singularPartReal κ ν a ⟂ₘ ν a := by
  symm
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  refine ⟨{x | g κ (κ + ν) a x = 1}, measurable_g_right _ _ a (measurableSet_singleton _), ?_, ?_⟩
  · suffices kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (1 - g κ (κ + ν) a x)) a
        {x | g κ (κ + ν) a x = 1} = 0 by
      rwa [withDensity_one_sub_g κ ν] at this
    simp_rw [h_coe]
    rw [kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq, ae_restrict_iff]
    rotate_left
    · exact (measurable_const.sub ((measurable_g _ _).comp measurable_prod_mk_left)).ennreal_ofReal
        (measurableSet_singleton _)
    · exact (measurable_const.sub ((measurable_g _ _).comp measurable_prod_mk_left)).ennreal_ofReal
    · exact (measurable_const.sub (measurable_g _ _)).ennreal_ofReal
    refine ae_of_all _ (fun x hx ↦ ?_)
    simp only [mem_setOf_eq] at hx
    simp [hx]
  · rw [kernel.singularPartReal, kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
      ae_restrict_iff]
    all_goals simp_rw [h_coe]
    rotate_left
    · refine measurableSet_preimage (Measurable.sub ?_ ?_) (measurableSet_singleton _)
      · exact (measurable_g_right _ _ _).ennreal_ofReal
      · refine Measurable.mul ?_ ?_
        · exact (measurable_const.sub (measurable_g_right _ _ _)).ennreal_ofReal
        · exact measurable_rnDerivReal_right _ _ _
    · refine Measurable.sub ?_ ?_
      · exact (measurable_g_right _ _ _).ennreal_ofReal
      · refine Measurable.mul ?_ ?_
        · exact (measurable_const.sub (measurable_g_right _ _ _)).ennreal_ofReal
        · exact measurable_rnDerivReal_right _ _ _
    · refine Measurable.sub ?_ ?_
      · exact (measurable_g _ _).ennreal_ofReal
      · refine Measurable.mul ?_ ?_
        · exact (measurable_const.sub (measurable_g _ _)).ennreal_ofReal
        · exact measurable_rnDerivReal
    refine ae_of_all _ (fun x hx ↦ ?_)
    simp only [mem_compl_iff, mem_setOf_eq] at hx
    simp_rw [rnDerivReal]
    rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
      mul_inv_cancel, one_mul, tsub_self]
    · rfl
    · rw [ne_eq, sub_eq_zero]
      exact Ne.symm hx
    · simp [g_le_one (todo κ ν)]
    · simp [lt_of_le_of_ne (g_le_one (todo κ ν)) hx]

lemma kernel.rnDerivReal_add_singularPartReal (κ ν : kernel α ℝ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity ν (kernel.rnDerivReal κ ν) + kernel.singularPartReal κ ν = κ := by
  have : kernel.withDensity ν (kernel.rnDerivReal κ ν)
      = kernel.withDensity (kernel.withDensity (κ + ν)
        (fun a x ↦ Real.toNNReal (1 - g κ (κ + ν) a x))) (kernel.rnDerivReal κ ν) := by
    rw [kernel.rnDerivReal_def]
    congr
    exact (withDensity_one_sub_g κ ν).symm
  rw [this, kernel.singularPartReal, add_comm, ← kernel.withDensity_mul]
  rotate_left
  · exact (measurable_const.sub (measurable_g _ _)).real_toNNReal
  · exact measurable_rnDerivReal
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  have h_le : ∀ a x, ENNReal.ofReal (1 - g κ (κ + ν) a x) * kernel.rnDerivReal κ ν a x
      ≤ ENNReal.ofReal (g κ (κ + ν) a x) := by
    intro a x
    unfold kernel.rnDerivReal
    by_cases hg_one : g κ (κ + ν) a x = 1
    · simp [hg_one]
    rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
      mul_inv_cancel, one_mul]
    · rw [ne_eq, sub_eq_zero]
      exact Ne.symm hg_one
    · simp [g_le_one (todo κ ν)]
    · simp [lt_of_le_of_ne (g_le_one (todo κ ν)) hg_one]
  rw [kernel.withDensity_sub_add, withDensity_g]
  all_goals simp_rw [h_coe]
  · exact (measurable_g _ _).ennreal_ofReal
  · exact Measurable.mul (measurable_const.sub (measurable_g _ _)).ennreal_ofReal
      measurable_rnDerivReal
  · intro a
    have : ∀ x, ENNReal.ofReal (1 - g κ (κ + ν) a x) * kernel.rnDerivReal κ ν a x ≤ 1 := by
      refine fun x ↦ (h_le a x).trans ?_
      simp only [ENNReal.ofReal_le_one, g_le_one (todo κ ν)]
    refine ne_of_lt ?_
    calc ∫⁻ x, ENNReal.ofReal (1 - g κ (κ + ν) a x) * kernel.rnDerivReal κ ν a x ∂(κ + ν) a
      ≤ ∫⁻ _, 1 ∂(κ + ν) a := lintegral_mono this
    _ < ⊤ := by rw [MeasureTheory.lintegral_const, one_mul]; exact measure_lt_top _ _
  · exact fun a ↦ ae_of_all _ (h_le a)

end Real

section StandardBorel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {κ ν : kernel α Ω}

protected noncomputable def kernel.rnDeriv (κ ν : kernel α Ω) (a : α) (ω : Ω) : ℝ≥0∞ :=
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  kernel.rnDerivReal (kernel.map κ f hf.measurable) (kernel.map ν f hf.measurable) a (f ω)

protected noncomputable def kernel.singularPart (κ ν : kernel α Ω)
    [IsSFiniteKernel κ] [IsSFiniteKernel ν] : kernel α Ω :=
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  kernel.comapRight
    (kernel.singularPartReal (kernel.map κ f hf.measurable) (kernel.map ν f hf.measurable))
    hf

lemma kernel.mutuallySingular_singularPart (κ ν : kernel α Ω) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    kernel.singularPart κ ν a ⟂ₘ ν a := by
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  change kernel.comapRight
    (kernel.singularPartReal (kernel.map κ f hf.measurable) (kernel.map ν f hf.measurable))
    hf a ⟂ₘ ν a
  let s := (kernel.mutuallySingular_singularPartReal (kernel.map κ f hf.measurable)
    (kernel.map ν f hf.measurable) a).nullSet
  have hs : MeasurableSet s := Measure.MutuallySingular.measurableSet_nullSet _
  have hνs := Measure.MutuallySingular.measure_compl_nullSet
    (kernel.mutuallySingular_singularPartReal (kernel.map κ f hf.measurable)
      (kernel.map ν f hf.measurable) a)
  have hsing := Measure.MutuallySingular.measure_nullSet
    (kernel.mutuallySingular_singularPartReal (kernel.map κ f hf.measurable)
      (kernel.map ν f hf.measurable) a)
  refine ⟨f ⁻¹' s, hf.measurable hs, ?_, ?_⟩
  · rw [kernel.comapRight_apply' _ _ _ (hf.measurable hs)]
    refine measure_mono_null (fun x hx ↦ ?_) hsing
    exact image_preimage_subset _ _ hx
  · have : ν = kernel.comapRight (kernel.map ν f hf.measurable) hf := by
      ext a
      rw [kernel.comapRight_apply _ hf, kernel.map_apply, MeasurableEmbedding.comap_map]
      exact hf
    rw [this, kernel.comapRight_apply' _ _ _ (hf.measurable hs).compl]
    refine measure_mono_null (fun x ↦ ?_) hνs
    rw [image_compl_preimage, mem_diff]
    exact fun h ↦ h.2

lemma kernel.rnDeriv_add_singularPart (κ ν : kernel α Ω) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity ν (kernel.rnDeriv κ ν) + kernel.singularPart κ ν = κ := by
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  ext a : 1
  simp only [coeFn_add, Pi.add_apply]
  change kernel.withDensity ν
      (fun a ω ↦ kernel.rnDerivReal (kernel.map κ f hf.measurable)
        (kernel.map ν f hf.measurable) a (f ω)) a + kernel.comapRight
    (kernel.singularPartReal (kernel.map κ f hf.measurable) (kernel.map ν f hf.measurable))
    hf a = κ a
  have h := kernel.rnDerivReal_add_singularPartReal (kernel.map κ f hf.measurable)
    (kernel.map ν f hf.measurable)
  have : κ = kernel.comapRight (kernel.map κ f hf.measurable) hf := by
    ext a
    rw [kernel.comapRight_apply _ hf, kernel.map_apply, MeasurableEmbedding.comap_map]
    exact hf
  conv_rhs => rw [this, ← h]
  rw [comapRight_apply, comapRight_apply]
  simp only [coeFn_add, Pi.add_apply]
  rw [MeasurableEmbedding.comap_add hf]
  congr
  ext s hs
  rw [Measure.comap_apply _ hf.injective (fun s hs ↦ hf.measurableSet_image.mpr hs) _ hs,
    kernel.withDensity_apply', kernel.withDensity_apply', kernel.map_apply,
    Measure.restrict_map hf.measurable (hf.measurableSet_image.mpr hs),
    MeasureTheory.lintegral_map _ hf.measurable, preimage_image_eq _ hf.injective]
  · exact measurable_rnDerivReal_right _ _ _
  · exact measurable_rnDerivReal
  · change Measurable ((Function.uncurry fun a x ↦
        rnDerivReal (map κ f hf.measurable) (map ν f hf.measurable) a x)
      ∘ (fun p : α × Ω ↦ (p.1, f p.2)))
    exact measurable_rnDerivReal.comp (measurable_fst.prod_mk (hf.measurable.comp measurable_snd))

end StandardBorel

end ProbabilityTheory
