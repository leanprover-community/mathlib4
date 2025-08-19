/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable set `s`, `v i = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `MeasureTheory.Measure.withDensityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/


noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- Given a measure `μ` and an integrable function `f`, `μ.withDensityᵥ f` is
the vector measure which maps the set `s` to `∫ₛ f ∂μ`. -/
def Measure.withDensityᵥ {m : MeasurableSpace α} (μ : Measure α) (f : α → E) : VectorMeasure α E :=
  if hf : Integrable f μ then
    { measureOf' := fun s ↦ if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
      not_measurable' := fun _ hs ↦ if_neg hs
      m_iUnion' := fun s hs₁ hs₂ ↦ by
        convert hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        · rw [if_pos (hs₁ n)]
        · rw [if_pos (MeasurableSet.iUnion hs₁)] }
  else 0

open Measure

variable {f g : α → E}

theorem withDensityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f s = ∫ x in s, f x ∂μ := by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs

@[simp]
theorem withDensityᵥ_zero : μ.withDensityᵥ (0 : α → E) = 0 := by
  ext1 s hs
  rw [Pi.zero_def, withDensityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]
theorem withDensityᵥ_neg : μ.withDensityᵥ (-f) = -μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [VectorMeasure.neg_apply, withDensityᵥ_apply hf hi, ← integral_neg,
      withDensityᵥ_apply hf.neg hi]
    simp only [Pi.neg_apply]
  · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, neg_zero]
    rwa [integrable_neg_iff]

theorem withDensityᵥ_neg' : (μ.withDensityᵥ fun x ↦ -f x) = -μ.withDensityᵥ f :=
  withDensityᵥ_neg

@[simp]
theorem withDensityᵥ_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensityᵥ g := by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.add hg) hi, VectorMeasure.add_apply, withDensityᵥ_apply hf hi,
    withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add]
  · exact hf.integrableOn
  · exact hg.integrableOn

theorem withDensityᵥ_add' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x ↦ f x + g x) = μ.withDensityᵥ f + μ.withDensityᵥ g :=
  withDensityᵥ_add hf hg

@[simp]
theorem withDensityᵥ_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f - g) = μ.withDensityᵥ f - μ.withDensityᵥ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, withDensityᵥ_add hf hg.neg, withDensityᵥ_neg]

theorem withDensityᵥ_sub' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x ↦ f x - g x) = μ.withDensityᵥ f - μ.withDensityᵥ g :=
  withDensityᵥ_sub hf hg

@[simp]
theorem withDensityᵥ_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (f : α → E) (r : 𝕜) : μ.withDensityᵥ (r • f) = r • μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [withDensityᵥ_apply (hf.smul r) hi, VectorMeasure.smul_apply, withDensityᵥ_apply hf hi, ←
      integral_smul r f]
    simp only [Pi.smul_apply]
  · by_cases hr : r = 0
    · rw [hr, zero_smul, zero_smul, withDensityᵥ_zero]
    · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, smul_zero]
      rwa [integrable_smul_iff hr f]

theorem withDensityᵥ_smul' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (f : α → E) (r : 𝕜) :
    (μ.withDensityᵥ fun x ↦ r • f x) = r • μ.withDensityᵥ f :=
  withDensityᵥ_smul f r

theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity {f : α → ℝ≥0} {g : α → E}
    (hf : AEMeasurable f μ) (hfg : Integrable (f • g) μ) :
    μ.withDensityᵥ (f • g) = (μ.withDensity (fun x ↦ f x)).withDensityᵥ g := by
  ext s hs
  rw [withDensityᵥ_apply hfg hs,
    withDensityᵥ_apply ((integrable_withDensity_iff_integrable_smul₀ hf).mpr hfg) hs,
    setIntegral_withDensity_eq_setIntegral_smul₀ hf.restrict _ hs]
  simp only [Pi.smul_apply']

theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity' {f : α → ℝ≥0∞} {g : α → E}
    (hf : AEMeasurable f μ) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    (hfg : Integrable (fun x ↦ (f x).toReal • g x) μ) :
    μ.withDensityᵥ (fun x ↦ (f x).toReal • g x) = (μ.withDensity f).withDensityᵥ g := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    ← withDensityᵥ_smul_eq_withDensityᵥ_withDensity hf.ennreal_toNNReal hfg]
  apply congr_arg
  ext
  simp [NNReal.smul_def, ENNReal.coe_toNNReal_eq_toReal]

theorem Measure.withDensityᵥ_absolutelyContinuous (μ : Measure α) (f : α → ℝ) :
    μ.withDensityᵥ f ≪ᵥ μ.toENNRealVectorMeasure := by
  by_cases hf : Integrable f μ
  · refine VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ ↦ ?_
    rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
    rw [withDensityᵥ_apply hf hi₁, Measure.restrict_zero_set hi₂, integral_zero_measure]
  · rw [withDensityᵥ, dif_neg hf]
    exact VectorMeasure.AbsolutelyContinuous.zero _

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
theorem Integrable.ae_eq_of_withDensityᵥ_eq [CompleteSpace E] {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : μ.withDensityᵥ f = μ.withDensityᵥ g) : f =ᵐ[μ] g := by
  refine hf.ae_eq_of_forall_setIntegral_eq f g hg fun i hi _ ↦ ?_
  rw [← withDensityᵥ_apply hf hi, hfg, withDensityᵥ_apply hg hi]

theorem WithDensityᵥEq.congr_ae {f g : α → E} (h : f =ᵐ[μ] g) :
    μ.withDensityᵥ f = μ.withDensityᵥ g := by
  by_cases hf : Integrable f μ
  · ext i hi
    rw [withDensityᵥ_apply hf hi, withDensityᵥ_apply (hf.congr h) hi]
    exact integral_congr_ae (ae_restrict_of_ae h)
  · have hg : ¬Integrable g μ := by intro hg; exact hf (hg.congr h.symm)
    rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg hg]

theorem Integrable.withDensityᵥ_eq_iff [CompleteSpace E]
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ f = μ.withDensityᵥ g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h ↦ WithDensityᵥEq.congr_ae h⟩

section SignedMeasure

theorem withDensityᵥ_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (μ.withDensityᵥ fun x ↦ (f x).toReal) =
      @toSignedMeasure α _ (μ.withDensity f) (isFiniteMeasure_withDensity hf) := by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  haveI := isFiniteMeasure_withDensity hf
  ext i hi
  rw [withDensityᵥ_apply hfi hi, toSignedMeasure_apply_measurable hi, measureReal_def,
    withDensity_apply _ hi, integral_toReal hfm.restrict]
  refine ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf ?_)
  conv_rhs => rw [← setLIntegral_univ]
  exact lintegral_mono_set (Set.subset_univ _)

theorem withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part {f : α → ℝ}
    (hfi : Integrable f μ) :
    μ.withDensityᵥ f =
      @toSignedMeasure α _ (μ.withDensity fun x ↦ ENNReal.ofReal <| f x)
          (isFiniteMeasure_withDensity_ofReal hfi.2) -
        @toSignedMeasure α _ (μ.withDensity fun x ↦ ENNReal.ofReal <| -f x)
          (isFiniteMeasure_withDensity_ofReal hfi.neg.2) := by
  haveI := isFiniteMeasure_withDensity_ofReal hfi.2
  haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  ext i hi
  rw [withDensityᵥ_apply hfi hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn,
    VectorMeasure.sub_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi, measureReal_def, measureReal_def,
    withDensity_apply _ hi, withDensity_apply _ hi]

theorem Integrable.withDensityᵥ_trim_eq_integral {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → ℝ} (hf : Integrable f μ) {i : Set α} (hi : MeasurableSet[m] i) :
    (μ.withDensityᵥ f).trim hm i = ∫ x in i, f x ∂μ := by
  rw [VectorMeasure.trim_measurableSet_eq hm hi, withDensityᵥ_apply hf (hm _ hi)]

theorem Integrable.withDensityᵥ_trim_absolutelyContinuous {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) (hfi : Integrable f μ) :
    (μ.withDensityᵥ f).trim hm ≪ᵥ (μ.trim hm).toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ ↦ ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁, trim_measurableSet_eq hm hj₁] at hj₂
  rw [VectorMeasure.trim_measurableSet_eq hm hj₁, withDensityᵥ_apply hfi (hm _ hj₁)]
  simp only [Measure.restrict_eq_zero.mpr hj₂, integral_zero_measure]

end SignedMeasure

end MeasureTheory
