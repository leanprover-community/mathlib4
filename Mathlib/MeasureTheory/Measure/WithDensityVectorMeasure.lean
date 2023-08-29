/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

#align_import measure_theory.measure.with_density_vector_measure from "leanprover-community/mathlib"@"d1bd9c5df2867c1cb463bc6364446d57bdd9f7f1"

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

open scoped Classical MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable {μ ν : Measure α}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Given a measure `μ` and an integrable function `f`, `μ.withDensityᵥ f` is
the vector measure which maps the set `s` to `∫ₛ f ∂μ`. -/
def Measure.withDensityᵥ {m : MeasurableSpace α} (μ : Measure α) (f : α → E) : VectorMeasure α E :=
  if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
                   -- 🎉 no goals
      not_measurable' := fun s hs => if_neg hs
      m_iUnion' := fun s hs₁ hs₂ => by
        dsimp only
        -- ⊢ HasSum (fun i => if MeasurableSet (s i) then ∫ (x : α) in s i, f x ∂μ else 0 …
        convert hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        -- ⊢ (if MeasurableSet (s n) then ∫ (x : α) in s n, f x ∂μ else 0) = ∫ (a : α) in …
        · rw [if_pos (hs₁ n)]
          -- 🎉 no goals
        · rw [if_pos (MeasurableSet.iUnion hs₁)] }
          -- 🎉 no goals
  else 0
#align measure_theory.measure.with_densityᵥ MeasureTheory.Measure.withDensityᵥ

open Measure

variable {f g : α → E}

theorem withDensityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f s = ∫ x in s, f x ∂μ := by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs
                                                -- ⊢ ↑{ measureOf' := fun s => if MeasurableSet s then ∫ (x : α) in s, f x ∂μ els …
                                                                               -- 🎉 no goals
#align measure_theory.with_densityᵥ_apply MeasureTheory.withDensityᵥ_apply

@[simp]
theorem withDensityᵥ_zero : μ.withDensityᵥ (0 : α → E) = 0 := by
  ext1 s hs; erw [withDensityᵥ_apply (integrable_zero α E μ) hs]; simp
  -- ⊢ ↑(withDensityᵥ μ 0) s = ↑0 s
             -- ⊢ ∫ (x : α) in s, 0 ∂μ = ↑0 s
                                                                  -- 🎉 no goals
#align measure_theory.with_densityᵥ_zero MeasureTheory.withDensityᵥ_zero

@[simp]
theorem withDensityᵥ_neg : μ.withDensityᵥ (-f) = -μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  -- ⊢ withDensityᵥ μ (-f) = -withDensityᵥ μ f
  · ext1 i hi
    -- ⊢ ↑(withDensityᵥ μ (-f)) i = ↑(-withDensityᵥ μ f) i
    rw [VectorMeasure.neg_apply, withDensityᵥ_apply hf hi, ← integral_neg,
      withDensityᵥ_apply hf.neg hi]
    rfl
    -- 🎉 no goals
  · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, neg_zero]
    -- ⊢ ¬Integrable (-f)
    rwa [integrable_neg_iff]
    -- 🎉 no goals
#align measure_theory.with_densityᵥ_neg MeasureTheory.withDensityᵥ_neg

theorem withDensityᵥ_neg' : (μ.withDensityᵥ fun x => -f x) = -μ.withDensityᵥ f :=
  withDensityᵥ_neg
#align measure_theory.with_densityᵥ_neg' MeasureTheory.withDensityᵥ_neg'

@[simp]
theorem withDensityᵥ_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensityᵥ g := by
  ext1 i hi
  -- ⊢ ↑(withDensityᵥ μ (f + g)) i = ↑(withDensityᵥ μ f + withDensityᵥ μ g) i
  rw [withDensityᵥ_apply (hf.add hg) hi, VectorMeasure.add_apply, withDensityᵥ_apply hf hi,
    withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  -- ⊢ ∫ (x : α) in i, f x + g x ∂μ = ∫ (x : α) in i, f x ∂μ + ∫ (x : α) in i, g x ∂μ
  rw [integral_add] <;> rw [← integrableOn_univ]
  -- ⊢ Integrable fun x => f x
                        -- ⊢ IntegrableOn (fun x => f x) Set.univ
                        -- ⊢ IntegrableOn (fun x => g x) Set.univ
  · exact hf.integrableOn.restrict MeasurableSet.univ
    -- 🎉 no goals
  · exact hg.integrableOn.restrict MeasurableSet.univ
    -- 🎉 no goals
#align measure_theory.with_densityᵥ_add MeasureTheory.withDensityᵥ_add

theorem withDensityᵥ_add' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x + g x) = μ.withDensityᵥ f + μ.withDensityᵥ g :=
  withDensityᵥ_add hf hg
#align measure_theory.with_densityᵥ_add' MeasureTheory.withDensityᵥ_add'

@[simp]
theorem withDensityᵥ_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f - g) = μ.withDensityᵥ f - μ.withDensityᵥ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, withDensityᵥ_add hf hg.neg, withDensityᵥ_neg]
  -- 🎉 no goals
#align measure_theory.with_densityᵥ_sub MeasureTheory.withDensityᵥ_sub

theorem withDensityᵥ_sub' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x - g x) = μ.withDensityᵥ f - μ.withDensityᵥ g :=
  withDensityᵥ_sub hf hg
#align measure_theory.with_densityᵥ_sub' MeasureTheory.withDensityᵥ_sub'

@[simp]
theorem withDensityᵥ_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (f : α → E) (r : 𝕜) : μ.withDensityᵥ (r • f) = r • μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  -- ⊢ withDensityᵥ μ (r • f) = r • withDensityᵥ μ f
  · ext1 i hi
    -- ⊢ ↑(withDensityᵥ μ (r • f)) i = ↑(r • withDensityᵥ μ f) i
    rw [withDensityᵥ_apply (hf.smul r) hi, VectorMeasure.smul_apply, withDensityᵥ_apply hf hi, ←
      integral_smul r f]
    rfl
    -- 🎉 no goals
  · by_cases hr : r = 0
    -- ⊢ withDensityᵥ μ (r • f) = r • withDensityᵥ μ f
    · rw [hr, zero_smul, zero_smul, withDensityᵥ_zero]
      -- 🎉 no goals
    · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, smul_zero]
      -- ⊢ ¬Integrable (r • f)
      rwa [integrable_smul_iff hr f]
      -- 🎉 no goals
#align measure_theory.with_densityᵥ_smul MeasureTheory.withDensityᵥ_smul

theorem withDensityᵥ_smul' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (f : α → E) (r : 𝕜) :
    (μ.withDensityᵥ fun x => r • f x) = r • μ.withDensityᵥ f :=
  withDensityᵥ_smul f r
#align measure_theory.with_densityᵥ_smul' MeasureTheory.withDensityᵥ_smul'

theorem Measure.withDensityᵥ_absolutelyContinuous (μ : Measure α) (f : α → ℝ) :
    μ.withDensityᵥ f ≪ᵥ μ.toENNRealVectorMeasure := by
  by_cases hf : Integrable f μ
  -- ⊢ withDensityᵥ μ f ≪ᵥ toENNRealVectorMeasure μ
  · refine' VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ => _
    -- ⊢ ↑(withDensityᵥ μ f) i = 0
    rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
    -- ⊢ ↑(withDensityᵥ μ f) i = 0
    rw [withDensityᵥ_apply hf hi₁, Measure.restrict_zero_set hi₂, integral_zero_measure]
    -- 🎉 no goals
  · rw [withDensityᵥ, dif_neg hf]
    -- ⊢ 0 ≪ᵥ toENNRealVectorMeasure μ
    exact VectorMeasure.AbsolutelyContinuous.zero _
    -- 🎉 no goals
#align measure_theory.measure.with_densityᵥ_absolutely_continuous MeasureTheory.Measure.withDensityᵥ_absolutelyContinuous

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
theorem Integrable.ae_eq_of_withDensityᵥ_eq {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : μ.withDensityᵥ f = μ.withDensityᵥ g) : f =ᵐ[μ] g := by
  refine' hf.ae_eq_of_forall_set_integral_eq f g hg fun i hi _ => _
  -- ⊢ ∫ (x : α) in i, f x ∂μ = ∫ (x : α) in i, g x ∂μ
  rw [← withDensityᵥ_apply hf hi, hfg, withDensityᵥ_apply hg hi]
  -- 🎉 no goals
#align measure_theory.integrable.ae_eq_of_with_densityᵥ_eq MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq

theorem WithDensityᵥEq.congr_ae {f g : α → E} (h : f =ᵐ[μ] g) :
    μ.withDensityᵥ f = μ.withDensityᵥ g := by
  by_cases hf : Integrable f μ
  -- ⊢ withDensityᵥ μ f = withDensityᵥ μ g
  · ext i hi
    -- ⊢ ↑(withDensityᵥ μ f) i = ↑(withDensityᵥ μ g) i
    rw [withDensityᵥ_apply hf hi, withDensityᵥ_apply (hf.congr h) hi]
    -- ⊢ ∫ (x : α) in i, f x ∂μ = ∫ (x : α) in i, g x ∂μ
    exact integral_congr_ae (ae_restrict_of_ae h)
    -- 🎉 no goals
  · have hg : ¬Integrable g μ := by intro hg; exact hf (hg.congr h.symm)
    -- ⊢ withDensityᵥ μ f = withDensityᵥ μ g
    rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg hg]
    -- 🎉 no goals
#align measure_theory.with_densityᵥ_eq.congr_ae MeasureTheory.WithDensityᵥEq.congr_ae

theorem Integrable.withDensityᵥ_eq_iff {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ f = μ.withDensityᵥ g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg => hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae h⟩
#align measure_theory.integrable.with_densityᵥ_eq_iff MeasureTheory.Integrable.withDensityᵥ_eq_iff

section SignedMeasure

theorem withDensityᵥ_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (μ.withDensityᵥ fun x => (f x).toReal) =
      @toSignedMeasure α _ (μ.withDensity f) (isFiniteMeasure_withDensity hf) := by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  -- ⊢ (withDensityᵥ μ fun x => ENNReal.toReal (f x)) = toSignedMeasure (withDensit …
  haveI := isFiniteMeasure_withDensity hf
  -- ⊢ (withDensityᵥ μ fun x => ENNReal.toReal (f x)) = toSignedMeasure (withDensit …
  ext i hi
  -- ⊢ ↑(withDensityᵥ μ fun x => ENNReal.toReal (f x)) i = ↑(toSignedMeasure (withD …
  rw [withDensityᵥ_apply hfi hi, toSignedMeasure_apply_measurable hi, withDensity_apply _ hi,
    integral_toReal hfm.restrict]
  refine' ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf _)
  -- ⊢ ∫⁻ (x : α) in i, f x ∂μ ≤ ∫⁻ (x : α), f x ∂μ
  conv_rhs => rw [← set_lintegral_univ]
  -- ⊢ ∫⁻ (x : α) in i, f x ∂μ ≤ ∫⁻ (x : α) in Set.univ, f x ∂μ
  exact lintegral_mono_set (Set.subset_univ _)
  -- 🎉 no goals
#align measure_theory.with_densityᵥ_to_real MeasureTheory.withDensityᵥ_toReal

theorem withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part {f : α → ℝ}
    (hfi : Integrable f μ) :
    μ.withDensityᵥ f =
      @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| f x)
          (isFiniteMeasure_withDensity_ofReal hfi.2) -
        @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| -f x)
          (isFiniteMeasure_withDensity_ofReal hfi.neg.2) := by
  haveI := isFiniteMeasure_withDensity_ofReal hfi.2
  -- ⊢ withDensityᵥ μ f = toSignedMeasure (withDensity μ fun x => ENNReal.ofReal (f …
  haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  -- ⊢ withDensityᵥ μ f = toSignedMeasure (withDensity μ fun x => ENNReal.ofReal (f …
  ext i hi
  -- ⊢ ↑(withDensityᵥ μ f) i = ↑(toSignedMeasure (withDensity μ fun x => ENNReal.of …
  rw [withDensityᵥ_apply hfi hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn,
    VectorMeasure.sub_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi, withDensity_apply _ hi, withDensity_apply _ hi]
#align measure_theory.with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part MeasureTheory.withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part

theorem Integrable.withDensityᵥ_trim_eq_integral {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → ℝ} (hf : Integrable f μ) {i : Set α} (hi : MeasurableSet[m] i) :
    (μ.withDensityᵥ f).trim hm i = ∫ x in i, f x ∂μ := by
  rw [VectorMeasure.trim_measurableSet_eq hm hi, withDensityᵥ_apply hf (hm _ hi)]
  -- 🎉 no goals
#align measure_theory.integrable.with_densityᵥ_trim_eq_integral MeasureTheory.Integrable.withDensityᵥ_trim_eq_integral

theorem Integrable.withDensityᵥ_trim_absolutelyContinuous {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) (hfi : Integrable f μ) :
    (μ.withDensityᵥ f).trim hm ≪ᵥ (μ.trim hm).toENNRealVectorMeasure := by
  refine' VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ => _
  -- ⊢ ↑(VectorMeasure.trim (withDensityᵥ μ f) hm) j = 0
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁, trim_measurableSet_eq hm hj₁] at hj₂
  -- ⊢ ↑(VectorMeasure.trim (withDensityᵥ μ f) hm) j = 0
  rw [VectorMeasure.trim_measurableSet_eq hm hj₁, withDensityᵥ_apply hfi (hm _ hj₁)]
  -- ⊢ ∫ (x : α) in j, f x ∂μ = 0
  simp only [Measure.restrict_eq_zero.mpr hj₂, integral_zero_measure]
  -- 🎉 no goals
#align measure_theory.integrable.with_densityᵥ_trim_absolutely_continuous MeasureTheory.Integrable.withDensityᵥ_trim_absolutelyContinuous

end SignedMeasure

end MeasureTheory
