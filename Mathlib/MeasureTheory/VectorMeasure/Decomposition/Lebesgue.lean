/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem for signed measures. The Lebesgue decomposition
theorem states that, given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ`
and a measurable function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect
to `ν`.

## Main definitions

* `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition` : A signed measure `s` and a
  measure `μ` is said to `HaveLebesgueDecomposition` if both the positive part and negative
  part of `s` `HaveLebesgueDecomposition` with respect to `μ`.
* `MeasureTheory.SignedMeasure.singularPart` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `MeasureTheory.SignedMeasure.rnDeriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

## Tags

Lebesgue decomposition theorem
-/


noncomputable section

open scoped MeasureTheory NNReal ENNReal

open Set

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

namespace MeasureTheory

namespace SignedMeasure

open Measure

/-- A signed measure `s` is said to `HaveLebesgueDecomposition` with respect to a measure `μ`
if the positive part and the negative part of `s` both `HaveLebesgueDecomposition` with
respect to `μ`. -/
class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart

theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

-- `inferInstance` directly does not work
-- see Note [lower instance priority]
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] : s.HaveLebesgueDecomposition μ where
  posPart := inferInstance
  negPart := inferInstance

instance haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_negPart]
    infer_instance

instance haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ≥0) : (r • s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart]
    infer_instance

instance haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ) : (r • s).HaveLebesgueDecomposition μ := by
  by_cases hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · rw [not_le] at hr
    refine
      { posPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_negPart_neg _ _ hr]
          infer_instance }

/-- Given a signed measure `s` and a measure `μ`, `s.singularPart μ` is the signed measure
such that `s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s` and
`s.singularPart μ` is mutually singular with respect to `μ`. -/
def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

section

theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ := by
  by_cases hl : s.HaveLebesgueDecomposition μ
  · obtain ⟨i, hi, hpos, hneg⟩ := s.toJordanDecomposition.mutuallySingular
    rw [s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ] at hpos
    rw [s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ] at hneg
    rw [add_apply, add_eq_zero] at hpos hneg
    exact ⟨i, hi, hpos.1, hneg.1⟩
  · rw [not_haveLebesgueDecomposition_iff] at hl
    rcases hl with hp | hn
    · rw [Measure.singularPart, dif_neg hp]
      exact MutuallySingular.zero_left
    · rw [Measure.singularPart, Measure.singularPart, dif_neg hn]
      exact MutuallySingular.zero_right

theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJordanDecomposition, singularPart, JordanDecomposition.toSignedMeasure]
  rw [totalVariation, this]

nonrec theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutuallySingular_ennreal_iff, singularPart_totalVariation,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)

end

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`rnDeriv s μ` satisfies `μ.withDensityᵥ (s.rnDeriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`
and can be found in `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`. -/
def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α → ℝ := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal

-- The generated equation theorem is the form of `rnDeriv s μ x = ...`.
theorem rnDeriv_def (s : SignedMeasure α) (μ : Measure α) : rnDeriv s μ = fun x =>
    (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
      (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal :=
  rfl

variable {s t : SignedMeasure α}

@[measurability]
theorem measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ) := by
  rw [rnDeriv_def]
  fun_prop

theorem integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ := by
  refine Integrable.sub ?_ ?_ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable
        fun_prop
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne

variable (s μ)

/-- **The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed measure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with respect to `μ`
and `s = t + μ.withDensityᵥ f`. In this case `t = s.singularPart μ` and
`f = s.rnDeriv μ`. -/
theorem singularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] :
    s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s := by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s, JordanDecomposition.toSignedMeasure]
  rw [singularPart, rnDeriv_def,
    withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _),
    withDensityᵥ_toReal, withDensityᵥ_toReal, sub_eq_add_neg, sub_eq_add_neg,
    add_comm (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure, ← add_assoc,
    add_assoc (-(s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure),
    ← toSignedMeasure_add, add_comm, ← add_assoc, ← neg_add, ← toSignedMeasure_add, add_comm,
    ← sub_eq_add_neg]
  · convert rfl
    -- `convert rfl` much faster than `congr`
    · exact s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ
    · rw [add_comm]
      exact s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ
  all_goals
    first
    | exact (lintegral_rnDeriv_lt_top _ _).ne
    | measurability

variable {s μ}

theorem jordanDecomposition_add_withDensity_mutuallySingular {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) :
    (t.toJordanDecomposition.posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ
      t.toJordanDecomposition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x) := by
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
      ((htμ.2.symm.mono_ac (withDensity_absolutelyContinuous _ _) (refl _)).add_right
        (withDensity_ofReal_mutuallySingular hf))

theorem toJordanDecomposition_eq_of_eq_add_withDensity {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.toJordanDecomposition =
      @JordanDecomposition.mk α _
        (t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x))
        (t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
        (by haveI := isFiniteMeasure_withDensity_ofReal hfi.2; infer_instance)
        (by haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2; infer_instance)
        (jordanDecomposition_add_withDensity_mutuallySingular hf htμ) := by
  haveI := isFiniteMeasure_withDensity_ofReal hfi.2
  haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine toJordanDecomposition_eq ?_
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [VectorMeasure.sub_apply, toSignedMeasure_apply_measurable hi,
      toSignedMeasure_apply_measurable hi, measureReal_add_apply, measureReal_add_apply,
      add_sub_add_comm, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi, ← VectorMeasure.sub_apply,
      ← JordanDecomposition.toSignedMeasure, toSignedMeasure_toJordanDecomposition,
      VectorMeasure.add_apply, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi,
      withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi,
      VectorMeasure.sub_apply]

private theorem haveLebesgueDecomposition_mk' (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv, totalVariation_mutuallySingular_iff] at htμ
  refine
    { posPart := by
        use ⟨t.toJordanDecomposition.posPart, fun x => ENNReal.ofReal (f x)⟩
        refine ⟨hf.ennreal_ofReal, htμ.1, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
      negPart := by
        use ⟨t.toJordanDecomposition.negPart, fun x => ENNReal.ofReal (-f x)⟩
        refine ⟨hf.neg.ennreal_ofReal, htμ.2, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd] }

theorem haveLebesgueDecomposition_mk (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

private theorem eq_singularPart' (t : SignedMeasure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    t = s.singularPart μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  rw [singularPart, ← t.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure]
  congr
  -- NB: `measurability` proves this `have`, but is slow.
  -- TODO: make `fun_prop` able to handle this
  · have hfpos : Measurable fun x => ENNReal.ofReal (f x) := hf.real_toNNReal.coe_nnreal_ennreal
    refine eq_singularPart hfpos htμ.1 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
  · have hfneg : Measurable fun x => ENNReal.ofReal (-f x) :=
      -- NB: `measurability` proves this, but is slow.
      -- XXX: `fun_prop` doesn't work here yet
      (measurable_neg_iff.mpr hf).real_toNNReal.coe_nnreal_ennreal
    refine eq_singularPart hfneg htμ.2 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`t = singularPart s μ`, i.e. `t` is the singular part of the Lebesgue decomposition between
`s` and `μ`. -/
theorem eq_singularPart (t : SignedMeasure α) (f : α → ℝ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
    (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ := by
  by_cases hfi : Integrable f μ
  · refine eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ ?_
    convert hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine eq_singularPart' t measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

theorem singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ = 0 := by
  refine (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left ?_).symm
  rw [zero_add, withDensityᵥ_zero]

theorem singularPart_neg (s : SignedMeasure α) (μ : Measure α) :
    (-s).singularPart μ = -s.singularPart μ := by
  have h₁ :
    ((-s).toJordanDecomposition.posPart.singularPart μ).toSignedMeasure =
      (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure := by
    refine toSignedMeasure_congr ?_
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_posPart]
  have h₂ :
    ((-s).toJordanDecomposition.negPart.singularPart μ).toSignedMeasure =
      (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure := by
    refine toSignedMeasure_congr ?_
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_negPart]
  rw [singularPart, singularPart, neg_sub, h₁, h₂]

theorem singularPart_smul_nnreal (s : SignedMeasure α) (μ : Measure α) (r : ℝ≥0) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  rw [singularPart, singularPart, smul_sub, ← toSignedMeasure_smul, ← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart, singularPart_smul]

nonrec theorem singularPart_smul (s : SignedMeasure α) (μ : Measure α) (r : ℝ) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  cases le_or_gt 0 r with
  | inl hr =>
    lift r to ℝ≥0 using hr
    exact singularPart_smul_nnreal s μ r
  | inr hr =>
    rw [singularPart, singularPart]
    conv_lhs =>
      congr
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_posPart_neg _ _ hr, singularPart_smul]
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_negPart_neg _ _ hr, singularPart_smul]
    rw [toSignedMeasure_smul, toSignedMeasure_smul, ← neg_sub, ← smul_sub, NNReal.smul_def,
      ← neg_smul, Real.coe_toNNReal _ (le_of_lt (neg_pos.mpr hr)), neg_neg]

theorem singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s + t).singularPart μ = s.singularPart μ + t.singularPart μ := by
  refine
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        ?_).symm
  rw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ), add_assoc,
    add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]

theorem singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s - t).singularPart μ = s.singularPart μ - t.singularPart μ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, singularPart_add, singularPart_neg]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`f = rnDeriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`. -/
theorem eq_rnDeriv (t : SignedMeasure α) (f : α → ℝ) (hfi : Integrable f μ)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    f =ᵐ[μ] s.rnDeriv μ := by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  have := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi ?_).symm
  rw [← add_right_inj t, ← hadd, eq_singularPart _ f htμ hadd,
    singularPart_add_withDensity_rnDeriv_eq]

theorem rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] :
    (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg ?_
  rw [withDensityᵥ_neg, ← add_right_inj ((-s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_neg, ← neg_add,
    singularPart_add_withDensity_rnDeriv_eq]

theorem rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : ℝ) :
    (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) ?_
  rw [withDensityᵥ_smul (rnDeriv s μ) r, ← add_right_inj ((r • s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_smul, ← smul_add,
    singularPart_add_withDensity_rnDeriv_eq]

theorem rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] :
    (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) ?_
  rw [← add_right_inj ((s + t).singularPart μ), singularPart_add_withDensity_rnDeriv_eq,
    withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDeriv _ _), singularPart_add,
    add_assoc, add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]

theorem rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
    (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ := by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact ae_eq_trans (rnDeriv_add _ _ _) (Filter.EventuallyEq.add (ae_eq_refl _) (rnDeriv_neg _ _))

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is said to `HaveLebesgueDecomposition` with respect to a positive measure
if both its real and imaginary part `HaveLebesgueDecomposition` with respect to that measure. -/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  rePart : c.re.HaveLebesgueDecomposition μ
  imPart : c.im.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.rePart

attribute [instance] HaveLebesgueDecomposition.imPart

/-- The singular part between a complex measure `c` and a positive measure `μ` is the complex
measure satisfying `c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c`. This property is given
by `MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq`. -/
def singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α :=
  (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)

/-- The Radon-Nikodym derivative between a complex measure and a positive measure. -/
def rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α → ℂ := fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩

variable {c : ComplexMeasure α}

theorem integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ := by
  rw [← memLp_one_iff_integrable, ← memLp_re_im_iff]
  exact
    ⟨memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩

theorem singularPart_add_withDensity_rnDeriv_eq [c.HaveLebesgueDecomposition μ] :
    c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c := by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [VectorMeasure.add_apply, SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).integrableOn, RCLike.re_eq_complex_re,
      ← withDensityᵥ_apply _ hi]
    · change (c.re.singularPart μ + μ.withDensityᵥ (c.re.rnDeriv μ)) i = _
      rw [c.re.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _
  · rw [Complex.add_im, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.im_eq_complex_im,
      ← integral_im (c.integrable_rnDeriv μ).integrableOn, RCLike.im_eq_complex_im,
      ← withDensityᵥ_apply _ hi]
    · change (c.im.singularPart μ + μ.withDensityᵥ (c.im.rnDeriv μ)) i = _
      rw [c.im.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _

end ComplexMeasure

end MeasureTheory
