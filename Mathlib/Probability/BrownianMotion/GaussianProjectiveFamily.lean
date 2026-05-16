/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Finite dimensional distributions of Brownian motion

In this file we define `gaussianProjectiveFamily : (I : Finset ℝ≥0) → Measure (I → ℝ)`. Each
`gaussianProjectiveFamily I` is the centered Gaussian measure over `I → ℝ`
with covariance matrix given by `brownianCovMatrix I s t := min s t`.

We prove that these measures satisfy `IsProjectiveMeasureFamily`, which means that they can be
extended into a measure over `ℝ≥0 → ℝ` thanks to the Kolmogorov's extension theorem
(not in Mathlib yet). The obtained measure is a measure over the set of real processes indexed
by `ℝ≥0` and is the law of the Brownian motion.

-/

@[expose] public section


open MeasureTheory NormedSpace Set WithLp
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {I J : Finset ℝ≥0}

/-- The covariance matrix of the finite dimensional distribution of the Brownian motion
indexed by `I`. -/
def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := .of fun s t ↦ min s t

@[simp]
lemma brownianCovMatrix_apply (s t : I) :
    brownianCovMatrix I s t = min s.1 t.1 := rfl

lemma brownianCovMatrix_submatrix (hJI : J ⊆ I) :
    (brownianCovMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    brownianCovMatrix J := rfl

lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have : brownianCovMatrix I = .of fun s t ↦ volume.real ((Icc 0 s.1.1) ∩ (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ ↦ measurableSet_Icc)
    (fun _ ↦ isCompact_Icc.measure_ne_top)

/-- Each `gaussianProjectiveFamily I` is the centered Gaussian measure with covariance matrix given
by `brownianCovMatrix I s t := min s t`. -/
noncomputable def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

lemma measurePreserving_ofLp_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving ofLp
      (multivariateGaussian 0 (brownianCovMatrix I)) (gaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

lemma measurePreserving_equiv_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (toLp 2) (gaussianProjectiveFamily I)
      (multivariateGaussian 0 (brownianCovMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [gaussianProjectiveFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂gaussianProjectiveFamily I =
      ∫ x, f (ofLp x) ∂multivariateGaussian 0 (brownianCovMatrix I) := by
  simp [gaussianProjectiveFamily, integral_map_equiv]

@[to_fun]
lemma covariance_gaussianProjectiveFamily (I : Finset ℝ≥0) (f g : (I → ℝ) → ℝ) :
    cov[f, g; gaussianProjectiveFamily I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (brownianCovMatrix I)] := by
  rw [gaussianProjectiveFamily, covariance_map_equiv]
  rfl

@[to_fun]
lemma variance_gaussianProjectiveFamily (I : Finset ℝ≥0) (f : (I → ℝ) → ℝ) :
    Var[f; gaussianProjectiveFamily I] =
      Var[f ∘ ofLp; multivariateGaussian 0 (brownianCovMatrix I)] := by
  rw [gaussianProjectiveFamily, variance_map_equiv]
  rfl

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  rw [gaussianProjectiveFamily,
    show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

@[simp]
lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

lemma integral_id_gaussianProjectiveFamily' (I : Finset ℝ≥0) :
    ∫ x, id x ∂(gaussianProjectiveFamily I) = 0 := integral_id_gaussianProjectiveFamily I

@[simp]
lemma integral_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s : I) :
    ∫ x, x s ∂(gaussianProjectiveFamily I) = 0 := by
  conv => enter [1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
  rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
  exact IsGaussian.integrable_id

lemma covariance_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianProjectiveFamily I] = min s.1 t.1 := by
  rw [fun_covariance_gaussianProjectiveFamily,
    covariance_eval_multivariateGaussian (posSemidef_brownianCovMatrix I),
    brownianCovMatrix_apply]

set_option backward.isDefEq.respectTransparency false in
lemma variance_eval_gaussianProjectiveFamily (s : I) :
    Var[fun x ↦ x s; gaussianProjectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_gaussianProjectiveFamily, min_self]
  exact aemeasurable_id.eval s

lemma measurePreserving_eval_gaussianProjectiveFamily (s : I) :
    MeasurePreserving (fun x ↦ x s) (gaussianProjectiveFamily I) (gaussianReal 0 s) where
  measurable := by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal,
      integral_eval_gaussianProjectiveFamily,
      variance_eval_gaussianProjectiveFamily, Real.toNNReal_coe]

set_option backward.isDefEq.respectTransparency false in
open ContinuousLinearMap in
lemma measurePreserving_eval_sub_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    MeasurePreserving ((fun x ↦ x s - x t)) (gaussianProjectiveFamily I)
      (gaussianReal 0 (max (s - t) (t - s))) where
  measurable := by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_gaussianProjectiveFamily, variance_eval_gaussianProjectiveFamily,
      covariance_eval_gaussianProjectiveFamily, integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe]
      · wlog hst : (s : ℝ≥0) ≤ t generalizing s t
        · convert this t s (le_of_not_ge hst) using 1
          · rw [add_comm, min_comm]
          · rw [max_comm]
        grw [min_eq_left hst, max_eq_right (by grw [hst]), two_mul, add_tsub_add_eq_tsub_left]
      nth_grw 1 [two_mul, min_le_left, min_le_right]
    · exact (IsGaussian.hasGaussianLaw_id.eval s).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval t).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub

lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_ofLp_multivariateGaussian J).comp
      (measurePreserving_restrict₂_multivariateGaussian
        (posSemidef_brownianCovMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

lemma measurePreserving_restrict_gaussianProjectiveFamily (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (gaussianProjectiveFamily J)
      (gaussianProjectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_gaussianProjectiveFamily J I hIJ |>.symm

end ProbabilityTheory
