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

In this file we define `projectiveFamily : (I : Finset ℝ≥0) → Measure (I → ℝ)`. Each
`projectiveFamily I` is the centered Gaussian measure over `I → ℝ`
with covariance matrix given by `covMatrix I s t := min s t`.
Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov's extension
theorem, which is phrased in this language.

We prove that these measures satisfy `IsProjectiveMeasureFamily`, which means that they can be
extended into a measure over `ℝ≥0 → ℝ` thanks to the Kolmogorov's extension theorem
(not in Mathlib yet). The obtained measure is a measure over the set of real processes indexed
by `ℝ≥0` and is the law of the Brownian motion.

## Main definition

* `BrownianReal.projectiveFamily I`: The centered Gaussian measure over `I → ℝ`
  with covariance matrix given by `covMatrix I s t := min s t`.

## Main statement

* `BrownianReal.isProjectiveMeasureFamily_projectiveFamily`:
  `BrownianReal.projectiveFamily` satisfies `IsProjectiveMeasureFamily`,
  which means it can be extended into a measure over `ℝ≥0 → ℝ`.

## Tags

Brownian motion, covariance matrix, projective family
-/

@[expose] public section


open MeasureTheory NormedSpace Set WithLp
open scoped ENNReal NNReal

namespace ProbabilityTheory.BrownianReal

variable {I J : Finset ℝ≥0}

/-- The covariance matrix of the finite dimensional distribution of the Brownian motion
indexed by `I`. -/
def covMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := .of fun s t ↦ min s t

@[simp]
lemma covMatrix_apply (s t : I) :
    covMatrix I s t = min s.1 t.1 := rfl

lemma covMatrix_submatrix (hJI : J ⊆ I) :
    (covMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    covMatrix J := rfl

lemma posSemidef_covMatrix (I : Finset ℝ≥0) :
    (covMatrix I).PosSemidef := by
  have : covMatrix I = .of fun s t ↦ volume.real ((Icc 0 s.1.1) ∩ (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ ↦ measurableSet_Icc)
    (fun _ ↦ isCompact_Icc.measure_ne_top)

/-- Each `projectiveFamily I` is the centered Gaussian measure with covariance matrix given
by `covMatrix I s t := min s t`.

Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov's extension
theorem, which is phrased in this language. -/
noncomputable def projectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (covMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- Up to a measurable equivalence, `projectiveFamily I` is the centered multivariate Gaussian
with covariance matrix `covMatrix I`. -/
lemma measurePreserving_ofLp_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving ofLp
      (multivariateGaussian 0 (covMatrix I)) (projectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

/-- Up to a measurable equivalence, `projectiveFamily I` is the centered multivariate Gaussian
with covariance matrix `covMatrix I`. -/
lemma measurePreserving_toLp_projectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (toLp 2) (projectiveFamily I)
      (multivariateGaussian 0 (covMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [projectiveFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

lemma integral_projectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂projectiveFamily I =
      ∫ x, f (ofLp x) ∂multivariateGaussian 0 (covMatrix I) := by
  simp [projectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_projectiveFamily]
lemma covariance_projectiveFamily (I : Finset ℝ≥0) (f g : (I → ℝ) → ℝ) :
    cov[f, g; projectiveFamily I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily, covariance_map_equiv]
  rfl

@[to_fun variance_fun_projectiveFamily]
lemma variance_projectiveFamily (I : Finset ℝ≥0) (f : (I → ℝ) → ℝ) :
    Var[f; projectiveFamily I] =
      Var[f ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily, variance_map_equiv]
  rfl

instance isGaussian_projectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (projectiveFamily I) := by
  rw [projectiveFamily,
    show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

@[simp]
lemma integral_id_projectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(projectiveFamily I) = 0 := by
  rw [integral_projectiveFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

lemma integral_id_projectiveFamily' (I : Finset ℝ≥0) :
    (projectiveFamily I)[id] = 0 := integral_id_projectiveFamily I

@[simp]
lemma integral_eval_projectiveFamily (I : Finset ℝ≥0) (s : I) :
    ∫ x, x s ∂(projectiveFamily I) = 0 := by
  conv => enter [1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
  rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_projectiveFamily, map_zero]
  exact IsGaussian.integrable_id

lemma covariance_eval_projectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; projectiveFamily I] = min s.1 t.1 := by
  rw [covariance_fun_projectiveFamily,
    covariance_eval_multivariateGaussian (posSemidef_covMatrix I),
    covMatrix_apply]

lemma variance_eval_projectiveFamily (s : I) :
    Var[fun x ↦ x s; projectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_projectiveFamily, min_self]
  exact aemeasurable_id.eval s

/-- The distribution of finite-dimensional marginals of the real Brownian motion at time `s`
is the centered Gaussian with variance `s`. -/
lemma measurePreserving_eval_projectiveFamily (s : I) :
    MeasurePreserving (fun x ↦ x s) (projectiveFamily I) (gaussianReal 0 s) where
  measurable := by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal,
      integral_eval_projectiveFamily,
      variance_eval_projectiveFamily, Real.toNNReal_coe]

/-- The distribution of the increment of the real Brownian motion from time `s` to time `t`
is the centered Gaussian with variance `t - s`. -/
lemma measurePreserving_eval_sub_eval_projectiveFamily (I : Finset ℝ≥0) (s t : I) :
    MeasurePreserving (fun x ↦ x s - x t) (projectiveFamily I)
      (gaussianReal 0 (nndist s.1 t.1)) where
  measurable := by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_projectiveFamily, variance_eval_projectiveFamily,
      covariance_eval_projectiveFamily, integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe]
      · wlog hst : (s : ℝ≥0) ≤ t generalizing s t
        · convert this t s (le_of_not_ge hst) using 1
          · rw [add_comm, min_comm]
          · rw [nndist_comm]
        grw [min_eq_left hst, NNReal.nndist_eq, max_eq_right (by grw [hst]), two_mul,
          add_tsub_add_eq_tsub_left]
      nth_grw 1 [two_mul, min_le_left, min_le_right]
    · exact (IsGaussian.hasGaussianLaw_id.eval s).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval t).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub

lemma isProjectiveMeasureFamily_projectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) projectiveFamily := by
  intro I J hJI
  nth_rw 2 [projectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this, ((measurePreserving_ofLp_multivariateGaussian J).comp
        (measurePreserving_restrict₂_multivariateGaussian (posSemidef_covMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

/-- If one restricts the finite-dimensional distribution of the real Brownian motion over a finset
`J` to a smaller finset `I`, one obtains the finite-dimensional distribution of
the real Brownian motion over `I`. -/
lemma measurePreserving_restrict_projectiveFamily (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (projectiveFamily J)
      (projectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_projectiveFamily J I hIJ |>.symm

end ProbabilityTheory.BrownianReal
