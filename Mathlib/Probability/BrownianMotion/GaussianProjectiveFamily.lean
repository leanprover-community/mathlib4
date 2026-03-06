/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Pre-Brownian motion as a projective limit

-/

@[expose] public section


open MeasureTheory NormedSpace Set
open scoped ENNReal NNReal

namespace L2

variable {ι : Type*} [Finite ι]
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/- In an `L2` space, the matrix of intersections of pairs of sets is positive semi-definite. -/
theorem posSemidef_interMatrix {μ : Measure α} {v : ι → (Set α)}
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (v i ∩ v j)) := by
  simp only [hv₁, ne_eq, hv₂, not_false_eq_true,
    ← L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram ℝ _

end L2

namespace ProbabilityTheory

variable {ι : Type*} {d : ℕ}

def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := Matrix.of fun s t ↦ min s.1 t.1

lemma brownianCovMatrix_apply {I : Finset ℝ≥0} (s t : I) :
    brownianCovMatrix I s t = min s.1 t.1 := rfl

lemma brownianCovMatrix_submatrix {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (brownianCovMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    brownianCovMatrix J := rfl

lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have h : brownianCovMatrix I =
      fun s t ↦ volume.real ((Icc 0 s.1.toReal) ∩ (Icc 0 t.1.toReal)) := by
    simp [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  exact h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ isCompact_Icc.measure_ne_top)

variable [DecidableEq ι]

noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

lemma measurePreserving_equiv_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm
      (multivariateGaussian 0 (brownianCovMatrix I)) (gaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

lemma measurePreserving_equiv_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm.symm (gaussianProjectiveFamily I)
      (multivariateGaussian 0 (brownianCovMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [gaussianProjectiveFamily, Measure.map_map, MeasurableEquiv.symm_comp_self,
      Measure.map_id]
    all_goals fun_prop

lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂gaussianProjectiveFamily I =
      ∫ x, f (EuclideanSpace.equiv I ℝ x)
        ∂multivariateGaussian 0 (brownianCovMatrix I) := by
  simp only [gaussianProjectiveFamily, integral_map_equiv, MeasurableEquiv.toLp_symm_apply]
  rfl

instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  rw [show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

@[simp]
lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]

lemma integral_id_gaussianProjectiveFamily' (I : Finset ℝ≥0) :
    ∫ x, id x ∂(gaussianProjectiveFamily I) = 0 := integral_id_gaussianProjectiveFamily I

open scoped RealInnerProductSpace in
lemma covariance_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianProjectiveFamily I] = min s.1 t.1 := by
  rw [gaussianProjectiveFamily, covariance_map_equiv]
  change cov[fun x : EuclideanSpace ℝ I ↦ x s, fun x ↦ x t; _] = _
  have (u : I) : (fun x : EuclideanSpace ℝ I ↦ x u) =
      fun x ↦ ⟪EuclideanSpace.basisFun I ℝ u, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov,
    covarianceBilin_multivariateGaussian (posSemidef_brownianCovMatrix I),
    ContinuousBilinForm.ofMatrix_orthonormalBasis, brownianCovMatrix_apply]
  exact IsGaussian.memLp_two_id

lemma variance_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    Var[fun x ↦ x s; gaussianProjectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_gaussianProjectiveFamily, min_self]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    HasLaw (fun x ↦ x s) (gaussianReal 0 s) (gaussianProjectiveFamily I) where
  aemeasurable := Measurable.aemeasurable <| by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_eval_gaussianProjectiveFamily,
      Real.toNNReal_coe]
    swap
    · exact IsGaussian.hasGaussianLaw_id.eval s
    conv => enter [1, 1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
    rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
    exact IsGaussian.integrable_id

open ContinuousLinearMap in
lemma hasLaw_eval_sub_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    HasLaw ((fun x ↦ x s - x t)) (gaussianReal 0 (max (s - t) (t - s)))
      (gaussianProjectiveFamily I) where
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_gaussianProjectiveFamily, variance_eval_gaussianProjectiveFamily,
      covariance_eval_gaussianProjectiveFamily]
    · conv =>
        enter [1, 1, 2];
        change fun x ↦ (proj (R := ℝ) (φ := fun i : I ↦ ℝ) s -
          proj (R := ℝ) (φ := fun i : I ↦ ℝ) t) x
      rw [integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
      · norm_cast
        rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe,
          NNReal.add_sub_two_mul_min_eq_max]
        nth_grw 1 [two_mul, min_le_left, min_le_right]
      · exact IsGaussian.integrable_id
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub

lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        (MeasurableEquiv.toLp 2 (J → ℝ)).symm ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_equiv_multivariateGaussian J).comp
      (measurePreserving_restrict_multivariateGaussian
        (posSemidef_brownianCovMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

lemma measurePreserving_restrict_gaussianProjectiveFamily {I J : Finset ℝ≥0} (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (gaussianProjectiveFamily J)
      (gaussianProjectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_gaussianProjectiveFamily J I hIJ |>.symm
