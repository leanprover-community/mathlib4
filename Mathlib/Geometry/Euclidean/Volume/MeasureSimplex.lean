/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Geometry.Euclidean.Volume.Def
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Shift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Connect the algebraic definition and measure theory for the volume of a simplex

This file proves that `Affine.Simplex.volume` agrees with the volume measure of its closed
interior.

## Main statements
* `Affine.Simplex.euclideanHausdorffMeasure_real_closedInterior`: the volume measure of the closed
  interior of a simplex satisfies the recurrence relation with base and height.
* `Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior`: `Affine.Simplex.volume`
  is equal to the volume measure of the closed interior.
-/

open MeasureTheory Measure Module Submodule

public section

namespace Affine.Simplex
variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]
variable {n : ℕ}

theorem measurableSet_closedInterior (s : Simplex ℝ P n) : MeasurableSet s.closedInterior :=
  s.isClosed_closedInterior.measurableSet

omit [MeasurableSpace P] [BorelSpace P] in
/-- Auxiliary lemma that converts the shifted plane from integral formula style
to `AffineSubspace.shift`. -/
private theorem convert_shifted_plane [FiniteDimensional ℝ V]
    (hn : finrank ℝ V = n + 1) (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) (x : ℝ) :
    -- LHS: through a point on the altitude, draw the perpendicular plane
    AffineSubspace.mk' (x • (s.altitudeFoot i -ᵥ s.points i) +ᵥ s.points i)
      (ℝ ∙ (s.altitudeFoot i -ᵥ s.points i))ᗮ =
      -- RHS: shift the base towards the vertex
      (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) x := by
  have htop : vectorSpan ℝ (Set.range s.points) = ⊤ :=
    s.independent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp [hn])
  rw [AffineSubspace.shift_eq ⟨s.altitudeFoot i, altitudeFoot_mem_affineSpan_image_compl s i⟩]
  conv in affineSpan _ _ =>
    rw [← AffineSubspace.mk'_eq (altitudeFoot_mem_affineSpan_image_compl s i)]
  rw [AffineSubspace.map_mk']
  congrm AffineSubspace.mk' ?_ ?_
  · rw [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, sub_smul, sub_eq_add_neg,
      ← smul_neg, neg_vsub_eq_vsub_rev, one_smul, add_comm (s.points i -ᵥ s.altitudeFoot i),
      add_vadd, vsub_vadd]
  · rw [AffineEquiv.linear_toAffineMap, AffineEquiv.linear_constVAdd,
      LinearEquiv.refl_toLinearMap, Submodule.map_id, ← vectorSpan_pair, ← direction_affineSpan,
      affineSpan_pair_altitudeFoot_eq_altitude, direction_altitude, htop, inf_top_eq,
      direction_affineSpan, orthogonal_orthogonal]

/-- The volume of the cross-section is scaled from the base because of homothety -/
private theorem measure_cross_section (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    (μHE[n] <| s.closedInterior ∩ (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·)
      =ᵐ[MeasureSpace.volume.restrict (Set.Icc 0 1)]
      (‖·‖₊ ^ n • μHE[n] (s.faceOpposite i).closedInterior) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem (by simp) fun x hx ↦ ?_
  simp [s.closedInterior_inter_shift_eq_homothety i (Set.Ioc_subset_Icc_self hx),
    euclideanHausdorffMeasure_homothety_image _ _ hx.1.ne.symm]

/-- Cross-section vanishes outside of the simplex. -/
private theorem cross_section_support (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    Function.support (μHE[n] <| s.closedInterior ∩
      (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·) ⊆ Set.Icc 0 1 := by
  refine Function.support_subset_iff'.mpr fun x hx ↦ ?_
  rw [(s.disjoint_closedInterior_shift i (by grind)).inter_eq, measure_empty]

/-- Simplex volume formula that requires matching dimension of the simplex and the ambient space.
For the public version without this requirement, use
`Affine.Simplex.euclideanHausdorffMeasure_closedInterior`. -/
private theorem euclideanHausdorffMeasure_closedInterior_aux [FiniteDimensional ℝ V]
    (hn : finrank ℝ V = n + 1) (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior =
      (.ofReal ↑(n + 1))⁻¹ * .ofReal (s.height i) * μHE[n] (s.faceOpposite i).closedInterior := by
  borelize V
  conv in μHE[n + 1] => rw [← hn]
  -- Convert the LHS to integrating the cross-section of the interior
  have haltitudeFoot : s.altitudeFoot i -ᵥ s.points i ≠ 0 :=
    vsub_eq_zero_iff_eq.ne.mpr (s.ne_altitudeFoot i).symm
  rw [EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (s.points i) haltitudeFoot
    s.measurableSet_closedInterior, ← ofReal_norm, ← dist_eq_norm_vsub', ← Simplex.height,
    Nat.sub_eq_of_eq_add hn]
  simp_rw [convert_shifted_plane hn s i]
  rw [← setLIntegral_eq_of_support_subset (cross_section_support s i),
    lintegral_congr_ae (measure_cross_section s i)]
  -- Cancel common factors and reduce it to `∫ x in 0..1, x ^ n`
  simp_rw [nnreal_smul_coe_apply]
  rw [lintegral_mul_const _ (by fun_prop), ← mul_assoc, mul_comm (ENNReal.ofReal (s.height i))]
  congr
  suffices (∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n)).toReal = (ENNReal.ofReal ↑(n + 1))⁻¹.toReal by
    rw [ENNReal.toReal_eq_toReal_iff] at this
    apply this.resolve_right
    push +distrib Not
    exact ⟨Or.inr (by simp; grind), Or.inr (by simp)⟩
  calc
  _ = ∫ (x : ℝ) in Set.Icc 0 1, x ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ by simp [hx.1]) (by fun_prop),
      setLIntegral_congr_fun (by simp) fun x hx ↦ ?_]
    rw [← nnnorm_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal (by simp [hx.1])]
  _ = ∫ x in 0..1, x ^ n := by
    rw [intervalIntegral.integral_of_le (by simp), integral_Icc_eq_integral_Ioc]
  _ = _ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
    simp

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `ENNReal`. -/
theorem euclideanHausdorffMeasure_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior =
      (.ofReal ↑(n + 1))⁻¹ * .ofReal (s.height i) * μHE[n] (s.faceOpposite i).closedInterior := by
  have hn : finrank ℝ (affineSpan ℝ (Set.range s.points)).direction = n + 1 := by
    rw [direction_affineSpan]
    exact s.independent.finrank_vectorSpan (by simp)
  convert ← (s.restrict _ le_rfl).euclideanHausdorffMeasure_closedInterior_aux hn i using 0
  congrm ?_ = _ * ENNReal.ofReal ?_ * ?_
  · rw [closedInterior_restrict, isometry_subtype_coe.euclideanHausdorffMeasure_preimage]
    congrm μHE[n + 1] $(by simpa using closedInterior_subset_affineSpan)
  · simp
  · rw [faceOpposite_restrict, closedInterior_restrict,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage]
    congrm μHE[n] ?_
    rw [Set.inter_eq_left]
    apply (s.closedInterior_faceOpposite_subset_closedInterior i).trans
    simpa using closedInterior_subset_affineSpan

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `Real`. -/
theorem euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1].real s.closedInterior =
      (↑(n + 1))⁻¹ * s.height i * μHE[n].real (s.faceOpposite i).closedInterior := by
  simp_rw [measureReal_def]
  rw [s.euclideanHausdorffMeasure_closedInterior i, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (s.height_pos i).le, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]

theorem euclideanHausdorffMeasure_closedInterior_eq_one (s : Simplex ℝ P 0) :
    μHE[0] s.closedInterior = 1 := by
  simp

theorem euclideanHausdorffMeasure_closedInterior_real_eq_one (s : Simplex ℝ P 0) :
    μHE[0].real s.closedInterior = 1 := by
  simp [real_def]

/-- `Affine.Simplex.volume` is equal to the Euclidean Hausdorff measure of the closed interior. -/
theorem volume_eq_euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P n) :
    s.volume = μHE[n].real s.closedInterior := by
  induction n with
  | zero => rw [euclideanHausdorffMeasure_closedInterior_real_eq_one, volume]
  | succ n ih => simp [volume, s.euclideanHausdorffMeasure_real_closedInterior 0, ih]

/-- `Affine.Simplex.volume` is equal to the Lebesgue measure of the closed interior. -/
theorem volume_eq_volume_real_closedInterior [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (hn : finrank ℝ V = n) (s : Simplex ℝ V n) :
    s.volume = MeasureTheory.MeasureSpace.volume.real s.closedInterior := by
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, ← hn,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Affine.Simplex
