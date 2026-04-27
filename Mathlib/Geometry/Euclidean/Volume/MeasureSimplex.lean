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
* `Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior`: `Affines.Simplex.volume`
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

/-- For public version, use `Affine.Simplex.euclideanHausdorffMeasure_closedInterior`. -/
private theorem euclideanHausdorffMeasure_closedInterior' [FiniteDimensional ℝ V]
    (hn : finrank ℝ V = n + 1) (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior = (ENNReal.ofReal (n + 1 : ℕ))⁻¹ * ENNReal.ofReal (s.height i) *
    μHE[n] (s.faceOpposite i).closedInterior := by
  borelize V
  have htop : vectorSpan ℝ (Set.range s.points) = ⊤ :=
    s.independent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp [hn])
  have haltitudeFoot : s.altitudeFoot i -ᵥ s.points i ≠ 0 := by
    rw [← norm_eq_zero.ne, ← dist_eq_norm_vsub', ← height]
    exact (s.height_pos i).ne.symm
  have hshift (x : ℝ) : AffineSubspace.mk' (x • (s.altitudeFoot i -ᵥ s.points i) +ᵥ s.points i)
      (ℝ ∙ (s.altitudeFoot i -ᵥ s.points i))ᗮ =
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x := by
    convert AffineSubspace.mk'_eq ?_
    · rw [AffineSubspace.direction_shift]
      trans (affineSpan ℝ (Set.range (s.faceOpposite i).points)).direction
        ⊔ (vectorSpan ℝ (Set.range s.points))ᗮ
      · rw [← orthogonalComplement_eq_orthogonalComplement, ← inf_orthogonal,
          orthogonal_orthogonal, orthogonal_orthogonal,
          range_faceOpposite_points, direction_affineSpan, ← direction_altitude,
          ← affineSpan_pair_altitudeFoot_eq_altitude, direction_affineSpan, vectorSpan_pair]
      · simp [htop]
    rw [AffineSubspace.shift_eq ⟨s.altitudeFoot i, altitudeFoot_mem_affineSpan_faceOpposite s i⟩]
    suffices ∃ y ∈ (affineSpan ℝ (Set.range (s.faceOpposite i).points)),
        (1 - x) • (s.points i -ᵥ s.altitudeFoot i) +ᵥ y =
        x • (s.altitudeFoot i -ᵥ s.points i) +ᵥ s.points i by
      simpa
    simp only [vadd_eq_iff_eq_neg_vadd, ↓existsAndEq, and_true]
    rw [← smul_neg, neg_vsub_eq_vsub_rev, vadd_vadd, ← add_smul, sub_add_cancel, one_smul,
      vsub_vadd]
    exact altitudeFoot_mem_affineSpan_faceOpposite s i
  conv in μHE[n + 1] => rw [← hn]
  rw [EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (s.points i) haltitudeFoot
    s.measurableSet_closedInterior, enorm_eq_nnnorm, ← norm_toNNReal, ← dist_eq_norm_vsub',
    ← Simplex.height, Nat.sub_eq_of_eq_add hn]
  simp_rw [hshift]
  have hcongr : (fun x ↦ μHE[n] (s.closedInterior ∩
        (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x))
      =ᶠ[ae (MeasureSpace.volume.restrict (Set.Icc 0 1))]
      fun x ↦ ‖x‖₊ ^ n • μHE[n] (s.faceOpposite i).closedInterior := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    refine ae_restrict_of_forall_mem (by simp) fun x hx ↦ ?_
    simp only
    rw [s.closedInterior_inter_shift i (Set.mem_of_mem_of_subset hx (by grind)),
      euclideanHausdorffMeasure_homothety_image _ _ hx.1.ne.symm]
  have hsupport : Function.support (fun x ↦ μHE[n] (s.closedInterior ∩
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x)) ⊆
      Set.Icc 0 1 := by
    intro x
    contrapose
    intro hx
    rw [Function.mem_support, not_not, s.closedInterior_inter_shift_eq_empty i hx, measure_empty]
  rw [← setLIntegral_eq_of_support_subset hsupport, lintegral_congr_ae hcongr]
  simp_rw [nnreal_smul_coe_apply]
  rw [lintegral_mul_const _ (by fun_prop), ← mul_assoc]
  congrm ?_ * _
  suffices ∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n) = (ENNReal.ofReal ↑(n + 1))⁻¹ by
    rw [this, mul_comm]
    norm_cast
  suffices (∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n)).toReal = (ENNReal.ofReal ↑(n + 1))⁻¹.toReal by
    rw [ENNReal.toReal_eq_toReal_iff] at this
    apply this.resolve_right
    push +distrib Not
    exact ⟨Or.inr (by simp; grind), Or.inr (by simp)⟩
  calc
  (∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n)).toReal = ∫ (x : ℝ) in Set.Icc 0 1, ‖x‖ ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall (fun x ↦ by positivity)) (by fun_prop),
      setLIntegral_congr_fun (by simp) ?_]
    intro x hx
    simp only
    push_cast
    rw [ENNReal.ofReal_pow (by simp)]
    congrm ($norm_toNNReal.symm) ^ _
  _ = ∫ x in Set.Icc 0 1, x ^ n := by
    refine setIntegral_congr_fun (by simp) fun x hx ↦ ?_
    simpa [Real.norm_eq_abs, ← abs_pow] using abs_of_nonneg <| pow_nonneg hx.1 n
  _ = ∫ x in 0..1, x ^ n := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_Icc_eq_integral_Ioc]
  _ = _ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the volume of the face. This version is expressed in `ENNReal`.
-/
theorem euclideanHausdorffMeasure_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior =
    (.ofReal (n + 1 : ℕ))⁻¹ * .ofReal (s.height i) * μHE[n] (s.faceOpposite i).closedInterior := by
  have hn : finrank ℝ (affineSpan ℝ (Set.range s.points)).direction = n + 1 := by
    rw [← add_left_inj 1, direction_affineSpan, s.independent.finrank_vectorSpan_add_one]
    simp
  convert ← (s.restrict _ le_rfl).euclideanHausdorffMeasure_closedInterior' hn i using 0
  congrm (?_ = _ * ENNReal.ofReal ?_ * ?_)
  · rw [closedInterior_restrict, Isometry.euclideanHausdorffMeasure_preimage
      (by exact (AffineSubspace.subtypeₐᵢ _).isometry)]
    congr
    rw [Set.inter_eq_left]
    simpa using closedInterior_subset_affineSpan
  · exact (s.height_restrict _ le_rfl i)
  · rw [faceOpposite_restrict, closedInterior_restrict, Isometry.euclideanHausdorffMeasure_preimage
      (by exact (AffineSubspace.subtypeₐᵢ _).isometry)]
    congrm μHE[n] ?_
    rw [Set.inter_eq_left]
    apply closedInterior_subset_affineSpan.trans
    suffices affineSpan ℝ (s.points '' {i}ᶜ) ≤ affineSpan ℝ (Set.range s.points) by simpa
    exact affineSpan_mono _ (by simp)

/-- The volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the volume of the face. This version is expressed in `Real`.
-/
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

set_option backward.isDefEq.respectTransparency false in
/-- `Affine.Simplex.volume` is equal to the volume of the closed interior as in Euclidean Hausdorff
measure. -/
theorem volume_eq_euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P n) :
    s.volume = μHE[n].real s.closedInterior := by
  induction n with
  | zero => rw [euclideanHausdorffMeasure_closedInterior_real_eq_one, volume]
  | succ n ih => rw [volume, s.euclideanHausdorffMeasure_real_closedInterior 0, ih]

/-- `Affine.Simplex.volume` is equal to the volume of the closed interior as in Lebesgue measure. -/
theorem volume_eq_volume_real_closedInterior [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (hn : finrank ℝ V = n) (s : Simplex ℝ V n) :
    s.volume = MeasureTheory.MeasureSpace.volume.real s.closedInterior := by
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, ← hn,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Affine.Simplex
