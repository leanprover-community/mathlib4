/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Def
public import Mathlib.Geometry.Euclidean.Volume.Measure

import Mathlib.Geometry.Euclidean.Volume.Cone

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

open MeasureTheory Measure Module Submodule AffineSubspace
open scoped ENNReal NNReal

public section

namespace Affine.Simplex
variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]
variable {n : ℕ}

theorem measurableSet_closedInterior (s : Simplex ℝ P n) : MeasurableSet s.closedInterior :=
  s.isClosed_closedInterior.measurableSet

/-- The volume of the cross section of a simplex is scaled from the base. This is an intermediate
result for volume calculation and is expressed as a.e.-equal to take care of the exception at zero.

TODO: if the cross section object also shows up elsewhere, we should turn it to a proper definition.
-/
theorem euclideanHausdorffMeasure_closedInterior_inter_shift_aeEq (s : Simplex ℝ P (n + 1))
    (i : Fin (n + 2)) :
    (μHE[n] <| s.closedInterior ∩ (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·)
      =ᵐ[MeasureSpace.volume.restrict (Set.Icc 0 1)]
        (‖·‖₊ ^ n • μHE[n] (s.faceOpposite i).closedInterior) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem (by simp) fun x hx ↦ ?_
  simp [s.closedInterior_inter_shift_eq_homothety i (Set.Ioc_subset_Icc_self hx),
    euclideanHausdorffMeasure_homothety_image _ _ hx.1.ne.symm]

/-- The cross section of a simplex vanishes outside of the simplex in terms of its volume. -/
theorem support_euclideanHausdorffMeasure_closedInterior_inter_shift_subset
    (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    Function.support (μHE[n] <| s.closedInterior ∩
      (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·) ⊆ Set.Icc 0 1 := by
  refine Function.support_subset_iff'.mpr fun x hx ↦ ?_
  rw [(s.disjoint_closedInterior_shift i (by grind)).inter_eq, measure_empty]

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `ENNReal`. -/
theorem euclideanHausdorffMeasure_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * .ofReal (s.height i) * μHE[n] (s.faceOpposite i).closedInterior := by
  have hn : finrank ℝ (affineSpan ℝ (Set.range s.points)).direction = n + 1 := by
    rw [direction_affineSpan]
    exact s.independent.finrank_vectorSpan (by simp)
  rw [s.closedInterior_eq_iUnion_homothety i]
  exact EuclideanGeometry.euclideanHausdorffMeasure_cone
    (affineSpan_mono _ (by rw [range_faceOpposite_points]; exact Set.image_subset_range _ _))
    hn (mem_affineSpan _ (Set.mem_range_self i)) (s.points_notMem_affineSpan_faceOpposite i)
    (s.faceOpposite i).closedInterior_subset_affineSpan
    (s.faceOpposite i).measurableSet_closedInterior

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `Real`. -/
theorem euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1].real s.closedInterior =
      (↑(n + 1))⁻¹ * s.height i * μHE[n].real (s.faceOpposite i).closedInterior := by
  simp_rw [measureReal_def]
  rw [s.euclideanHausdorffMeasure_closedInterior i, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (s.height_pos i).le, ENNReal.toReal_inv, ENNReal.toReal_natCast]

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
