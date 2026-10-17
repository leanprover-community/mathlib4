/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Geometry.Euclidean.CornerSimplex
public import Mathlib.Geometry.Euclidean.Volume.Def

import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex

/-!
# Volume of a simplex

This file provides lemmas related to the volume of a simplex.

## Main statements
* `Affine.Simplex.volume_eq`: The volume of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the volume of the face.
* `Affine.Simplex.volume_eq_volumeForm`: The volume of a $n$-simplex is the absolute value of
`Orientation.volumeForm` divided by $n!$.
-/

public section

open MeasureTheory Measure Module Nat

namespace Affine.Simplex

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable {V₂ P₂ : Type*}
variable [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

@[simp]
theorem volume_eq_one (s : Simplex ℝ P 0) : s.volume = 1 := rfl

@[simp]
theorem volume_eq_dist (s : Simplex ℝ P 1) : s.volume = dist (s.points 0) (s.points 1) := by
  simp [volume]

theorem volume_eq {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.volume = (↑n)⁻¹ * s.height i * (s.faceOpposite i).volume := by
  obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr (NeZero.pos n)
  borelize P
  simp [volume_eq_euclideanHausdorffMeasure_real_closedInterior,
    s.euclideanHausdorffMeasure_real_closedInterior i]

@[simp]
theorem volume_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).volume = s.volume := by
  borelize P
  have hnm : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, hnm, closedInterior_reindex]

@[simp]
theorem volume_map {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).volume = s.volume := by
  induction n with
  | zero => simp
  | succ n ih => simp [volume_eq _ 0, height_map, faceOpposite_map, ih]

@[simp]
theorem volume_restrict {n : ℕ} (s : Simplex ℝ P n) {S : AffineSubspace ℝ P}
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).volume = s.volume := by
  induction n with
  | zero => simp
  | succ n ih => simp [volume_eq _ 0, height_restrict, faceOpposite_restrict, ih]

@[simp]
theorem volume_pos {n : ℕ} (s : Simplex ℝ P n) : 0 < s.volume := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [volume_eq _ 0]
    positivity [ih (s.faceOpposite 0)]

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the volume of a simplex is always positive. -/
@[positivity volume _]
meta def evalVolume : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@volume $V $P $i1 $i2 $i3 $i4 $n $s) =>
    assertInstancesCommute
    return .positive q(volume_pos $s)
  | _, _, _ => throwError "not Simplex.volume"

theorem volume_map_of_finrank_eq [FiniteDimensional ℝ V] {n : ℕ} (hn : finrank ℝ V = n)
    (s : Simplex ℝ P n) {f : P →ᵃ[ℝ] P₂} (hf : Function.Injective f) :
    (s.map f hf).volume = f.linear.normDet * s.volume := by
  borelize P P₂
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, closedInterior_map, ← hn,
    Measure.real_def, f.euclideanHausdorffMeasure_image]
  simp [f.linear.normDet_nonneg]

@[simp]
theorem volume_cornerSimplex (n : ℕ) : (cornerSimplex n).volume = (↑(n !))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [volume_eq _ (0 : Fin (n + 1)).succ, faceOpposite_cornerSimplex, volume_map, ih]
    simp [Nat.factorial_succ, mul_comm]

theorem volume_eq_volumeForm {n : ℕ} [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)]
    (o : Orientation ℝ V (Fin n)) (s : Simplex ℝ P n) :
    s.volume = (↑(n !))⁻¹ * |o.volumeForm fun i ↦ s.points i.succ -ᵥ s.points 0| := by
  conv_lhs => rw [← s.map_cornerSimplex_cornerMap, volume_map_of_finrank_eq (by simp),
    volume_cornerSimplex, mul_comm s.cornerMap.linear.normDet, s.normDet_cornerMap_linear o]

end Affine.Simplex
