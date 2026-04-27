/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Def
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex

/-!
# Volume of a simplex

This file provides lemma related to the volume of a simplex.

## Main statements
* `Affine.Simplex.volume_eq`: The volume of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the volume of the face.
-/

public section

open MeasureTheory Measure

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
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  conv_lhs => rw [volume_eq _ 0]
  conv_rhs => rw [volume_eq _ 0]
  rw [height_map, faceOpposite_map, volume_map]

@[simp]
theorem volume_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).volume = s.volume := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  conv_lhs => rw [volume_eq _ 0]
  conv_rhs => rw [volume_eq _ 0]
  rw [height_restrict, faceOpposite_restrict, volume_restrict]

@[simp]
theorem volume_pos {n : ℕ} (s : Simplex ℝ P n) : 0 < s.volume := by
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  rw [volume_eq _ 0]
  have : 0 < (s.faceOpposite 0).volume := volume_pos _
  positivity

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the volume of a simplex is always positive. -/
@[positivity volume _]
meta def evalVolume : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@volume $V $P $i1 $i2 $i3 $i4 $n $s) =>
    assertInstancesCommute
    return .positive q(volume_pos $s)
  | _, _, _ => throwError "not Simplex.volume"

end Affine.Simplex
