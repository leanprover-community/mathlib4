/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Geometry.Euclidean.Volume.Def

import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex

/-!
# Volume of a simplex

This file provides lemmas related to the volume of a simplex.

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

theorem volume_map_of_finrank_eq [FiniteDimensional ℝ V] {n : ℕ} (hn : Module.finrank ℝ V = n)
    (s : Simplex ℝ P n) {f : P →ᵃ[ℝ] P₂} (hf : Function.Injective f) :
    (s.map f hf).volume = f.linear.normDet * s.volume := by
  borelize P P₂ V V₂
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, closedInterior_map, ← hn,
    Measure.real_def]
  have : f = AffineIsometryEquiv.vaddConst ℝ (f (s.points 0)) ∘ f.linear ∘
      (AffineIsometryEquiv.vaddConst ℝ (s.points 0)).symm := by
    ext x
    simp
  rw [this, Set.image_comp, Set.image_comp,
    Isometry.euclideanHausdorffMeasure_image (AffineIsometryEquiv.isometry _),
    LinearMap.euclideanHausdorffMeasure_image,
    Isometry.euclideanHausdorffMeasure_image (AffineIsometryEquiv.isometry _)]
  simp [f.linear.normDet_nonneg]

@[simps]
private noncomputable def corner (n : ℕ) : Simplex ℝ (EuclideanSpace ℝ (Fin n)) n where
  points i := if h : i = 0 then 0 else EuclideanSpace.single (Fin.pred i h) 1
  independent := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
    convert_to LinearIndependent ℝ ((fun i : Fin n ↦ EuclideanSpace.single i (1 : ℝ)) ∘
      (fun i : { x : Fin (n + 1) // x ≠ 0 } ↦ Fin.pred i.val i.prop))
    · simp
      grind
    exact (PiLp.linearIndependent_single_one 2 ℝ).comp _ (fun i j ↦ by grind)

private theorem faceOpposite_corner_last_eq_map (n : ℕ) :
    (corner (n + 1)).faceOpposite (Fin.last (n + 1)) =
      (corner n).map
      (LinearIsometry.piLpExtendByZero 2 ℝ ℝ Fin.castSuccEmb).toAffineIsometry.toAffineMap
      (LinearIsometry.piLpExtendByZero 2 ℝ ℝ Fin.castSuccEmb).toAffineIsometry.injective := by
  ext1 i
  by_cases hi : i = 0
  · simp [faceOpposite_point_eq_point_succAbove, hi]
  simp [faceOpposite_point_eq_point_succAbove, hi, Fin.castSucc_pred_eq_pred_castSucc hi]

@[simp]
private theorem volume_faceOpposite_corner_last (n : ℕ) :
    ((corner (n + 1)).faceOpposite (Fin.last (n + 1))).volume = (corner n).volume := by
  rw [faceOpposite_corner_last_eq_map, volume_map]

@[simp]
private theorem altitudeFoot_corner (n : ℕ) [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    (corner n).altitudeFoot i = 0 := by
  rw [altitudeFoot, orthogonalProjectionSpan, EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
  constructor
  · apply mem_affineSpan
    simp [hi.symm]
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ (p := 0) (by simp [hi.symm])] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ : ∃ j, j ≠ i ∧
        (if h : j = 0 then 0 else EuclideanSpace.single (j.pred h) 1) = x := by
      simpa using hx
    by_cases hj0 : j = 0
    · simp [hj0]
    simp [hj0, hj, EuclideanSpace.inner_single_left, hi]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [inner_add_left, ihx, ihy, zero_add]
  | smul a x hx ih =>
    rw [inner_smul_left, ih, mul_zero]

@[simp]
private theorem height_corner (n : ℕ) [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    (corner n).height i = 1 := by
  simp [height, hi]

private theorem volume_corner (n : ℕ) : (corner n).volume = (↑n.factorial)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [volume_eq _ (Fin.last _), ih, Nat.factorial_succ, mul_comm]

private noncomputable def cornerMap {n : ℕ} (s : Simplex ℝ P n) :
    EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] P :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ
    fun i ↦ s.points i.succ -ᵥ s.points 0).toAffineMap +ᵥ
  AffineMap.const ℝ (EuclideanSpace ℝ (Fin n)) (s.points 0)

private theorem cornerMap_injective {n : ℕ} (s : Simplex ℝ P n) :
    Function.Injective (cornerMap s) := by
  intro x y h
  simp_rw [cornerMap, AffineMap.vadd_apply, AffineMap.const_apply, vadd_right_cancel_iff] at h
  refine (Module.Basis.injective_constr_of_linearIndependent _ ?_ (R₂ := ℝ)) h
  convert ((affineIndependent_iff_linearIndependent_vsub ℝ _ 0).mp s.independent).comp
    (fun i : Fin n ↦ ⟨i.succ, by simp⟩) (fun i j ↦ by simp)
  simp

private theorem map_corner_cornerMap {n : ℕ} (s : Simplex ℝ P n) :
    (corner n).map (cornerMap s) (cornerMap_injective s) = s := by
  ext1 i
  by_cases hi : i = 0 <;> simp [hi, cornerMap]

theorem volume_eq_volumeForm {n : ℕ} [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = n)]
    (o : Orientation ℝ V (Fin n)) (s : Simplex ℝ P n) :
    s.volume = (↑n.factorial)⁻¹ * |o.volumeForm fun i ↦ s.points i.succ -ᵥ s.points 0| := by
  rw [← s.map_corner_cornerMap, volume_map_of_finrank_eq (by simp), volume_corner,
    mul_comm s.cornerMap.linear.normDet]
  congrm _ * ?_
  suffices s.cornerMap.linear.normDet =
      |o.volumeForm fun i ↦ s.cornerMap.linear (EuclideanSpace.single i 1)| by
    simpa [← AffineMap.linearMap_vsub]
  let b : OrthonormalBasis (Fin n) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr ‹Fact (Module.finrank ℝ V = n)›.out)
  rw [s.cornerMap.linear.normDet_eq_norm_det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ) b,
    Real.norm_eq_abs, o.volumeForm_robust' b]
  rfl

end Affine.Simplex
