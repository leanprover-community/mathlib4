/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Nine-point circle

This file defines the nine-point circle of a triangle, and its higher dimension analogue, the
3(n+1)-point sphere of a simplex. Specifically for triangles, we show that it passes through nine
specific points as desired.

## Main definitions
* `Affine.Simplex.ninePointCircle`: the 3(n+1)-point sphere of a simplex.
* `Affine.Simplex.eulerPoint`: the $1/n$th of the way from the Monge point to a vertex.
* `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`: the 3(n+1)-point sphere passes through
  the centroid of each face of the simplex
* `Affine.Simplex.eulerPoint_mem_ninePointCircle`: the 3(n+1)-point sphere passes through all Euler
  points.
* `Affine.Triangle.altitudeFoot_mem_ninePointCircle`: the nine-point circle passes through all
  three altitude feet of the triangle.

## References
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)
-/

@[expose] public section

noncomputable section

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

/--
The 3(n+1)-point sphere of a simplex. Due to the lack of a better name and to avoid numbers in the
identifier, we still use the name "nine-point circle" even for higher dimensions. The center
$N$ is defined on the Euler line, collinear with circumcenter $O$ and centroid $G$, in the order of
$O$, $G$, and $N$, with $OG : GN = n : 1$. The radius is $1/n$ of the circumradius.
-/
def ninePointCircle {n : ℕ} (s : Simplex ℝ P n) : Sphere P where
  center := ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : ℝ)

theorem ninePointCircle_center {n : ℕ} (s : Simplex ℝ P n) : s.ninePointCircle.center =
    ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter := rfl

theorem ninePointCircle_center_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.ninePointCircle.center ∈ affineSpan ℝ (Set.range s.points) := by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan

theorem ninePointCircle_radius {n : ℕ} (s : Simplex ℝ P n) :
    s.ninePointCircle.radius = s.circumradius / (n : ℝ) := rfl

@[simp]
theorem ninePointCircle_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).ninePointCircle = s.ninePointCircle := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]

theorem ninePointCircle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).ninePointCircle =
    { center := f s.ninePointCircle.center, radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]

theorem ninePointCircle_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]

theorem faceOppositeCentroid_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.faceOppositeCentroid i ∈ s.ninePointCircle := by
  rw [mem_sphere, ninePointCircle_center, ninePointCircle_radius,
    ← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [eq_div_iff_mul_eq (by simpa using NeZero.ne n), mul_comm]
  nth_rw 1 [show (n : ℝ) = ‖(n : ℝ)‖ by simp]
  rw [← norm_smul, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul,
    mul_div_cancel₀ _ (by simpa using NeZero.ne n), add_smul, one_smul, ← sub_sub, ← smul_sub,
    vsub_sub_vsub_cancel_right, ← centroid_vsub_point_eq_smul_vsub, vsub_sub_vsub_cancel_left]

theorem ninePointCircle_eq_circumsphere_medial {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    s.ninePointCircle = s.medial.circumsphere := by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

/-- Euler points are a set of points that the `ninePointCircle` passes through. They are defined as
being $1/n$th of the way from the Monge point to a vertex. Specifically for triangles, these are
the midpoints between the orthocenter and a given vertex
(`Affine.Triangle.eulerPoint_eq_midpoint`). -/
def eulerPoint {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :=
  (n : ℝ)⁻¹ • (s.points i -ᵥ s.mongePoint) +ᵥ s.mongePoint

@[simp]
theorem eulerPoint_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).eulerPoint = s.eulerPoint ∘ e.symm := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]
theorem eulerPoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).eulerPoint i = f (s.eulerPoint i) := by
  simp [eulerPoint]

@[simp]
theorem eulerPoint_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  simp [eulerPoint]

theorem points_vsub_eulerPoint {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.eulerPoint i = ((n - 1) / n : ℝ) • (s.points i -ᵥ s.mongePoint) := by
  rw [eulerPoint, vsub_vadd_eq_vsub_sub]
  by_cases hn : n = 0
  · obtain rfl := hn
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hi : i = 0 := Subsingleton.eq_zero i
    have hrange : Set.range s.points = {s.points i} := by simp [hi]
    obtain hmonge := s.mongePoint_mem_affineSpan
    rw [hrange, mem_affineSpan_singleton] at hmonge
    simp [hmonge]
  have : ((n - 1) / n : ℝ) = 1 - (n : ℝ)⁻¹ := by
    rw [sub_div, div_self (by simpa using hn), one_div]
  rw [this, sub_smul, one_smul]

theorem midpoint_faceOppositeCentroid_eulerPoint {n : ℕ} [hn : NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    midpoint ℝ (s.faceOppositeCentroid i) (s.eulerPoint i) = s.ninePointCircle.center := by
  apply vsub_left_cancel (p := s.circumcenter)
  rw [ninePointCircle_center, midpoint_vsub, vadd_vsub, eulerPoint,
    mongePoint_eq_smul_vsub_vadd_circumcenter, ← centroid]
  by_cases hn1 : n = 1
  · obtain rfl := hn1
    suffices (2⁻¹ : ℝ) • (s.faceOppositeCentroid i -ᵥ s.centroid) +
        (2⁻¹ : ℝ) • (s.points i -ᵥ s.centroid) = 0 by
      simpa [circumcenter_eq_centroid, centroid]
    rw [faceOppositeCentroid_vsub_centroid_eq_smul_vsub, ← smul_add]
    exact (smul_eq_zero_of_right _ (by simp))
  have hltn : 1 < n := by
    have _ := hn.out
    lia
  have hnsub1 : (n - 1 : ℕ) = (n : ℝ) - 1 := by
    push_cast [hltn]
    rfl
  rw [vadd_vadd, vadd_vsub, vsub_vadd_eq_vsub_sub, smul_sub, sub_add, smul_smul, ← sub_smul,
    ← sub_one_mul, show ((n : ℝ)⁻¹ - 1) = -(n - 1) / n by field [hn.out],
    neg_div, neg_mul, hnsub1, div_mul_div_cancel₀' (by simpa [sub_eq_zero] using hn1),
    neg_smul, sub_neg_eq_add, faceOppositeCentroid_eq_smul_vsub_vadd_point,
    ← smul_add, vadd_vsub_assoc, add_add_add_comm, ← smul_add, vsub_add_vsub_cancel, ← add_assoc]
  push_cast
  have : (n : ℝ)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) =
      (((n + 1) / n : ℝ)) • (s.centroid -ᵥ s.circumcenter) := by
    rw [add_comm (n : ℝ) 1, add_div, div_self (by simpa using hn.out), add_smul, one_smul, one_div]
  rw [this, ← two_smul ℝ, smul_smul]
  norm_num

theorem isDiameter_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.ninePointCircle.IsDiameter (s.faceOppositeCentroid i) (s.eulerPoint i) where
  left_mem := s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i

theorem eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.eulerPoint i ∈ s.ninePointCircle :=
  (s.isDiameter_ninePointCircle i).right_mem

theorem orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n]
    (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    ((s.faceOpposite i).orthogonalProjectionSpan (s.eulerPoint i)).val ∈ s.ninePointCircle := by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i), orthogonalProjectionSpan]
  exact angle_orthogonalProjection_self _ <| faceOppositeCentroid_mem_affineSpan_face s i

end Affine.Simplex

namespace Affine.Triangle

theorem eulerPoint_eq_midpoint (s : Triangle ℝ P) (i : Fin 3) :
    s.eulerPoint i = midpoint ℝ s.orthocenter (s.points i) := by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint, Simplex.points_vsub_eulerPoint, vsub_midpoint]
  norm_num

theorem altitudeFoot_mem_ninePointCircle (s : Triangle ℝ P) (i : Fin 3) :
    s.altitudeFoot i ∈ s.ninePointCircle := by
  convert s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem,
    Simplex.points_vsub_eulerPoint, Submodule.smul_mem_iff _ (by norm_num),
    ← orthocenter_eq_mongePoint, direction_affineSpan, Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

end Affine.Triangle

end
