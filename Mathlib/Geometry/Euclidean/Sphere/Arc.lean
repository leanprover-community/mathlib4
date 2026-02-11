/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

/-!
# Arcs on Spheres

This file defines arcs on spheres and proves basic properties.

## Main definitions

* `EuclideanGeometry.Sphere.Arc`: An arc on a sphere, defined by a left endpoint and a midpoint.
* `EuclideanGeometry.Sphere.Arc.opposite`: The opposite arc sharing the same endpoints.
* `EuclideanGeometry.Sphere.Arc.minor`: The minor arc between two non-diametrically-opposite points.
* `EuclideanGeometry.Sphere.Arc.major`: The major arc between two non-diametrically-opposite points.
* `EuclideanGeometry.Sphere.Arc.through`: The arc from `A` to `C` passing through `B`.
* `EuclideanGeometry.Sphere.Arc.avoiding`: The arc from `A` to `C` not passing through `B`.
-/

@[expose] public section

namespace EuclideanGeometry

namespace Sphere

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

noncomputable section

/-- An arc on a sphere, defined by a left endpoint and a midpoint on the sphere.
The right endpoint is computed as the reflection of the left endpoint across the line through the
center and midpoint. -/
structure Arc (s : Sphere P) where
  /-- The left endpoint of the arc. -/
  left : P
  /-- A point on the arc (used to distinguish which arc between the endpoints). -/
  midpoint : P
  /-- Proof that left endpoint lies on the sphere. -/
  left_mem : left ∈ s
  /-- Proof that midpoint lies on the sphere. -/
  midpoint_mem : midpoint ∈ s

namespace Arc

variable {s : Sphere P}

/-- The right endpoint of an arc, computed as the reflection of the left endpoint
across the line through the center and midpoint. -/
def right (a : Arc s) : P :=
  reflection (line[ℝ, s.center, a.midpoint]) a.left

lemma right_eq_reflection (a : Arc s) :
  a.right = reflection (line[ℝ, s.center, a.midpoint]) a.left := rfl

lemma right_mem (a : Arc s) : a.right ∈ s := by
  rw [mem_sphere, right_eq_reflection]
  have h_center_mem : s.center ∈ line[ℝ, s.center, a.midpoint] :=
    left_mem_affineSpan_pair ℝ s.center a.midpoint
  rw [dist_comm, dist_reflection_eq_of_mem _ h_center_mem, ← a.left_mem, dist_comm]

lemma left_eq_right_iff_mem_line (a : Arc s) :
    a.left = a.right ↔ a.left ∈ line[ℝ, s.center, a.midpoint] := by
  rw [right_eq_reflection, eq_comm]
  haveI : Nonempty (line[ℝ, s.center, a.midpoint]) :=
    ⟨⟨s.center, left_mem_affineSpan_pair ℝ s.center a.midpoint⟩⟩
  exact reflection_eq_self_iff a.left

lemma left_eq_right_of_left_eq_midpoint (a : Arc s) (h : a.left = a.midpoint) :
    a.left = a.right := by
  rw [left_eq_right_iff_mem_line, h]
  exact right_mem_affineSpan_pair ℝ s.center a.midpoint

/-- A point `p` is in the arc if it lies on the sphere and is weakly on the same side
of the chord (or tangent line) as the midpoint. -/
instance : Membership P (Arc s) where
  mem := fun (a : Arc s) (p : P) =>
    dist p s.center = s.radius ∧ (s.lineOrOrthRadius a.left a.right).WSameSide a.midpoint p

/-- Coercion from an arc to the set of points it contains. -/
instance : CoeTC (Arc s) (Set P) where
  coe := fun (a : Arc s) => { p : P | p ∈ a }

/-- The interior of an arc consists of points on the sphere that are strictly on the
same side of the chord as the midpoint. -/
def interior (a : Arc s) : Set P :=
  { p | p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).SSameSide a.midpoint p }

lemma midpoint_mem_arc (a : Arc s) : a.midpoint ∈ a := by
  constructor
  · exact a.midpoint_mem
  · rw [AffineSubspace.wSameSide_self_iff]
    exact ⟨a.left, left_mem_lineOrOrthRadius⟩

lemma left_mem_arc (a : Arc s) : a.left ∈ a := by
  constructor
  · exact a.left_mem
  · exact AffineSubspace.wSameSide_of_right_mem a.midpoint left_mem_lineOrOrthRadius

lemma right_mem_arc (a : Arc s) : a.right ∈ a := by
  constructor
  · exact a.right_mem
  · exact AffineSubspace.wSameSide_of_right_mem a.midpoint right_mem_lineOrOrthRadius

lemma Sphere.pointReflection_center_mem_sphere {m : P} (hm : m ∈ s) :
    AffineEquiv.pointReflection ℝ s.center m ∈ s := by
  rw [mem_sphere] at hm ⊢
  rw [AffineEquiv.pointReflection_apply, dist_vadd_left, ← dist_eq_norm_vsub', ← hm]

/-- The opposite arc between the same endpoints, obtained by using the antipodal point
of the midpoint (reflection through the center). -/
def opposite (a : Arc s) : Arc s where
  left := a.left
  midpoint := AffineEquiv.pointReflection ℝ s.center a.midpoint
  left_mem := a.left_mem
  midpoint_mem := Sphere.pointReflection_center_mem_sphere a.midpoint_mem

lemma line_center_opposite_midpoint_eq_line_center_midpoint (a : Arc s) :
    line[ℝ, s.center, a.opposite.midpoint] = line[ℝ, s.center, a.midpoint] := by
  simp only [opposite]
  apply AffineSubspace.ext_of_direction_eq
  · rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair,
      ← neg_vsub_eq_vsub_rev, ← neg_vsub_eq_vsub_rev]
    simp only [AffineEquiv.pointReflection_apply_eq_equivPointReflection_apply,
      Equiv.left_vsub_pointReflection, neg_vsub_eq_vsub_rev]
    rw [← neg_vsub_eq_vsub_rev, ← Set.neg_singleton, Submodule.span_neg]
  · exact ⟨s.center, left_mem_affineSpan_pair ℝ _ _, left_mem_affineSpan_pair ℝ _ _⟩

@[simp]
lemma opposite_left (a : Arc s) : a.opposite.left = a.left := rfl

@[simp]
lemma opposite_right (a : Arc s) : a.opposite.right = a.right := by
  simp only [right, opposite]
  exact eq_reflection_of_eq_subspace
    (line_center_opposite_midpoint_eq_line_center_midpoint a) a.left

@[simp]
lemma opposite_opposite (a : Arc s) : a.opposite.opposite = a := by
  simp only [opposite]
  congr 1
  exact AffineEquiv.pointReflection_involutive ℝ s.center a.midpoint

/-- The equivalence given by `opposite`, which is an involution on arcs. -/
def oppositeEquiv : Arc s ≃ Arc s where
  toFun := opposite
  invFun := opposite
  left_inv := opposite_opposite
  right_inv := opposite_opposite

/-! ### minor and major -/

/-- If `A` and `C` are not diameter endpoints, then the sum of their position vectors
relative to the center is nonzero. -/
lemma sum_vsub_center_ne_zero_of_not_isDiameter {A C : P} (hA : A ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) : (A -ᵥ s.center) + (C -ᵥ s.center) ≠ 0 := by
  intro h
  apply hNotDiam
  refine ⟨hA, ?_⟩
  rw [midpoint_eq_iff, AffineEquiv.pointReflection_apply, ← neg_vsub_eq_vsub_rev A s.center,
    add_eq_zero_iff_eq_neg.mp h, neg_neg, vsub_vadd]

/-- Helper to compute the midpoint of the minor arc. -/
def minorMidpoint (s : Sphere P) (A C : P) : P :=
  let v := (A -ᵥ s.center) + (C -ᵥ s.center)
  (s.radius / ‖v‖) • v +ᵥ s.center

/-- The `minorMidpoint` lies on the sphere. -/
lemma minorMidpoint_mem {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) : minorMidpoint s A C ∈ s := by
  have hv : ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sum_vsub_center_ne_zero_of_not_isDiameter hA hNotDiam)
  have hradius : 0 ≤ s.radius := hC ▸ dist_nonneg
  rw [mem_sphere, minorMidpoint, dist_vadd_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hradius (norm_nonneg _)), div_mul_cancel₀ _ hv]

/-- The minor arc from `A` to `C`. The midpoint is chosen on the shorter arc.
Requires `A` and `C` are not diametrically opposite (but `A = C` is allowed,
giving a single-point arc). -/
def minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) : Arc s where
  left := A
  midpoint := minorMidpoint s A C
  left_mem := hA
  midpoint_mem := minorMidpoint_mem hA  hC hNotDiam

@[simp]
lemma minor_left {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).left = A := rfl

lemma minor_midpoint {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).midpoint =
      (s.radius / ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖) •
        ((A -ᵥ s.center) + (C -ᵥ s.center)) +ᵥ s.center := rfl

/-- The right endpoint of the minor arc equals C. -/
@[simp]
lemma minor_right {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).right = C := by
  simp only [minor, right, minorMidpoint]
  set a := A -ᵥ s.center with ha_def
  set c := C -ᵥ s.center with hc_def
  set v := a + c with hv_def
  set m := (s.radius / ‖v‖) • v +ᵥ s.center with hm_def
  set L := line[ℝ, s.center, m] with hL_def
  have hv_ne : v ≠ 0 := sum_vsub_center_ne_zero_of_not_isDiameter hA hNotDiam
  have ha_norm : ‖a‖ = s.radius := by rw [ha_def, ← dist_eq_norm_vsub']; exact mem_sphere'.mp hA
  have hc_norm : ‖c‖ = s.radius := by rw [hc_def, ← dist_eq_norm_vsub']; exact mem_sphere'.mp hC
  have hr : s.radius ≠ 0 := fun h => hv_ne <| by simp [hv_def, norm_eq_zero.mp (ha_norm.trans h),
                                                       norm_eq_zero.mp (hc_norm.trans h)]
  have hdir : L.direction = ℝ ∙ v := by
    simp only [hL_def, direction_affineSpan, hm_def, vectorSpan_pair, vsub_vadd_eq_vsub_sub,
               vsub_self, zero_sub, ← neg_smul]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr <| neg_ne_zero.mpr <|
          div_ne_zero hr (norm_ne_zero_iff.mpr hv_ne)) v
  have hinner : ⟪a, v⟫ = ‖v‖^2 / 2 := by
      rw [hv_def, inner_add_right, real_inner_self_eq_norm_sq a, ha_norm]
      have h1 : ‖a + c‖^2 = ‖a‖^2 + 2 * ⟪a, c⟫ + ‖c‖^2 := norm_add_sq_real a c
      rw [ha_norm, hc_norm] at h1
      linarith
  have hperp' : a - (1/2 : ℝ) • v ∈ L.directionᗮ := by
    rw [hdir, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        inner_smul_right, real_inner_comm, hinner, real_inner_self_eq_norm_sq]
    ring
  have hmid_mem : (1/2 : ℝ) • v +ᵥ s.center ∈ L := by
    rw [hL_def]
    convert smul_vsub_vadd_mem_affineSpan_pair (1/2 * ‖v‖ / s.radius) s.center m using 2
    rw [hm_def, vadd_vsub, smul_smul]; field_simp
  change reflection L A = C
  rw [show A = (a - (1/2 : ℝ) • v) +ᵥ ((1/2 : ℝ) • v +ᵥ s.center) by
      rw [vadd_vadd, sub_add_cancel, ha_def, vsub_vadd]]
  rw [reflection_orthogonal_vadd hmid_mem hperp']
  calc (-(a - (1/2 : ℝ) • v)) +ᵥ ((1/2 : ℝ) • v +ᵥ s.center)
      = (v - a) +ᵥ s.center := by
        rw [neg_sub, vadd_vadd]
        congr 1
        have h1 : (1/2 : ℝ) • v - a + (1/2 : ℝ) • v = (1/2 : ℝ) • v + (1/2 : ℝ) • v - a := by abel
        have h2 : (1/2 : ℝ) • v + (1/2 : ℝ) • v = v := by rw [← add_smul]; norm_num
        rw [h1, h2]
    _ = c +ᵥ s.center := by rw [hv_def]; abel_nf
    _ = C := by rw [hc_def, vsub_vadd]

/-- The major arc from A to C. This is the opposite of the minor arc. -/
def major {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) : Arc s :=
  (minor hA hC hNotDiam).opposite

@[simp]
lemma major_left {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).left = A := rfl

lemma major_midpoint {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).midpoint =
      AffineEquiv.pointReflection ℝ s.center (minor hA hC hNotDiam).midpoint := rfl

/-- The right endpoint of the major arc equals C. -/
@[simp]
lemma major_right {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).right = C := by
  simp only [major, opposite_right, minor_right]

lemma major_eq_minor_opposite {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    major hA hC hNotDiam = (minor hA hC hNotDiam).opposite := rfl

/-- Minor and major arcs are opposite to each other. -/
@[simp]
lemma minor_opposite_eq_major {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).opposite = major hA hC hNotDiam := rfl

@[simp]
lemma major_opposite_eq_minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).opposite = minor hA hC hNotDiam := by
  simp only [major, opposite_opposite]

open Classical in
/-- The component of `B -ᵥ A` perpendicular to `s.lineOrOrthRadius A C`.
When `A ≠ C`, this is the rejection of `B -ᵥ A` from the chord direction `C -ᵥ A`.
When `A = C`, this is the projection of `B -ᵥ A` onto the radius direction
`A -ᵥ s.center`. -/
noncomputable def perpToLineOrOrthRadius (s : Sphere P) (A B C : P) : V :=
  if A = C then
    let a := A -ᵥ s.center
    (⟪B -ᵥ A, a⟫ / ⟪a, a⟫) • a
  else
    let d := C -ᵥ A
    (B -ᵥ A) - (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d

/-- The midpoint of the arc from `A` to `C` passing through `B`, constructed by
normalizing `perpToLineOrOrthRadius s A B C` to have norm `s.radius`. -/
noncomputable def throughMidpoint (s : Sphere P) (A B C : P) : P :=
  let w := perpToLineOrOrthRadius s A B C
  (s.radius / ‖w‖) • w +ᵥ s.center

/-- The perpendicular component `perpToLineOrOrthRadius s A B C` is nonzero when `B`
is distinct from both `A` and `C` and all three lie on the sphere `s`. -/
lemma perpToLineOrOrthRadius_ne_zero {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
   perpToLineOrOrthRadius s A B C ≠ 0 := by
  have hB_not_mem := not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC
  intro heq
  apply hB_not_mem
  simp only [perpToLineOrOrthRadius] at heq
  split_ifs at heq with hAC
  · subst hAC
    simp only [lineOrOrthRadius_of_eq, mem_orthRadius_iff_inner_left]
    by_cases ha : A -ᵥ s.center = 0
    · have : A = s.center := vsub_eq_zero_iff_eq.mp ha
      have : s.radius = 0 := by rw [← mem_sphere.mp hA, this, dist_self]
      have : B = s.center := by rw [← dist_eq_zero]; linarith [mem_sphere.mp hB]
      exact absurd (‹B = s.center› ▸ ‹A = s.center› ▸ rfl : B = A) hBA
    · rwa [smul_eq_zero, div_eq_zero_iff, inner_self_eq_zero, or_iff_left ha,
           or_iff_left ha] at heq
  · simp only [lineOrOrthRadius_of_ne hAC]
    have : B -ᵥ A = (⟪B -ᵥ A, C -ᵥ A⟫ / ⟪C -ᵥ A, C -ᵥ A⟫) • (C -ᵥ A) := by
      rwa [sub_eq_zero] at heq
    rw [show B = (⟪B -ᵥ A, C -ᵥ A⟫ / ⟪C -ᵥ A, C -ᵥ A⟫) • (C -ᵥ A) +ᵥ A from
      by rw [← this, vsub_vadd]]
    exact smul_vsub_vadd_mem_affineSpan_pair _ A C

open Classical in
/-- The `throughMidpoint` lies on the sphere. -/
lemma throughMidpoint_mem {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    throughMidpoint s A B C ∈ s := by
  have hw := perpToLineOrOrthRadius_ne_zero hA hB hC hBA hBC
  simp only [mem_sphere, throughMidpoint]
  rw [dist_vadd_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (Sphere.radius_nonneg_of_mem hA) (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)]

/-- The arc on `s` from `A` to `C` passing through `B`. -/
noncomputable def through {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : Arc s where
  left := A
  midpoint := throughMidpoint s A B C
  left_mem := hA
  midpoint_mem := throughMidpoint_mem hA hB hC hBA hBC

@[simp]
lemma through_left {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).left = A := rfl

lemma through_midpoint {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).midpoint = throughMidpoint s A B C := rfl

/-- The arc on `s` from `A` to `C` not passing through `B`. -/
noncomputable def avoiding {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : Arc s :=
  (through hA hB hC hBA hBC).opposite

@[simp]
lemma avoiding_left {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).left = A := rfl

lemma avoiding_midpoint {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).midpoint =
      AffineEquiv.pointReflection ℝ s.center (throughMidpoint s A B C) := rfl

@[simp]
lemma through_opposite {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).opposite = avoiding hA hB hC hBA hBC := rfl

@[simp]
lemma avoiding_opposite {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).opposite = through hA hB hC hBA hBC := by
  simp only [avoiding, opposite_opposite]

lemma avoiding_eq_through_opposite {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    avoiding hA hB hC hBA hBC = (through hA hB hC hBA hBC).opposite := rfl

end Arc

end

end Sphere

end EuclideanGeometry
