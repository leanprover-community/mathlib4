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

This file defines arcs on spheres (circles in 2D, great circle arcs in higher dimensions)
and proves basic properties.

-/

@[expose] public section

namespace EuclideanGeometry

namespace Sphere

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

noncomputable section

/-- An arc on a sphere, defined by a left endpoint and a midpoint on the sphere.
The right endpoint is computed as the reflection of the left endpoint across theline through the
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

lemma right_def (a : Arc s) : a.right = reflection (line[ℝ, s.center, a.midpoint]) a.left := rfl

lemma right_mem (a : Arc s) : a.right ∈ s := by
  rw [mem_sphere, right_def]
  have h_center_mem : s.center ∈ line[ℝ, s.center, a.midpoint] :=
    left_mem_affineSpan_pair ℝ s.center a.midpoint
  rw [dist_comm, dist_reflection_eq_of_mem _ h_center_mem, ← a.left_mem, dist_comm]

lemma left_eq_right_iff_mem_line (a : Arc s) :
    a.left = a.right ↔ a.left ∈ line[ℝ, s.center, a.midpoint] := by
  rw [right_def, eq_comm]
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

lemma pointReflection_center_mem_sphere {m : P} (hm : m ∈ s) :
    AffineEquiv.pointReflection ℝ s.center m ∈ s := by
  rw [mem_sphere] at hm ⊢
  rw [AffineEquiv.pointReflection_apply, dist_vadd_left, ← dist_eq_norm_vsub', ← hm]

/-- The opposite arc between the same endpoints, obtained by using the antipodal point
of the midpoint (reflection through the center). -/
def opposite (a : Arc s) : Arc s where
  left := a.left
  midpoint := AffineEquiv.pointReflection ℝ s.center a.midpoint
  left_mem := a.left_mem
  midpoint_mem := pointReflection_center_mem_sphere a.midpoint_mem

lemma line_center_opposite_midpoint_eq (a : Arc s) :
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
  exact eq_reflection_of_eq_subspace (line_center_opposite_midpoint_eq a) a.left

@[simp]
lemma opposite_opposite (a : Arc s) : a.opposite.opposite = a := by
  simp only [opposite]
  congr 1
  exact AffineEquiv.pointReflection_involutive ℝ s.center a.midpoint

/-- Bundled equivalence showing that `opposite` is an involution. -/
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

/-- The minor midpoint lies on the sphere. -/
lemma minorMidpoint_mem {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) : minorMidpoint s A C ∈ s := by
  have hv : ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sum_vsub_center_ne_zero_of_not_isDiameter hA hNotDiam)
  have hradius : 0 ≤ s.radius := hC ▸ dist_nonneg
  rw [mem_sphere, minorMidpoint, dist_vadd_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hradius (norm_nonneg _)), div_mul_cancel₀ _ hv]

/-- The minor arc from A to C. The midpoint is chosen on the shorter arc.
    Requires AC is not a diameter (but A = C is allowed, giving a single-point arc). -/
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
/-- The midpoint for an arc from A to C that contains B.
    Chooses minorMidpoint if B is on the same side, otherwise the antipodal point. -/
def throughMidpoint (s : Sphere P) (A B C : P) : P :=
  let m := minorMidpoint s A C
  if (s.lineOrOrthRadius A C).WSameSide m B then m
  else AffineEquiv.pointReflection ℝ s.center m

/-- The through midpoint lies on the sphere. -/
lemma throughMidpoint_mem (A B C : P) (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (throughMidpoint (s := s) (A := A) (B := B) (C := C)) ∈ s := by
  simp only [throughMidpoint]
  split_ifs
  · exact minorMidpoint_mem hA hC hNotDiam
  · exact pointReflection_center_mem_sphere (minorMidpoint_mem hA hC hNotDiam)

/-- Arc from A to C passing through B. -/
def through {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) : Arc s where
  left := A
  midpoint := throughMidpoint s A B C
  left_mem := hA
  midpoint_mem := throughMidpoint_mem A B C hA hC hNotDiam

/-- Arc from A to C not passing through B. -/
def avoiding {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) : Arc s :=
  (through (B := B) hA hC hNotDiam).opposite

@[simp]
lemma through_left {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (through (B := B) hA hC hNotDiam).left = A := rfl

lemma through_midpoint {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (through (B := B) hA hC hNotDiam).midpoint = throughMidpoint s A B C := rfl

/-- The right endpoint of `through A B C` equals C. -/
@[simp]
lemma through_right {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (through (B := B) hA hC hNotDiam).right = C := by
  classical
  have hminor : (minor hA hC hNotDiam).right = C := minor_right hA hC hNotDiam
  have hmajor : (major hA hC hNotDiam).right = C := major_right hA hC hNotDiam
  simp only [through, right, throughMidpoint, minor, major, opposite] at *
  split_ifs with h <;> assumption

@[simp]
lemma avoiding_left {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (avoiding (B := B) hA hC hNotDiam).left = A := by
  simp only [avoiding, opposite_left, through_left]

@[simp]
lemma avoiding_right {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (avoiding (B := B) hA hC hNotDiam).right = C := by
  simp only [avoiding, opposite_right, through_right]

lemma avoiding_eq_through_opposite {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    avoiding (B := B) hA hC hNotDiam =
      (through (B := B) hA hC hNotDiam).opposite := rfl

lemma through_eq_minor_of_wSameSide {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C)
    (h : (s.lineOrOrthRadius A C).WSameSide (minorMidpoint s A C) B) :
    through (B := B) hA hC hNotDiam = minor hA hC hNotDiam := by
  classical
  simp only [through, minor, throughMidpoint, if_pos h]

lemma through_eq_major_of_not_wSameSide {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C)
    (h : ¬(s.lineOrOrthRadius A C).WSameSide (minorMidpoint s A C) B) :
    through (B := B) hA hC hNotDiam = major hA hC hNotDiam := by
  classical
  simp only [through, major, opposite, minor, throughMidpoint, if_neg h]

lemma avoiding_eq_major_of_wSameSide {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C)
    (h : (s.lineOrOrthRadius A C).WSameSide (minorMidpoint s A C) B) :
    avoiding (B := B) hA hC hNotDiam = major hA hC hNotDiam := by
  simp only [avoiding, through_eq_minor_of_wSameSide hA hC hNotDiam h,
             minor_opposite_eq_major]

lemma avoiding_eq_minor_of_not_wSameSide {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C)
    (h : ¬(s.lineOrOrthRadius A C).WSameSide (minorMidpoint s A C) B) :
    avoiding (B := B) hA hC hNotDiam = minor hA hC hNotDiam := by
  simp only [avoiding, through_eq_major_of_not_wSameSide hA hC hNotDiam h,
             major_opposite_eq_minor]

@[simp]
lemma through_opposite {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (through (B := B) hA hC hNotDiam).opposite =
      avoiding (B := B) hA hC hNotDiam := rfl

@[simp]
lemma avoiding_opposite {A B C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    (avoiding (B := B) hA hC hNotDiam).opposite =
      through (B := B) hA hC hNotDiam := by
  simp only [avoiding, opposite_opposite]

end Arc

end

end Sphere

end EuclideanGeometry
