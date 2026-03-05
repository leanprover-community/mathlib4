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
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Arcs on Spheres

This file defines arcs on spheres and proves basic properties.

## Main definitions

* `EuclideanGeometry.Sphere.Arc`: An arc on a sphere, defined by a left endpoint and a mid.
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

/-- An arc on a sphere, defined by a left endpoint and a mid on the sphere.
The right endpoint is computed as the reflection of the left endpoint across the line through the
center and mid. -/
structure Arc (s : Sphere P) where
  /-- The left endpoint of the arc. -/
  left : P
  /-- A point on the arc (used to distinguish which arc between the endpoints). -/
  mid : P
  /-- Proof that left endpoint lies on the sphere. -/
  left_mem : left ∈ s
  /-- Proof that mid lies on the sphere. -/
  mid_mem : mid ∈ s

namespace Arc

variable {s : Sphere P}

/-- The right endpoint of an arc, computed as the reflection of the left endpoint
across the line through the center and mid. -/
def right (a : Arc s) : P :=
  reflection (line[ℝ, s.center, a.mid]) a.left

lemma right_eq_reflection (a : Arc s) :
  a.right = reflection (line[ℝ, s.center, a.mid]) a.left := rfl

lemma right_mem (a : Arc s) : a.right ∈ s := by
  rw [mem_sphere, right_eq_reflection]
  have h_center_mem : s.center ∈ line[ℝ, s.center, a.mid] :=
    left_mem_affineSpan_pair ℝ s.center a.mid
  rw [dist_comm, dist_reflection_eq_of_mem _ h_center_mem, ← a.left_mem, dist_comm]

lemma left_eq_right_iff_mem_line (a : Arc s) :
    a.left = a.right ↔ a.left ∈ line[ℝ, s.center, a.mid] := by
  rw [right_eq_reflection, eq_comm]
  haveI : Nonempty (line[ℝ, s.center, a.mid]) :=
    ⟨⟨s.center, left_mem_affineSpan_pair ℝ s.center a.mid⟩⟩
  exact reflection_eq_self_iff a.left

lemma left_eq_right_of_left_eq_mid (a : Arc s) (h : a.left = a.mid) :
    a.left = a.right := by
  rw [left_eq_right_iff_mem_line, h]
  exact right_mem_affineSpan_pair ℝ s.center a.mid

/-- A point `p` is in the arc if it lies on the sphere and is weakly on the same side
of the chord (or tangent line) as the mid. -/
instance : Membership P (Arc s) where
  mem := fun (a : Arc s) (p : P) =>
    dist p s.center = s.radius ∧ (s.lineOrOrthRadius a.left a.right).WSameSide a.mid p

/-- Coercion from an arc to the set of points it contains. -/
instance : CoeTC (Arc s) (Set P) where
  coe := fun (a : Arc s) => { p : P | p ∈ a }

/-- The interior of an arc consists of points on the sphere that are strictly on the
same side of the chord as the mid. -/
def interior (a : Arc s) : Set P :=
  { p | p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p }

lemma mid_mem_arc (a : Arc s) : a.mid ∈ a := by
  constructor
  · exact a.mid_mem
  · rw [AffineSubspace.wSameSide_self_iff]
    exact ⟨a.left, left_mem_lineOrOrthRadius⟩

lemma left_mem_arc (a : Arc s) : a.left ∈ a := by
  constructor
  · exact a.left_mem
  · exact AffineSubspace.wSameSide_of_right_mem a.mid left_mem_lineOrOrthRadius

lemma right_mem_arc (a : Arc s) : a.right ∈ a := by
  constructor
  · exact a.right_mem
  · exact AffineSubspace.wSameSide_of_right_mem a.mid right_mem_lineOrOrthRadius

lemma Sphere.pointReflection_center_mem_sphere {m : P} (hm : m ∈ s) :
    AffineEquiv.pointReflection ℝ s.center m ∈ s := by
  rw [mem_sphere] at hm ⊢
  rw [AffineEquiv.pointReflection_apply, dist_vadd_left, ← dist_eq_norm_vsub', ← hm]

/-- The opposite arc between the same endpoints, obtained by using the antipodal point
of the mid (reflection through the center). -/
def opposite (a : Arc s) : Arc s where
  left := a.left
  mid := AffineEquiv.pointReflection ℝ s.center a.mid
  left_mem := a.left_mem
  mid_mem := Sphere.pointReflection_center_mem_sphere a.mid_mem

lemma line_center_opposite_mid (a : Arc s) :
    line[ℝ, s.center, a.opposite.mid] = line[ℝ, s.center, a.mid] := by
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
    (line_center_opposite_mid a) a.left

@[simp]
lemma opposite_opposite (a : Arc s) : a.opposite.opposite = a := by
  simp only [opposite]
  congr 1
  exact AffineEquiv.pointReflection_involutive ℝ s.center a.mid

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

/-- Helper to compute the mid of the minor arc. -/
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

/-- The minor arc from `A` to `C`. The mid is chosen on the shorter arc.
Requires `A` and `C` are not diametrically opposite (but `A = C` is allowed,
giving a single-point arc). -/
def minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) : Arc s where
  left := A
  mid := minorMidpoint s A C
  left_mem := hA
  mid_mem := minorMidpoint_mem hA  hC hNotDiam

@[simp]
lemma minor_left {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).left = A := rfl

lemma minor_mid {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).mid =
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

lemma major_mid {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).mid =
      AffineEquiv.pointReflection ℝ s.center (minor hA hC hNotDiam).mid := rfl

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
/-- The mid of the arc from `A` to `C` passing through `B`. When `A ≠ C`, this is
constructed by normalizing the component of `B -ᵥ A` perpendicular to the chord `C -ᵥ A`.
When `A = C`, it normalizes the projection of `B -ᵥ A` onto the radius `A -ᵥ s.center`. -/
noncomputable def throughMidpoint (s : Sphere P) (A B C : P) : P :=
  let w : V := if A = C then
    (⟪B -ᵥ A, A -ᵥ s.center⟫ / ⟪A -ᵥ s.center, A -ᵥ s.center⟫) • (A -ᵥ s.center)
  else
    (B -ᵥ A) - (⟪B -ᵥ A, C -ᵥ A⟫ / ⟪C -ᵥ A, C -ᵥ A⟫) • (C -ᵥ A)
  (s.radius / ‖w‖) • w +ᵥ s.center

open Classical in
/-- The `throughMidpoint` lies on the sphere. -/
lemma throughMidpoint_mem {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    throughMidpoint s A B C ∈ s := by
  have hB_not_mem := not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC
  simp only [mem_sphere, throughMidpoint]
  split_ifs with hAC <;> (
    rw [dist_vadd_left, norm_smul,
      Real.norm_of_nonneg (div_nonneg (Sphere.radius_nonneg_of_mem hA) (norm_nonneg _))]
    refine div_mul_cancel₀ _ (norm_ne_zero_iff.mpr ?_)
    intro heq; apply hB_not_mem)
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

/-- The arc on `s` from `A` to `C` passing through `B`. -/
noncomputable def through {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : Arc s where
  left := A
  mid := throughMidpoint s A B C
  left_mem := hA
  mid_mem := throughMidpoint_mem hA hB hC hBA hBC

@[simp]
lemma through_left {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).left = A := rfl

lemma through_mid {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).mid = throughMidpoint s A B C := rfl

@[simp]
lemma through_right [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).right = C := by
  simp only [through, right, throughMidpoint]
  split_ifs with hAC
  · subst hAC
    set rv := A -ᵥ s.center
    set t := ⟪B -ᵥ A, rv⟫ / ⟪rv, rv⟫
    set m := (s.radius / ‖t • rv‖) • (t • rv) +ᵥ s.center
    have hrv_ne : rv ≠ 0 := by
      intro h; have hAc := vsub_eq_zero_iff_eq.mp h
      have : s.radius = 0 := by rw [← mem_sphere.mp hA, hAc, dist_self]
      exact hBA ((dist_eq_zero.mp (by linarith [mem_sphere.mp hB])).trans hAc.symm)
    have ht_ne : t ≠ 0 := by
      intro ht
      have := not_mem_lineOrOrthRadius_of_mem_sphere hA hB hA hBA hBA
      simp only [lineOrOrthRadius_of_eq] at this
      exact this (mem_orthRadius_iff_inner_left.mpr
        (by rwa [div_eq_zero_iff, inner_self_eq_zero, or_iff_left hrv_ne] at ht))
    have hcoeff : s.radius / ‖t • rv‖ * t ≠ 0 :=
      mul_ne_zero (div_ne_zero
        (by intro h; exact hrv_ne (norm_eq_zero.mp
          (by rw [← dist_eq_norm_vsub', mem_sphere'.mp hA, h])))
        (norm_ne_zero_iff.mpr (smul_ne_zero ht_ne hrv_ne))) ht_ne
    apply (reflection_eq_self_iff A).mpr
    convert smul_vsub_vadd_mem_affineSpan_pair (s.radius / ‖t • rv‖ * t)⁻¹ s.center m using 1
    rw [vadd_vsub, smul_smul, smul_smul, mul_assoc,
        inv_mul_cancel₀ hcoeff, one_smul, vsub_vadd]
  · set d := C -ᵥ A with hd_def
    set w := (B -ᵥ A) - (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d with hw_def
    set m := (s.radius / ‖w‖) • w +ᵥ s.center with hm_def
    set L := line[ℝ, s.center, m] with hL_def
    set M := _root_.midpoint ℝ A C with hM_def
    have hd_ne : d ≠ 0 := vsub_ne_zero.mpr (Ne.symm hAC)
    have hw_ne : w ≠ 0 := by
      intro heq; exact (not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC)
        (lineOrOrthRadius_of_ne hAC ▸ by
          rw [show B = (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d +ᵥ A from
            by rw [← sub_eq_zero.mp heq, vsub_vadd]]
          exact smul_vsub_vadd_mem_affineSpan_pair _ A C)
    have hr_ne : s.radius ≠ 0 := by
          intro h
          have hAc : A = s.center := by rw [← dist_eq_zero]; linarith [mem_sphere.mp hA]
          have hCc : C = s.center := by rw [← dist_eq_zero]; linarith [mem_sphere.mp hC]
          exact hAC (hAc.trans hCc.symm)
    have hdir : L.direction = ℝ ∙ w := by
      rw [hL_def, direction_affineSpan, hm_def, vectorSpan_pair,
          vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, ← neg_smul]
      exact Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr <| neg_ne_zero.mpr <|
         div_ne_zero hr_ne (norm_ne_zero_iff.mpr hw_ne)) w
    have hw_perp_d : ⟪w, d⟫ = 0 := by
      rw [hw_def]; exact real_inner_sub_smul_div_inner_self_eq_zero (B -ᵥ A) d
    have hAM_eq : A -ᵥ M = -(2⁻¹ : ℝ) • d := by
      rw [hM_def, hd_def, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev C A,
          ← invOf_eq_inv (2 : ℝ)]
      exact _root_.left_vsub_midpoint A C
    have hAM_perp : A -ᵥ M ∈ L.directionᗮ := by
      rw [hdir, Submodule.mem_orthogonal_singleton_iff_inner_right,
          hAM_eq, inner_smul_right, hw_perp_d, mul_zero]
    have hM_mem : M ∈ L := by
      have : s.center -ᵥ M ∈ L.direction := by
        rw [hdir]
        by_cases hcM : s.center -ᵥ M = 0
        · exact hcM ▸ Submodule.zero_mem _
        · exact Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hd_ne hw_ne
            (by rw [real_inner_comm]; rw [hM_def, hd_def]
                exact Sphere.inner_vsub_center_midpoint_vsub hA hC)
            (by rw [real_inner_comm]; exact hw_perp_d)
      rw [show M = (-(s.center -ᵥ M)) +ᵥ s.center from by rw [neg_vsub_eq_vsub_rev, vsub_vadd]]
      exact AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.neg_mem _ this) (left_mem_affineSpan_pair ℝ s.center m)
    change reflection L A = C
    rw [show A = (A -ᵥ M) +ᵥ M from (vsub_vadd A M).symm,
        reflection_orthogonal_vadd hM_mem hAM_perp, hAM_eq, neg_smul, neg_neg,
        show (2⁻¹ : ℝ) • d = C -ᵥ M from by
          rw [hM_def, hd_def, ← neg_vsub_eq_vsub_rev (_root_.midpoint ℝ A C) C,
              _root_.midpoint_vsub_right, ← smul_neg, neg_vsub_eq_vsub_rev, invOf_eq_inv],
        vsub_vadd]

/-- When `A = C`, the `throughMidpoint` coincides with the antipodal point of `A`. -/
lemma throughMidpoint_eq_antipodal_of_eq {A B : P}
    (hA : A ∈ s) (hB : B ∈ s) (hBA : B ≠ A) :
    throughMidpoint s A B A =
      AffineEquiv.pointReflection ℝ s.center A := by
  simp only [throughMidpoint, ite_true]
  set rv := A -ᵥ s.center with hrv_def
  set t := ⟪B -ᵥ A, rv⟫ / ⟪rv, rv⟫
  have hrv_ne : rv ≠ 0 := by
    intro h
    have hAc := vsub_eq_zero_iff_eq.mp h
    have : s.radius = 0 := by rw [← mem_sphere.mp hA, hAc, dist_self]
    exact hBA ((dist_eq_zero.mp (by linarith [mem_sphere.mp hB])).trans hAc.symm)
  have ht_neg : t < 0 := div_neg_of_neg_of_pos
    (Sphere.inner_vsub_vsub_center_lt_zero hA hB hBA) (real_inner_self_pos.mpr hrv_ne)
  have hrn : ‖rv‖ = s.radius := by rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hA
  have hr_ne : s.radius ≠ 0 := hrn ▸ norm_ne_zero_iff.mpr hrv_ne
  have ht_ne : t ≠ 0 := ne_of_lt ht_neg
  rw [AffineEquiv.pointReflection_apply, ← neg_vsub_eq_vsub_rev A s.center]
  congr 1
  rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_neg ht_neg, hrn,
      show s.radius / (-t * s.radius) * t = (-1 : ℝ) from by field_simp, neg_one_smul]

/-- The specified second point lies in the interior of the `through` arc. -/
lemma mem_interior_through [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    B ∈ (through hA hB hC hBA hBC).interior := by
  refine ⟨hB, ?_⟩
  change (s.lineOrOrthRadius A (through hA hB hC hBA hBC).right).SSameSide
    (throughMidpoint s A B C) B
  rw [through_right hA hB hC hBA hBC]
  have hB_not := not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC
  by_cases hAC : A = C
  · subst hAC
    rw [lineOrOrthRadius_of_eq rfl, throughMidpoint_eq_antipodal_of_eq hA hB hBA]
    set rv := A -ᵥ s.center with hrv_def
    have hrv_ne : rv ≠ 0 := by
      intro h
      have hAc := vsub_eq_zero_iff_eq.mp h
      have hr0 : s.radius = 0 := by rw [← mem_sphere.mp hA, hAc, dist_self]
      exact hBA (dist_eq_zero.mp (by linarith [mem_sphere.mp hB]) |>.trans hAc.symm)
    set t := ⟪B -ᵥ A, rv⟫ / ⟪rv, rv⟫ with ht_def
    have ht_neg : t < 0 := div_neg_of_neg_of_pos
      (Sphere.inner_vsub_vsub_center_lt_zero hA hB hBA) (real_inner_self_pos.mpr hrv_ne)
    have hcA : s.center -ᵥ A = -rv := by rw [hrv_def, neg_vsub_eq_vsub_rev]
    set foot := ((B -ᵥ A) - t • rv) +ᵥ A
    have hfoot_mem : foot ∈ s.orthRadius A := by
      rw [mem_orthRadius_iff_inner_left, vadd_vsub, inner_sub_left,
          inner_smul_left, conj_trivial, ht_def,
          div_mul_cancel₀ _ (inner_self_ne_zero.mpr hrv_ne), sub_self]
    have hB_foot : B -ᵥ foot = t • rv := by
      conv_lhs => rw [show B = ((B -ᵥ A) +ᵥ A) from (vsub_vadd B A).symm]
      rw [vadd_vsub_vadd_cancel_right, sub_sub_cancel]
    refine ⟨⟨A, self_mem_orthRadius s A, foot, hfoot_mem, ?_⟩, ?_, ?_⟩
    · rw [AffineEquiv.pointReflection_apply, vadd_vsub_assoc, hcA, hB_foot,
        show -rv + -rv = (-2 : ℝ) • rv from by rw [← neg_one_smul ℝ rv, ← add_smul]; norm_num]
      exact Or.inr (Or.inr ⟨-t, 2, neg_pos.mpr ht_neg, two_pos,
        by rw [smul_smul, smul_smul]; congr 1; ring⟩)
    · intro h
      rw [mem_orthRadius_iff_inner_left, AffineEquiv.pointReflection_apply,
          vadd_vsub_assoc, hcA, inner_add_left, inner_neg_left] at h
      linarith [real_inner_self_pos.mpr hrv_ne]
    · rwa [lineOrOrthRadius_of_eq rfl] at hB_not
  · unfold throughMidpoint
    rw [if_neg hAC, lineOrOrthRadius_of_ne hAC]
    set d := C -ᵥ A with hd_def
    set w : V := (B -ᵥ A) - (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d with hw_def
    set tm := (s.radius / ‖w‖) • w +ᵥ s.center with htm_def
    set M := midpoint ℝ A C with hM_def
    have hd_ne : d ≠ 0 := vsub_ne_zero.mpr (Ne.symm hAC)
    have hw_ne : w ≠ 0 := by
      intro heq; exact hB_not (lineOrOrthRadius_of_ne hAC ▸
        show B ∈ line[ℝ, A, C] from
          (show B = (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d +ᵥ A by rw [← sub_eq_zero.mp heq, vsub_vadd]) ▸
          smul_vsub_vadd_mem_affineSpan_pair _ A C)
    have hw_perp : ⟪w, d⟫ = 0 := real_inner_sub_smul_div_inner_self_eq_zero ..
    have hmw : w ∈ (Submodule.span ℝ {d})ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hw_perp
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hd_ne hw_ne
        (by rw [real_inner_comm]; exact Sphere.inner_vsub_center_midpoint_vsub hA hC)
        (by rw [real_inner_comm]; exact hw_perp))
    have hβ_bound : |β| * ‖w‖ < s.radius := by
      have := Sphere.dist_center_midpoint_lt_radius hA hC hAC
      rwa [dist_eq_norm_vsub V, ← hβ, norm_smul, Real.norm_eq_abs] at this
    have hw_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw_ne
    have hcoeff : 0 < s.radius / ‖w‖ + β := by
      have habs : |β| < s.radius / ‖w‖ := by rwa [lt_div_iff₀ hw_pos]
      linarith [neg_abs_le β]
    set proj_B := (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d +ᵥ A with hproj_def
    have hBproj : B -ᵥ proj_B = w := by
      conv_lhs => rw [show B = ((B -ᵥ A) +ᵥ A) from (vsub_vadd B A).symm]
      rw [hproj_def, vadd_vsub_vadd_cancel_right]
    have htm_M : tm -ᵥ M = (s.radius / ‖w‖ + β) • w := by
      rw [htm_def, vadd_vsub_assoc, hM_def, ← hβ, ← add_smul]
    have hM_mem : M ∈ line[ℝ, A, C] := hM_def ▸ AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hproj_mem : proj_B ∈ line[ℝ, A, C] :=
      smul_vsub_vadd_mem_affineSpan_pair _ A C
    refine ⟨⟨M, hM_mem, proj_B, hproj_mem, ?_⟩, ?_, ?_⟩
    · rw [htm_M, hBproj]
      exact SameRay.symm (SameRay.sameRay_pos_smul_right w hcoeff)
    · intro htm
      exact hw_ne <| by
        have h : (s.radius / ‖w‖ + β) • w ∈ Submodule.span ℝ {d} := by
          have := htm_M ▸ AffineSubspace.vsub_mem_direction htm hM_mem
          rwa [direction_affineSpan, Set.pair_comm, vectorSpan_pair] at this
        have h2 : w ∈ Submodule.span ℝ {d} :=
          (Submodule.smul_mem_iff _ hcoeff.ne').mp h
        have hmem := Submodule.mem_inf.mpr ⟨h2, hmw⟩
        rwa [disjoint_iff.mp (Submodule.orthogonal_disjoint _), Submodule.mem_bot] at hmem
    · exact lineOrOrthRadius_of_ne hAC ▸ hB_not

/-- The specified second point lies in the `through` arc. -/
lemma mem_through [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : B ∈ through hA hB hC hBA hBC :=
  ⟨hB, (mem_interior_through hA hB hC hBA hBC).2.wSameSide⟩

/-- The arc on `s` from `A` to `C` not passing through `B`. -/
noncomputable def avoiding {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : Arc s :=
  (through hA hB hC hBA hBC).opposite

@[simp]
lemma avoiding_left {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).left = A := rfl

lemma avoiding_mid {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).mid =
      AffineEquiv.pointReflection ℝ s.center (throughMidpoint s A B C) := rfl

@[simp]
lemma avoiding_right [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).right = C := by
  simp [avoiding, opposite_right, through_right]

/-- The specified second point does not lie in the `avoiding` arc when `A ≠ C`. -/
lemma not_mem_avoiding [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hAC : A ≠ C) :
    B ∉ avoiding hA hB hC hBA hBC := by
  intro ⟨_, hws⟩
  have h_ss := (mem_interior_through hA hB hC hBA hBC).2
  simp only [avoiding_left, avoiding_right hA hB hC hBA hBC,
             through_left, through_right hA hB hC hBA hBC] at hws h_ss
  rw [lineOrOrthRadius_of_ne hAC] at hws h_ss
  set d := C -ᵥ A; set w : V := (B -ᵥ A) - (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d
  set M := midpoint ℝ A C
  have hd_ne : d ≠ 0 := vsub_ne_zero.mpr hAC.symm
  have hw_ne : w ≠ 0 := by
    intro heq; exact (lineOrOrthRadius_of_ne hAC ▸
      not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC)
      ((show B = (⟪B -ᵥ A, d⟫ / ⟪d, d⟫) • d +ᵥ A by rw [← sub_eq_zero.mp heq, vsub_vadd]) ▸
       smul_vsub_vadd_mem_affineSpan_pair _ A C)
  have hw_perp : ⟪w, d⟫ = 0 := real_inner_sub_smul_div_inner_self_eq_zero ..
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hd_ne hw_ne
      (by rw [real_inner_comm]; exact Sphere.inner_vsub_center_midpoint_vsub hA hC)
      (by rw [real_inner_comm]; exact hw_perp))
  have hw_pos := norm_pos_iff.mpr hw_ne
  have hβ_bound : |β| * ‖w‖ < s.radius := by
    have h := Sphere.dist_center_midpoint_lt_radius hA hC hAC
    rwa [dist_eq_norm_vsub V, ← hβ, norm_smul, Real.norm_eq_abs] at h
  have hβ_div : |β| < s.radius / ‖w‖ := (lt_div_iff₀ hw_pos).mpr hβ_bound
  have hM_mem : M ∈ line[ℝ, A, C] := by
    rw [show M = (2⁻¹ : ℝ) • (C -ᵥ A) +ᵥ A from by
      simp [M, midpoint, AffineMap.lineMap_apply, invOf_eq_inv]]
    exact smul_vsub_vadd_mem_affineSpan_pair 2⁻¹ A C
  have htm_M : throughMidpoint s A B C -ᵥ M = (s.radius / ‖w‖ + β) • w := by
    simp only [throughMidpoint, if_neg hAC]; rw [vadd_vsub_assoc, ← hβ, ← add_smul]
  have htm'_M : AffineEquiv.pointReflection ℝ s.center (throughMidpoint s A B C) -ᵥ M =
      (β - s.radius / ‖w‖) • w := by
    have hvs : s.center -ᵥ (throughMidpoint s A B C) =
        (s.center -ᵥ M) - (throughMidpoint s A B C -ᵥ M) :=
      (vsub_sub_vsub_cancel_right s.center (throughMidpoint s A B C) M).symm
    rw [AffineEquiv.pointReflection_apply, vadd_vsub_assoc, hvs,
        ← hβ, htm_M, ← sub_smul, ← add_smul]; ring_nf
  have h_opp : (line[ℝ, A, C]).SOppSide (throughMidpoint s A B C)
      (AffineEquiv.pointReflection ℝ s.center (throughMidpoint s A B C)) := by
    refine ⟨⟨M, hM_mem, M, hM_mem, ?_⟩, h_ss.2.1, ?_⟩
    · rw [htm_M, ← neg_vsub_eq_vsub_rev, htm'_M, ← neg_smul, neg_sub]
      exact .inr (.inr ⟨s.radius / ‖w‖ - β, s.radius / ‖w‖ + β,
        by linarith [le_abs_self β], by linarith [neg_abs_le β],
        by rw [smul_smul, smul_smul]; congr 1; ring⟩)
    · intro h
      have h1 : (β - s.radius / ‖w‖) • w ∈ (line[ℝ, A, C]).direction :=
        htm'_M ▸ AffineSubspace.vsub_mem_direction h hM_mem
      rw [direction_affineSpan, Set.pair_comm, vectorSpan_pair] at h1
      have h2 := (Submodule.smul_mem_iff _
        (show (β - s.radius / ‖w‖) ≠ 0 by linarith [le_abs_self β])).mp h1
      have h3 := Submodule.mem_inf.mpr
        ⟨h2, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hw_perp⟩
      rw [(Submodule.orthogonal_disjoint (𝕜 := ℝ) (E := V) _).eq_bot, Submodule.mem_bot] at h3
      exact hw_ne h3
  exact (h_opp.symm.trans_sSameSide h_ss).not_wSameSide hws

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
