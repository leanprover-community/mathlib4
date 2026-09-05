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
# Arcs on spheres

An `EuclideanGeometry.Sphere.Arc s` is one of the two arcs cut out of a sphere `s` by a pair of
points on it. It is represented by a left endpoint together with an anchor `mid` on the sphere:
the right endpoint is *derived* as the reflection of `left` in the line through `s.center` and
`mid`, and membership is decided by the side of the chord on which `mid` lies. This file sets up
that representation together with its membership and interior predicates, the involution sending
an arc to the complementary arc on the same endpoints, and the four constructors `minor`,
`major`, `through` and `avoiding`.

## Main definitions

* `EuclideanGeometry.Sphere.Arc`: an arc on a sphere, given by a left endpoint and an anchor
  `mid`, both on the sphere.
* `EuclideanGeometry.Sphere.Arc.right`: the derived right endpoint.
* `EuclideanGeometry.Sphere.Arc.interior`: the arc with its two endpoints removed.
* `EuclideanGeometry.Sphere.Arc.opposite`: the complementary arc on the same endpoints.
* `EuclideanGeometry.Sphere.Arc.minor` / `major`: the two arcs determined by a non-diametral
  pair of points on the sphere.
* `EuclideanGeometry.Sphere.Arc.through` / `avoiding`: the arc from `A` to `C` that does,
  respectively does not, contain `B`.

## Main results

* `EuclideanGeometry.Sphere.Arc.mem_iff_wSameSide`: for an arc with distinct endpoints,
  membership is weak same-sidedness with `mid`, replacing the disjunctive definition by a single
  convex-geometry condition.
* `EuclideanGeometry.Sphere.Arc.coe_eq_interior_union_endpoints`: an arc, as a point set, is its
  interior together with its endpoints, including when those endpoints coincide.
* `EuclideanGeometry.Sphere.Arc.interior_eq_empty_of_mid_eq_left` and
  `EuclideanGeometry.Sphere.Arc.coe_eq_singleton_iff_mid_eq_left`: the single-point representation
  has empty interior and is characterized by its singleton point set.
* `EuclideanGeometry.Sphere.Arc.minor_right`, `major_right`, `through_right`, `avoiding_right`:
  each constructor has `C` as its right endpoint, which is what makes the derived-endpoint
  representation usable.
* `EuclideanGeometry.Sphere.Arc.sOppSide_mid_opposite_mid` and
  `EuclideanGeometry.Sphere.Arc.sSameSide_opposite_mid_iff`: in two dimensions the anchors of an
  arc and of its opposite lie strictly on opposite sides of the chord, and exactly one of them
  lies on the same side as `s.center`.
* `EuclideanGeometry.Sphere.Arc.eq_or_eq_opposite_of_left_eq_of_right_eq` and
  `EuclideanGeometry.Sphere.Arc.eq_of_left_eq_of_right_eq_of_sSameSide_mid`: in two dimensions
  the ordered endpoints leave exactly two arcs, and adding a choice of side pins down the `Arc`
  object.
* `EuclideanGeometry.Sphere.Arc.eq_minor_or_eq_major_of_ne`: in two dimensions, `minor` and
  `major` exhaust the `Arc` objects with the same distinct non-diametral ordered endpoints.
* `EuclideanGeometry.Sphere.Arc.minor_ne_major`: under the non-diameter hypothesis, the two
  branches are distinct `Arc` objects.
* `EuclideanGeometry.Sphere.Arc.mem_through` and
  `EuclideanGeometry.Sphere.Arc.notMem_avoiding`: the defining properties of the last two
  constructors.
* `EuclideanGeometry.Sphere.Arc.through_self_eq_major_self`: when the endpoints coincide,
  `through A B A` is the full circle `major A A`, independently of which `B` selects it.

## Implementation notes

An arc is stored as an endpoint together with an anchor `mid` on the sphere, with `right` derived
as a reflection, rather than as two endpoints and a choice of side. This makes `right_mem`
automatic, and when the endpoints coincide it turns the difference between a single-point arc and
a full circle into a property of `mid` rather than an extra field.

Membership is stated disjunctively — being an endpoint, or lying strictly on the same side of
`s.lineOrOrthRadius a.left a.right` as `mid` — and the separating subspace is `lineOrOrthRadius`
rather than the chord. Both choices are forced by the case `left = right`, where the chord
degenerates to a point and weak same-sidedness would admit every point of the sphere. For arcs
with distinct endpoints the simpler form is `mem_iff_wSameSide`.

The structure fields `left_mem` and `mid_mem` assert membership in the sphere; membership in the
arc is `left_mem_arc`, `right_mem_arc` and `mid_mem_arc`. `Arc.interior` is the arc minus its
endpoints, and is unrelated to the topological interior of the coerced set.
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
center and mid.

Note that the coercion to `Set P` is not injective: reversing the named endpoints of a `minor`
arc with distinct endpoints preserves its point set but changes `left`. The correct object-level
uniqueness statement is `eq_of_left_eq_of_right_eq_of_sSameSide_mid`. -/
@[ext]
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
  rw [mem_sphere, right_eq_reflection, dist_comm,
      dist_reflection_eq_of_mem _ (left_mem_affineSpan_pair ℝ s.center a.mid), ← a.left_mem,
      dist_comm]

lemma left_eq_right_iff_mem_line (a : Arc s) :
    a.left = a.right ↔ a.left ∈ line[ℝ, s.center, a.mid] := by
  rw [right_eq_reflection, eq_comm]
  have : Nonempty (line[ℝ, s.center, a.mid]) :=
    ⟨⟨s.center, left_mem_affineSpan_pair ℝ s.center a.mid⟩⟩
  exact reflection_eq_self_iff a.left

lemma left_eq_right_of_left_eq_mid (a : Arc s) (h : a.left = a.mid) :
    a.left = a.right := by
  rw [left_eq_right_iff_mem_line, h]
  exact right_mem_affineSpan_pair ℝ s.center a.mid

/-- An arc whose mid equals its right endpoint has equal left and right endpoints. -/
lemma left_eq_right_of_mid_eq_right (a : Arc s) (h : a.mid = a.right) :
    a.left = a.right := by
  apply left_eq_right_of_left_eq_mid
  have : Nonempty (line[ℝ, s.center, a.mid]) :=
    ⟨⟨a.mid, right_mem_affineSpan_pair ℝ s.center a.mid⟩⟩
  apply (reflection (line[ℝ, s.center, a.mid])).injective
  rw [← a.right_eq_reflection, (reflection_eq_self_iff a.mid).mpr
        (right_mem_affineSpan_pair ℝ s.center a.mid)]
  exact h.symm

/-- An arc whose endpoints coincide, but whose mid is not that endpoint, has the reflection of
the endpoint through the center as its mid. -/
theorem mid_eq_pointReflection_center_left_of_left_eq_right_of_mid_ne_left (a : Arc s)
    (hlr : a.left = a.right) (hml : a.mid ≠ a.left) :
    a.mid = AffineEquiv.pointReflection ℝ s.center a.left := by
  have hleft_line : a.left ∈ line[ℝ, s.center, a.mid] :=
    (left_eq_right_iff_mem_line a).mp hlr
  have hcol : Collinear ℝ ({a.mid, s.center, a.left} : Set P) := by
    have h' : Collinear ℝ ({a.left, s.center, a.mid} : Set P) :=
      collinear_insert_of_mem_affineSpan_pair hleft_line
    simpa [Set.insert_comm, Set.pair_comm] using h'
  have hdiam : s.IsDiameter a.mid a.left :=
    isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨a.mid_mem, a.left_mem,
      wbtw_of_collinear_of_dist_center_le_radius hcol a.mid_mem
        (by simpa using radius_nonneg_of_mem a.mid_mem) a.left_mem hml⟩
  simpa [AffineEquiv.coe_pointReflection] using hdiam.symm.pointReflection_center_left.symm

/-- A point `p` is in the arc if it lies on the sphere and is an endpoint or lies strictly on the
same side of `lineOrOrthRadius` as the mid. Thus an arc is its interior together with its
endpoints, including when those endpoints coincide. -/
instance : Membership P (Arc s) where
  mem := fun (a : Arc s) (p : P) =>
    dist p s.center = s.radius ∧
      (p = a.left ∨ p = a.right ∨ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p)

/-- A point lies in an arc iff it lies on the sphere and is an endpoint or lies strictly on the
same side of `lineOrOrthRadius` as the mid. Named form of the defining membership. -/
lemma mem_iff {a : Arc s} {p : P} :
    p ∈ a ↔ p ∈ s ∧
      (p = a.left ∨ p = a.right ∨ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p) :=
  ⟨fun h => ⟨mem_sphere.mpr h.1, h.2⟩, fun h => ⟨mem_sphere.mp h.1, h.2⟩⟩

lemma left_mem_arc (a : Arc s) : a.left ∈ a := mem_iff.mpr ⟨a.left_mem, Or.inl rfl⟩

lemma right_mem_arc (a : Arc s) : a.right ∈ a := mem_iff.mpr ⟨a.right_mem, Or.inr (Or.inl rfl)⟩

lemma mid_mem_arc (a : Arc s) : a.mid ∈ a := by
  refine mem_iff.mpr ⟨a.mid_mem, ?_⟩
  by_cases hL : a.mid ∈ s.lineOrOrthRadius a.left a.right
  · rcases (mem_lineOrOrthRadius_iff_of_mem_sphere a.left_mem a.mid_mem a.right_mem).mp hL
    with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (AffineSubspace.sSameSide_self_iff.mpr
      ⟨⟨a.left, left_mem_lineOrOrthRadius⟩, hL⟩))

/-- For an arc with distinct endpoints, the mid does not lie on `lineOrOrthRadius`. -/
lemma mid_notMem_lineOrOrthRadius (a : Arc s) (hne : a.left ≠ a.right) :
    a.mid ∉ s.lineOrOrthRadius a.left a.right :=
  notMem_lineOrOrthRadius_of_mem_sphere a.left_mem a.mid_mem a.right_mem
    (fun h => hne (left_eq_right_of_left_eq_mid a h.symm))
    (fun h => hne (left_eq_right_of_mid_eq_right a h))

/-- For an arc with distinct endpoints, the anchor does not lie on the chord. -/
lemma mid_notMem_line (a : Arc s) (hne : a.left ≠ a.right) :
    a.mid ∉ line[ℝ, a.left, a.right] := by
  have h := a.mid_notMem_lineOrOrthRadius hne
  rwa [lineOrOrthRadius_of_ne hne] at h

/-- For an arc with distinct endpoints, the endpoint-or-strict-side definition of membership is
equivalent to weak same-sidedness with the mid. -/
lemma mem_iff_wSameSide {a : Arc s} {p : P} (hne : a.left ≠ a.right) :
    p ∈ a ↔ p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).WSameSide a.mid p := by
  rw [mem_iff, and_congr_right_iff]
  intro hp
  constructor
  · rintro (rfl | rfl | hss)
    · exact AffineSubspace.wSameSide_of_right_mem _ left_mem_lineOrOrthRadius
    · exact AffineSubspace.wSameSide_of_right_mem _ right_mem_lineOrOrthRadius
    · exact hss.wSameSide
  · intro hws
    by_cases hpL : p ∈ s.lineOrOrthRadius a.left a.right
    · rcases (mem_lineOrOrthRadius_iff_of_mem_sphere a.left_mem hp a.right_mem).mp hpL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hws, a.mid_notMem_lineOrOrthRadius hne, hpL⟩)

/-- For an arc with distinct endpoints, a point on the sphere that does not lie in the arc is not
weakly on the same side of the chord as the mid. -/
lemma not_wSameSide_mid_of_mem_sphere_of_notMem {a : Arc s} {p : P}
    (hp : p ∈ s) (hpa : p ∉ a) (hne : a.left ≠ a.right) :
    ¬ (s.lineOrOrthRadius a.left a.right).WSameSide a.mid p :=
  fun hws => hpa ((mem_iff_wSameSide hne).mpr ⟨hp, hws⟩)

/-- Coercion from an arc to the set of points it contains. -/
instance : CoeTC (Arc s) (Set P) where
  coe := fun (a : Arc s) => { p : P | p ∈ a }

/-- The interior of an arc consists of points on the sphere that are strictly on the
same side of the chord as the mid. -/
def interior (a : Arc s) : Set P :=
  { p | p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p }

/-- A point lies in an arc's interior if and only if it lies on the sphere and is strictly on the
same side of the chord as the arc's mid. -/
lemma mem_interior_iff {a : Arc s} {p : P} :
    p ∈ a.interior ↔ p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p :=
  Iff.rfl

/-- An interior point of an arc lies on the sphere. -/
lemma mem_sphere_of_mem_interior {a : Arc s} {p : P} (h : p ∈ a.interior) : p ∈ s :=
  (mem_interior_iff.mp h).1

/-- An interior point lies strictly on the same side of the chord as the arc's mid. -/
lemma sSameSide_of_mem_interior {a : Arc s} {p : P} (h : p ∈ a.interior) :
    (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p :=
  (mem_interior_iff.mp h).2

/-- A sphere point in an arc that is distinct from both endpoints lies in the arc's interior. -/
theorem mem_interior_of_mem_of_ne_left_of_ne_right
    {a : Arc s} {p : P} (hp : p ∈ a) (hpl : p ≠ a.left) (hpr : p ≠ a.right) :
    p ∈ a.interior := by
  rcases (mem_iff.mp hp) with ⟨hps, hleft | hright | hss⟩
  · exact absurd hleft hpl
  · exact absurd hright hpr
  · exact mem_interior_iff.mpr ⟨hps, hss⟩

/-- An interior point of an arc lies in the arc. -/
theorem mem_of_mem_interior {a : Arc s} {p : P} (hp : p ∈ a.interior) : p ∈ a :=
  mem_iff.mpr ⟨mem_sphere_of_mem_interior hp, Or.inr (Or.inr (sSameSide_of_mem_interior hp))⟩

/-- An arc's interior is contained in the arc. -/
theorem interior_subset (a : Arc s) : a.interior ⊆ (a : Set P) := fun _ => mem_of_mem_interior

/-- An interior point of an arc does not lie on its chord or orthogonal radius. -/
theorem notMem_lineOrOrthRadius_of_mem_interior {a : Arc s} {p : P}
    (hp : p ∈ a.interior) :
    p ∉ s.lineOrOrthRadius a.left a.right := (sSameSide_of_mem_interior hp).right_notMem

/-- An interior point of an arc is not the left endpoint. -/
theorem ne_left_of_mem_interior {a : Arc s} {p : P} (hp : p ∈ a.interior) :
    p ≠ a.left :=
  fun h => notMem_lineOrOrthRadius_of_mem_interior hp (h ▸ left_mem_lineOrOrthRadius)

/-- An interior point of an arc is not the right endpoint. -/
theorem ne_right_of_mem_interior {a : Arc s} {p : P} (hp : p ∈ a.interior) :
    p ≠ a.right :=
  fun h => notMem_lineOrOrthRadius_of_mem_interior hp (h ▸ right_mem_lineOrOrthRadius)

/-- A point lies in an arc's interior if and only if it lies in the arc and is distinct from
both endpoints. -/
theorem mem_interior_iff_mem_and_ne {a : Arc s} {p : P} :
    p ∈ a.interior ↔ p ∈ a ∧ p ≠ a.left ∧ p ≠ a.right :=
  ⟨fun hp => ⟨mem_of_mem_interior hp, ne_left_of_mem_interior hp, ne_right_of_mem_interior hp⟩,
    fun ⟨hp, hpl, hpr⟩ => mem_interior_of_mem_of_ne_left_of_ne_right hp hpl hpr⟩

/-- An arc, viewed as a set, is exactly its interior together with its two endpoints. -/
theorem coe_eq_interior_union_endpoints (a : Arc s) :
    (a : Set P) = a.interior ∪ {a.left, a.right} := by
  ext p
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun hp => ?_, ?_⟩
  · rcases eq_or_ne p a.left with rfl | hpl
    · exact Or.inr (Or.inl rfl)
    rcases eq_or_ne p a.right with rfl | hpr
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (mem_interior_of_mem_of_ne_left_of_ne_right hp hpl hpr)
  · rintro (h | rfl | rfl)
    exacts [mem_of_mem_interior h, a.left_mem_arc, a.right_mem_arc]

/-- An arc whose anchor is its left endpoint has empty interior. -/
lemma interior_eq_empty_of_mid_eq_left (a : Arc s) (h : a.mid = a.left) :
    a.interior = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hp =>
    (sSameSide_of_mem_interior hp).left_notMem
      (by rw [h]; exact left_mem_lineOrOrthRadius)

/-- An arc reduces to its left endpoint exactly when its anchor is that endpoint. -/
theorem coe_eq_singleton_iff_mid_eq_left (a : Arc s) :
    (a : Set P) = {a.left} ↔ a.mid = a.left := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hm : a.mid ∈ ({a.left} : Set P) := by
      rw [← h]
      exact mid_mem_arc a
    exact Set.mem_singleton_iff.mp hm
  · rw [coe_eq_interior_union_endpoints, interior_eq_empty_of_mid_eq_left a h,
      Set.empty_union, ← left_eq_right_of_left_eq_mid a h.symm, Set.pair_eq_singleton]

/-- The mid point of an arc with distinct endpoints lies in its interior. -/
theorem mid_mem_interior (a : Arc s) (hne : a.left ≠ a.right) :
    a.mid ∈ a.interior :=
  mem_interior_iff.mpr ⟨a.mid_mem, AffineSubspace.sSameSide_self_iff.mpr
    ⟨⟨a.left, left_mem_lineOrOrthRadius⟩, mid_notMem_lineOrOrthRadius a hne⟩⟩

/-- The opposite arc between the same endpoints, obtained by using the antipodal point
of the mid (reflection through the center). -/
def opposite (a : Arc s) : Arc s where
  left := a.left
  mid := AffineEquiv.pointReflection ℝ s.center a.mid
  left_mem := a.left_mem
  mid_mem := Sphere.pointReflection_center_mem a.mid_mem

/-- The line through `s.center` and the opposite arc's mid coincides with the
line through `s.center` and `a.mid`. -/
lemma line_center_opposite_mid (a : Arc s) :
    line[ℝ, s.center, a.opposite.mid] = line[ℝ, s.center, a.mid] := by
  refine AffineSubspace.ext_of_direction_eq ?_
    ⟨s.center, left_mem_affineSpan_pair ℝ _ _, left_mem_affineSpan_pair ℝ _ _⟩
  simp only [opposite, direction_affineSpan, vectorSpan_pair, AffineEquiv.coe_pointReflection,
    Equiv.left_vsub_pointReflection]
  rw [← neg_vsub_eq_vsub_rev a.mid s.center, ← Set.neg_singleton, Submodule.span_neg]

@[simp]
lemma opposite_left (a : Arc s) : a.opposite.left = a.left := rfl

@[simp]
lemma opposite_right (a : Arc s) : a.opposite.right = a.right := by
  simp only [right, opposite]
  exact eq_reflection_of_eq_subspace
    (line_center_opposite_mid a) a.left

/-- For an arc with distinct endpoints, the opposite arc's anchor does not lie on the chord. -/
lemma opposite_mid_notMem_line (a : Arc s) (hne : a.left ≠ a.right) :
    a.opposite.mid ∉ line[ℝ, a.left, a.right] := by
  simpa only [opposite_left, opposite_right] using
    a.opposite.mid_notMem_line (by simpa using hne)

lemma opposite_mid_vsub_center (a : Arc s) :
    a.opposite.mid -ᵥ s.center = -(a.mid -ᵥ s.center) := by
  change AffineEquiv.pointReflection ℝ s.center a.mid -ᵥ s.center = _
  rw [AffineEquiv.pointReflection_apply, vadd_vsub, neg_vsub_eq_vsub_rev]

@[simp]
lemma midpoint_mid_opposite_mid (a : Arc s) :
    midpoint ℝ a.mid a.opposite.mid = s.center := by
  rw [midpoint_eq_iff]
  rfl

@[simp]
lemma opposite_opposite (a : Arc s) : a.opposite.opposite = a := by
  simp only [opposite]
  congr 1
  exact AffineEquiv.pointReflection_involutive ℝ s.center a.mid

/-- The reflection axis of an arc is contained in the perpendicular bisector of its endpoints. -/
lemma line_center_mid_le_perpBisector (a : Arc s) :
    line[ℝ, s.center, a.mid] ≤ AffineSubspace.perpBisector a.left a.right := by
  intro p hp
  rw [AffineSubspace.mem_perpBisector_iff_dist_eq, a.right_eq_reflection, eq_comm]
  exact dist_reflection_eq_of_mem _ hp _

/-- For any arc, the vector from `s.center` to `a.mid` is orthogonal to the
chord `a.right -ᵥ a.left`. -/
lemma inner_mid_vsub_center_right_vsub_left (a : Arc s) :
    ⟪a.mid -ᵥ s.center, a.right -ᵥ a.left⟫ = 0 := by
  have hdist : dist a.right a.mid = dist a.left a.mid := by
      rw [a.right_eq_reflection, dist_comm, dist_reflection_eq_of_mem, dist_comm]
      exact right_mem_affineSpan_pair ℝ s.center a.mid
  have hL_norm : ‖a.left -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.left_mem
  have hR_norm : ‖a.right -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.right_mem
  have hdist_sq : ‖a.right -ᵥ a.mid‖ ^ 2 = ‖a.left -ᵥ a.mid‖ ^ 2 := by
    rw [← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, hdist]
  rw [show a.right -ᵥ a.mid = (a.right -ᵥ s.center) - (a.mid -ᵥ s.center) from
        (vsub_sub_vsub_cancel_right _ _ _).symm,
      show a.left -ᵥ a.mid = (a.left -ᵥ s.center) - (a.mid -ᵥ s.center) from
        (vsub_sub_vsub_cancel_right _ _ _).symm,
      @norm_sub_sq_real, @norm_sub_sq_real, hR_norm, hL_norm] at hdist_sq
  have h_inner_eq :
      ⟪a.right -ᵥ s.center, a.mid -ᵥ s.center⟫ =
      ⟪a.left -ᵥ s.center, a.mid -ᵥ s.center⟫ := by linarith
  rw [real_inner_comm,
      show (a.right -ᵥ a.left : V) = (a.right -ᵥ s.center) - (a.left -ᵥ s.center) from
        (vsub_sub_vsub_cancel_right _ _ _).symm,
      inner_sub_left, h_inner_eq, sub_self]

/-- In two dimensions, the midpoint of the chord lies strictly between an arc's anchor and the
anchor of the opposite arc. -/
theorem sbtw_mid_midpoint_opposite_mid [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right) :
    Sbtw ℝ a.mid (midpoint ℝ a.left a.right) a.opposite.mid := by
  set m : V := a.mid -ᵥ s.center with hm_def
  set d : V := a.right -ᵥ a.left with hd_def
  set F : P := midpoint ℝ a.left a.right with hF_def
  have hd_ne : d ≠ 0 := vsub_ne_zero.mpr hne.symm
  have hm_perp_d : ⟪m, d⟫ = 0 := a.inner_mid_vsub_center_right_vsub_left
  have hm_norm : ‖m‖ = s.radius := by
    rw [hm_def]; exact norm_vsub_center_eq_radius a.mid_mem
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne a.left_mem a.right_mem hne
  have hr_pos : 0 < s.radius :=
    lt_of_le_of_ne (Sphere.radius_nonneg_of_mem a.left_mem) (Ne.symm hr_ne)
  have hm_ne : m ≠ 0 := by rw [← norm_ne_zero_iff, hm_norm]; exact hr_ne
  have hF_mem : F ∈ line[ℝ, a.left, a.right] := by
    rw [hF_def]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hFc_perp : ⟪F -ᵥ s.center, d⟫ = 0 := by
    rw [hF_def, hd_def, ← neg_vsub_eq_vsub_rev, inner_neg_left,
        Sphere.inner_vsub_center_midpoint_vsub a.left_mem a.right_mem, neg_zero]
  have hd_inner_Fc : ⟪d, F -ᵥ s.center⟫ = 0 := by rw [real_inner_comm]; exact hFc_perp
  have hd_inner_m : ⟪d, m⟫ = 0 := by rw [real_inner_comm]; exact hm_perp_d
  have hFc_in_span : (F -ᵥ s.center : V) ∈ Submodule.span ℝ ({m} : Set V) :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      hd_ne hm_ne hd_inner_Fc hd_inner_m
  obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp hFc_in_span
  have hδ_abs : |δ| < 1 := by
    have h_dist : dist s.center F < s.radius :=
      Sphere.dist_center_midpoint_lt_radius a.left_mem a.right_mem hne
    have h_norm : ‖s.center -ᵥ F‖ = |δ| * s.radius := by
      rw [show (s.center -ᵥ F : V) = -(F -ᵥ s.center) from (neg_vsub_eq_vsub_rev _ _).symm,
          norm_neg, ← hδ, norm_smul, Real.norm_eq_abs, hm_norm]
    rw [dist_eq_norm_vsub V, h_norm] at h_dist
    exact lt_of_mul_lt_mul_right (by rwa [one_mul]) hr_pos.le
  have ham_sub : a.mid -ᵥ F = (1 - δ) • m := by
    have h1 : (a.mid -ᵥ F : V) = (a.mid -ᵥ s.center) - (F -ᵥ s.center) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [h1, ← hm_def, ← hδ]; module
  have hopp_sub : (a.opposite.mid -ᵥ a.mid : V) = (-2 : ℝ) • m := by
    rw [show (a.opposite.mid -ᵥ a.mid : V) =
        (a.opposite.mid -ᵥ s.center) - (a.mid -ᵥ s.center) from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
      opposite_mid_vsub_center, ← hm_def]
    module
  have hF_sub : (F -ᵥ a.mid : V) =
      ((1 - δ) / 2) • (a.opposite.mid -ᵥ a.mid) := by
    rw [show (F -ᵥ a.mid : V) = -(a.mid -ᵥ F) from
          (neg_vsub_eq_vsub_rev _ _).symm,
      ham_sub, hopp_sub]
    module
  have h_mid_not_mem := a.mid_notMem_line hne
  have h_omid_not_mem := a.opposite_mid_notMem_line hne
  obtain ⟨hδ_lo, hδ_hi⟩ := abs_lt.mp hδ_abs
  refine ⟨⟨(1 - δ) / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_, ?_⟩
  · rw [AffineMap.lineMap_apply, ← hF_sub, vsub_vadd]
  · exact fun h => h_mid_not_mem (h ▸ hF_mem)
  · exact fun h => h_omid_not_mem (h ▸ hF_mem)

/-- In two dimensions, an arc's mid and the opposite arc's mid lie on strictly
opposite sides of the chord. -/
theorem sOppSide_mid_opposite_mid [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right) :
    (s.lineOrOrthRadius a.left a.right).SOppSide a.mid a.opposite.mid := by
  rw [lineOrOrthRadius_of_ne hne]
  have hF_mem : midpoint ℝ a.left a.right ∈ line[ℝ, a.left, a.right] :=
    AffineMap.lineMap_mem_affineSpan_pair _ _ _
  exact ⟨(sbtw_mid_midpoint_opposite_mid a hne).wbtw.wOppSide₁₃ hF_mem,
    a.mid_notMem_line hne, a.opposite_mid_notMem_line hne⟩

/-- In two dimensions, an arc's anchor and the opposite arc's anchor are strictly opposite
across the chord. -/
lemma sOppSide_mid_opposite_mid_line [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right) :
    line[ℝ, a.left, a.right].SOppSide a.mid a.opposite.mid := by
  have h := a.sOppSide_mid_opposite_mid hne
  rwa [lineOrOrthRadius_of_ne hne] at h

/-- In two dimensions, two arcs with the same distinct ordered endpoints are equal or opposite. -/
theorem eq_or_eq_opposite_of_left_eq_of_right_eq [Fact (Module.finrank ℝ V = 2)]
    {a b : Arc s} (hl : a.left = b.left) (hr : a.right = b.right)
    (hne : a.left ≠ a.right) : b = a ∨ b = a.opposite := by
  have hrad : s.radius ≠ 0 := radius_ne_zero_of_mem_of_mem_of_ne a.left_mem a.right_mem hne
  obtain ⟨r, hru⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (vsub_ne_zero.mpr hne.symm)
      (norm_ne_zero_iff.mp ((norm_vsub_center_eq_radius a.mid_mem).trans_ne hrad))
      (by rw [real_inner_comm, hl, hr]; exact b.inner_mid_vsub_center_right_vsub_left)
      (by rw [real_inner_comm]; exact a.inner_mid_vsub_center_right_vsub_left))
  have hr_abs : |r| = 1 := by
    have hnorm := congrArg norm hru
    rw [norm_smul, Real.norm_eq_abs, norm_vsub_center_eq_radius a.mid_mem,
      norm_vsub_center_eq_radius b.mid_mem] at hnorm
    exact mul_right_cancel₀ hrad (hnorm.trans (one_mul _).symm)
  rcases eq_or_eq_neg_of_abs_eq hr_abs with rfl | rfl
  · exact Or.inl (Arc.ext hl.symm (vsub_left_injective s.center (by simpa using hru.symm)))
  · exact Or.inr (Arc.ext hl.symm (vsub_left_injective s.center
      (by simpa [opposite_mid_vsub_center] using hru.symm)))

/-- In two dimensions, two arcs with distinct endpoints, the same ordered endpoints, and mids on the
same side of their common chord are equal as `Arc` objects. -/
theorem eq_of_left_eq_of_right_eq_of_sSameSide_mid [Fact (Module.finrank ℝ V = 2)]
    {a b : Arc s} (hl : a.left = b.left) (hr : a.right = b.right)
    (hne : a.left ≠ a.right)
    (hmid : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid b.mid) :
    a = b := by
  rcases eq_or_eq_opposite_of_left_eq_of_right_eq hl hr hne with rfl | rfl
  · rfl
  · exact absurd hmid (a.sOppSide_mid_opposite_mid hne).not_sSameSide

/-- In two dimensions, `a.opposite.mid` lies strictly on the same side of the
chord as `s.center` if and only if `a.mid` does not. -/
theorem sSameSide_opposite_mid_iff [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right)
    (h_center_not_mem : s.center ∉ line[ℝ, a.left, a.right]) :
    (s.lineOrOrthRadius a.left a.right).SSameSide a.opposite.mid s.center ↔
      ¬ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
  rw [lineOrOrthRadius_of_ne hne]
  set F : P := midpoint ℝ a.left a.right with hF_def
  set u : V := a.opposite.mid -ᵥ a.mid with hu_def
  have hsbtw : Sbtw ℝ a.mid F a.opposite.mid := by
    simpa only [hF_def] using sbtw_mid_midpoint_opposite_mid a hne
  obtain ⟨t, ⟨ht0, ht1⟩, htF⟩ := hsbtw.mem_image_Ioo
  have hF_mem : F ∈ line[ℝ, a.left, a.right] := by
    rw [hF_def]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hmid_not_mem := a.mid_notMem_line hne
  have homid_not_mem := a.opposite_mid_notMem_line hne
  have hSOpp := a.sOppSide_mid_opposite_mid_line hne
  have hmid_sub : (a.mid -ᵥ F : V) = (-t) • u := by
    rw [← htF, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_self, ← hu_def]
    module
  have homid_sub : (a.opposite.mid -ᵥ F : V) = (1 - t) • u := by
    rw [← htF, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, ← hu_def]
    module
  have hcenter_sub : (s.center -ᵥ F : V) = (1 / 2 - t) • u := by
    rw [← midpoint_mid_opposite_mid a, midpoint_vsub, hmid_sub, homid_sub]
    rw [invOf_eq_inv, one_div]
    module
  have ht_ne : t ≠ 1 / 2 := by
    rintro ht
    refine h_center_not_mem ?_
    have hcF : (s.center -ᵥ F : V) = 0 := by rw [hcenter_sub, ht, sub_self, zero_smul]
    rw [vsub_eq_zero_iff_eq.mp hcF]; exact hF_mem
  refine ⟨fun h_opp_ss h_mid_ss => (hSOpp.trans_sSameSide h_opp_ss).not_wSameSide h_mid_ss.1,
    fun h_not_mid => ?_⟩
  rcases lt_or_gt_of_ne ht_ne with ht | ht
  · exact AffineSubspace.sSameSide_of_vsub_eq_smul hF_mem hF_mem homid_sub hcenter_sub
      (mul_nonneg (by linarith) (by linarith)) homid_not_mem h_center_not_mem
  · exact absurd (AffineSubspace.sSameSide_of_vsub_eq_smul hF_mem hF_mem hmid_sub hcenter_sub
      (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hmid_not_mem h_center_not_mem)
      h_not_mid

/-- Taking the opposite arc is involutive. -/
theorem opposite_involutive : Function.Involutive (opposite (s := s)) :=
  opposite_opposite

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

/-- The minor-arc midpoint construction is symmetric in its endpoints. -/
lemma minorMidpoint_comm (s : Sphere P) (A C : P) :
    minorMidpoint s A C = minorMidpoint s C A := by
  unfold minorMidpoint
  rw [add_comm (A -ᵥ s.center) (C -ᵥ s.center)]

/-- On a sphere of nonzero radius, the minor-arc midpoint construction with equal endpoints
returns that endpoint. -/
lemma minorMidpoint_self {A : P}
    (hA : A ∈ s) (hr : s.radius ≠ 0) :
    minorMidpoint s A A = A := by
  rw [minorMidpoint, ← two_smul ℝ (A -ᵥ s.center), norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    norm_vsub_center_eq_radius hA, smul_smul,
    show s.radius / (2 * s.radius) * 2 = 1 by field_simp, one_smul, vsub_vadd]

/-- The minor arc from `A` to `C`. The mid is chosen on the shorter arc.
Requires `A` and `C` are not diametrically opposite (but `A = C` is allowed,
giving a single-point arc). -/
def minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) : Arc s where
  left := A
  mid := minorMidpoint s A C
  left_mem := hA
  mid_mem := minorMidpoint_mem hA hC hNotDiam

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
  have ha_norm : ‖a‖ = s.radius := by rw [ha_def]; exact norm_vsub_center_eq_radius hA
  have hc_norm : ‖c‖ = s.radius := by rw [hc_def]; exact norm_vsub_center_eq_radius hC
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

/-- Minor and major arcs are opposite to each other. -/
@[simp]
lemma minor_opposite_eq_major {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (minor hA hC hNotDiam).opposite = major hA hC hNotDiam := rfl

@[simp]
lemma major_opposite_eq_minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    (major hA hC hNotDiam).opposite = minor hA hC hNotDiam := by
  simp only [major, opposite_opposite]

/-- Under the non-diameter hypothesis, the minor and major branches are distinct `Arc` objects. -/
theorem minor_ne_major {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiam : ¬s.IsDiameter A C) :
    minor hA hC hNotDiam ≠ major hA hC hNotDiam := by
  intro h
  have hmc : (minor hA hC hNotDiam).mid = s.center := by
    have hm := midpoint_mid_opposite_mid (minor hA hC hNotDiam)
    rwa [minor_opposite_eq_major, ← h, midpoint_self] at hm
  have hr : s.radius = 0 := by
    rw [← norm_vsub_center_eq_radius (minor hA hC hNotDiam).mid_mem, hmc,
      vsub_self, norm_zero]
  exact hNotDiam ⟨hA, by
    rw [dist_eq_zero.mp ((mem_sphere.mp hA).trans hr),
      dist_eq_zero.mp ((mem_sphere.mp hC).trans hr), midpoint_self]⟩

/-- In two dimensions, `minor` and `major` exhaust the arcs with distinct ordered endpoints
`A` and `C`: no third arc has those endpoints. -/
theorem eq_minor_or_eq_major_of_ne [Fact (Module.finrank ℝ V = 2)]
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C) (hAC : A ≠ C)
    {a : Arc s} (hl : a.left = A) (hr : a.right = C) :
    a = minor hA hC hND ∨ a = major hA hC hND := by
  have h := eq_or_eq_opposite_of_left_eq_of_right_eq
    (a := minor hA hC hND) (b := a)
    (by rw [minor_left, hl]) (by rw [minor_right, hr])
    (by rw [minor_left, minor_right]; exact hAC)
  rwa [minor_opposite_eq_major] at h

open Classical in
/-- The mid of the arc from `A` to `C` passing through `B`. When `A ≠ C`, this is
constructed by normalizing the component of `B -ᵥ A` perpendicular to the chord `C -ᵥ A`.
When `A = C`, it normalizes the projection of `B -ᵥ A` onto the radius `A -ᵥ s.center`. -/
def throughMidpoint (s : Sphere P) (A B C : P) : P :=
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
  have hB_not_mem := notMem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC
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
def through {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
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
      have := notMem_lineOrOrthRadius_of_mem_sphere hA hB hA hBA hBA
      simp only [lineOrOrthRadius_of_eq] at this
      exact this (mem_orthRadius_iff_inner_left.mpr
        (by rwa [div_eq_zero_iff, inner_self_eq_zero, or_iff_left hrv_ne] at ht))
    have hcoeff : s.radius / ‖t • rv‖ * t ≠ 0 :=
      mul_ne_zero (div_ne_zero
        (by intro h; exact hrv_ne (norm_eq_zero.mp
          (by change ‖A -ᵥ s.center‖ = 0; rw [norm_vsub_center_eq_radius hA, h])))
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
      intro heq; exact (notMem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC)
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
      rw [hw_def, inner_sub_left, real_inner_smul_left,
          div_mul_cancel₀ _ (inner_self_ne_zero.mpr hd_ne), sub_self]
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
    (by rw [hrv_def, ← neg_vsub_eq_vsub_rev s.center A, inner_neg_right, neg_lt_zero]
        exact inner_vsub_center_vsub_pos hA hB hBA.symm)
    (real_inner_self_pos.mpr hrv_ne)
  have hrn : ‖rv‖ = s.radius := by rw [hrv_def]; exact norm_vsub_center_eq_radius hA
  have hr_ne : s.radius ≠ 0 := hrn ▸ norm_ne_zero_iff.mpr hrv_ne
  have ht_ne : t ≠ 0 := ne_of_lt ht_neg
  rw [AffineEquiv.pointReflection_apply, ← neg_vsub_eq_vsub_rev A s.center]
  congr 1
  rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_neg ht_neg, hrn,
      show s.radius / (-t * s.radius) * t = (-1 : ℝ) from by field_simp, neg_one_smul]

/-- When the endpoints coincide, `through A B A` is the corresponding major arc, independently
of which point `B` is used to select it. -/
theorem through_self_eq_major_self {A B : P} (hA : A ∈ s) (hB : B ∈ s) (hBA : B ≠ A)
    (hNotDiam : ¬s.IsDiameter A A) :
    through hA hB hA hBA hBA = major hA hA hNotDiam := by
  refine Arc.ext rfl ?_
  change throughMidpoint s A B A = AffineEquiv.pointReflection ℝ s.center (minorMidpoint s A A)
  rw [throughMidpoint_eq_antipodal_of_eq hA hB hBA,
    minorMidpoint_self hA (radius_ne_zero_of_mem_of_mem_of_ne hA hB hBA.symm)]

/-- The specified second point lies in the interior of the `through` arc. -/
lemma mem_interior_through [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    B ∈ (through hA hB hC hBA hBC).interior := by
  refine mem_interior_iff.mpr ⟨hB, ?_⟩
  change (s.lineOrOrthRadius A (through hA hB hC hBA hBC).right).SSameSide
    (throughMidpoint s A B C) B
  rw [through_right hA hB hC hBA hBC]
  have hB_not := notMem_lineOrOrthRadius_of_mem_sphere hA hB hC hBA hBC
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
      (by rw [hrv_def, ← neg_vsub_eq_vsub_rev s.center A, inner_neg_right, neg_lt_zero]
          exact inner_vsub_center_vsub_pos hA hB hBA.symm)
      (real_inner_self_pos.mpr hrv_ne)
    have hcA : s.center -ᵥ A = -rv := by rw [hrv_def, neg_vsub_eq_vsub_rev]
    set foot := ((B -ᵥ A) - t • rv) +ᵥ A
    have hfoot_mem : foot ∈ s.orthRadius A := by
      rw [mem_orthRadius_iff_inner_left, vadd_vsub, inner_sub_left,
          inner_smul_left, conj_trivial, ht_def,
          div_mul_cancel₀ _ (inner_self_ne_zero.mpr hrv_ne), sub_self]
    have hB_foot : B -ᵥ foot = t • rv := by
      conv_lhs => rw [show B = ((B -ᵥ A) +ᵥ A) from (vsub_vadd B A).symm]
      rw [vadd_vsub_vadd_cancel_right, sub_sub_cancel]
    have hx_sub : AffineEquiv.pointReflection ℝ s.center A -ᵥ A = (-2 : ℝ) • rv := by
      rw [AffineEquiv.pointReflection_apply, vadd_vsub_assoc, hcA,
          show -rv + -rv = (-2 : ℝ) • rv from by rw [← neg_one_smul ℝ rv, ← add_smul]; norm_num]
    refine AffineSubspace.sSameSide_of_vsub_eq_smul (self_mem_orthRadius s A) hfoot_mem hx_sub
      hB_foot (by linarith) ?_ ?_
    · intro h
      rw [mem_orthRadius_iff_inner_left, AffineEquiv.pointReflection_apply,
          vadd_vsub_assoc, hcA, inner_add_left, inner_neg_left] at h
      linarith [real_inner_self_pos.mpr hrv_ne]
    · rwa [lineOrOrthRadius_of_eq rfl] at hB_not
  · unfold throughMidpoint
    rw [ite_eq_right hAC, lineOrOrthRadius_of_ne hAC]
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
    have hw_perp : ⟪w, d⟫ = 0 := by
      rw [hw_def, inner_sub_left, real_inner_smul_left,
          div_mul_cancel₀ _ (inner_self_ne_zero.mpr hd_ne), sub_self]
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
    refine AffineSubspace.sSameSide_of_vsub_eq_smul hM_mem hproj_mem htm_M
      (hBproj.trans (one_smul ℝ w).symm) (by rw [mul_one]; exact hcoeff.le) ?_
      (lineOrOrthRadius_of_ne hAC ▸ hB_not)
    intro htm
    exact hw_ne <| by
      have h : (s.radius / ‖w‖ + β) • w ∈ Submodule.span ℝ {d} := by
        have := htm_M ▸ AffineSubspace.vsub_mem_direction htm hM_mem
        rwa [direction_affineSpan, Set.pair_comm, vectorSpan_pair] at this
      have h2 : w ∈ Submodule.span ℝ {d} :=
        (Submodule.smul_mem_iff _ hcoeff.ne').mp h
      have hmem := Submodule.mem_inf.mpr ⟨h2, hmw⟩
      rwa [disjoint_iff.mp (Submodule.orthogonal_disjoint _), Submodule.mem_bot] at hmem

/-- The specified second point lies in the `through` arc. -/
lemma mem_through [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) : B ∈ through hA hB hC hBA hBC :=
  mem_of_mem_interior (mem_interior_through hA hB hC hBA hBC)

/-- The arc on `s` from `A` to `C` not passing through `B`. -/
def avoiding {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
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

/-- The specified second point does not lie in the `avoiding` arc. -/
lemma notMem_avoiding [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C) :
    B ∉ avoiding hA hB hC hBA hBC := by
  intro hmem
  rcases mem_iff.mp hmem with ⟨_, hleft | hright | hss⟩
  · exact hBA (by simpa using hleft)
  · exact hBC (by simpa [avoiding_right hA hB hC hBA hBC] using hright)
  · by_cases hAC : A = C
    · subst C
      have hmid : (avoiding hA hB hC hBA hBC).mid = A := by
        rw [avoiding_mid, throughMidpoint_eq_antipodal_of_eq hA hB hBA]
        exact AffineEquiv.pointReflection_involutive ℝ s.center A
      exact hss.left_notMem (by
        rw [hmid, avoiding_left]
        exact left_mem_lineOrOrthRadius)
    · have hne : (through hA hB hC hBA hBC).left ≠
          (through hA hB hC hBA hBC).right := by
        simp only [through_left, through_right hA hB hC hBA hBC]
        exact hAC
      have h_opp := sOppSide_mid_opposite_mid_line (through hA hB hC hBA hBC) hne
      have h_ss := sSameSide_of_mem_interior
        (mem_interior_through hA hB hC hBA hBC)
      simp only [avoiding_left, avoiding_right hA hB hC hBA hBC,
        through_left, through_right hA hB hC hBA hBC] at hss h_ss h_opp
      rw [lineOrOrthRadius_of_ne hAC] at hss h_ss
      exact (h_opp.symm.trans_sSameSide h_ss).not_wSameSide hss.wSameSide

@[simp]
lemma through_opposite {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (through hA hB hC hBA hBC).opposite = avoiding hA hB hC hBA hBC := rfl

@[simp]
lemma avoiding_opposite {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) :
    (avoiding hA hB hC hBA hBC).opposite = through hA hB hC hBA hBC := by
  simp only [avoiding, opposite_opposite]

end Arc

end

end Sphere

end EuclideanGeometry
