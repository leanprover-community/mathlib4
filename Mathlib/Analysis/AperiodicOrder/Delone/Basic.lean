/-
Copyright (c) 2025 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **uniformly discrete**: there exists `r > 0` such that any two distinct points
  of `D` are at distance at least `r`;
* **relatively dense**: there exists `R > 0` such that every point of `X`
  is within distance `R` of some point of `D`.

Delone sets arise in discrete geometry, crystallography, quasicrystals,
aperiodic order, and tiling theory.

## Main definitions

* `UniformlyDiscrete (D : Set X)`
  Positive packing radius separating distinct points of `D`.

* `RelativelyDense (D : Set X)`
  Positive covering radius so that `R`-balls around `D` cover `X`.

* `DeloneSet X`
  A structure bundling a uniformly discrete and relatively dense set.

## Basic properties

* Canonical radii: `DeloneSet.coveringRadius`, `DeloneSet.packingRadius`,
  with corresponding bounds `dist_le_coveringRadius` and `le_dist_of_mem_ne`.
* `DeloneSet.dist_pos_of_ne`: distinct points lie at positive distance.
* `DeloneSet.subset_ball_singleton`: small balls contain at most one point of a Delone set.
* `DeloneSet.map`: Delone sets are preserved by isometries (with `map_id`, `map_comp`, `map_symm`).
-/

@[expose] public section

open Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Metric

/-- A set `D` in a metric space is *uniformly discrete* if there exists `r > 0`
such that distinct points of `D` are at least distance `r` apart. -/
def UniformlyDiscrete (D : Set X) : Prop :=
    ∃ r > 0, ∀ ⦃x y⦄, x ∈ D → y ∈ D → x ≠ y → r ≤ dist x y

/-- A set `D` in a metric space is *relatively dense* if there exists `R > 0`
such that every point of the space is within distance `R` of some point in `D`. -/
def RelativelyDense (D : Set X) : Prop :=
    ∃ R > 0, ∀ x : X, ∃ y ∈ D, dist x y ≤ R

/-- If `D ⊆ E` and `E` is uniformly discrete, then so is `D`. -/
lemma UniformlyDiscrete.mono {D E : Set X} (hDE : D ⊆ E) :
    UniformlyDiscrete E → UniformlyDiscrete D := by
  rintro ⟨r, hr, hsep⟩
  refine ⟨r, hr, fun x y hx hy hne ↦ ?_⟩
  exact hsep (hDE hx) (hDE hy) hne

/-- If `D ⊆ E` and `D` is relatively dense, then so is `E`. -/
lemma RelativelyDense.mono {D E : Set X} (hDE : D ⊆ E) :
    RelativelyDense D → RelativelyDense E := by
  rintro ⟨R, hR, hcov⟩
  refine ⟨R, hR, fun x ↦ ?_⟩
  rcases hcov x with ⟨y, hyD, hxy⟩
  exact ⟨y, hDE hyD, hxy⟩

lemma RelativelyDense.cthickening_eq_univ
    {X : Type*} [MetricSpace X] {D : Set X} :
    RelativelyDense D → ∃ R > 0, cthickening R D = Set.univ := by
  rintro ⟨R, hRpos, hcov⟩
  refine ⟨R, hRpos, ?_⟩
  ext x; constructor
  · intro _; trivial
  · intro _; rcases hcov x with ⟨y, hyD, hxy⟩
    exact mem_cthickening_of_dist_le x y R D hyD hxy

end Metric

namespace Delone

/-- A **Delone set** in a metric space: uniformly discrete and relatively dense. -/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set of a Delone set. -/
  (carrier : Set X)
  /-- Uniform discreteness: distinct points of the set are separated by a positive distance. -/
  (uniformlyDiscrete : UniformlyDiscrete carrier)
  /-- Relative denseness: every point of the space is within some bounded distance of the set. -/
  (relativelyDense : RelativelyDense carrier)

attribute [simp] DeloneSet.carrier

namespace DeloneSet

/-- A Delone set is nonempty. -/
lemma nonempty [Nonempty X] (D : DeloneSet X) : Nonempty D.carrier := by
  obtain ⟨_, _, hcov⟩ := D.relativelyDense
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hyD, _⟩ := hcov x
  exact ⟨y, hyD⟩

noncomputable def coveringRadius (D : DeloneSet X) : ℝ :=
  Classical.choose D.relativelyDense

lemma coveringRadius_pos (D : DeloneSet X) :
    0 < D.coveringRadius :=
  (Classical.choose_spec D.relativelyDense).1

lemma dist_le_coveringRadius (D : DeloneSet X) (x : X) :
    ∃ y ∈ D.carrier, dist x y ≤ D.coveringRadius :=
  (Classical.choose_spec D.relativelyDense).2 x

noncomputable def packingRadius (D : DeloneSet X) : ℝ :=
  Classical.choose D.uniformlyDiscrete

lemma packingRadius_pos (D : DeloneSet X) :
    0 < D.packingRadius :=
  (Classical.choose_spec D.uniformlyDiscrete).1

lemma le_dist_of_mem_ne (D : DeloneSet X)
    {x y : X} (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    D.packingRadius ≤ dist x y :=
  (Classical.choose_spec D.uniformlyDiscrete).2 hx hy hne

/-- Distinct points in a Delone set are at positive distance. -/
lemma dist_pos_of_ne {D : DeloneSet X} {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    0 < dist x y :=
  lt_of_lt_of_le D.packingRadius_pos <| D.le_dist_of_mem_ne hx hy hne

/--
If the packing radius of a Delone set is `r`, then for any `z : X` the open ball
`ball z (r / 2)` contains at most one point of the Delone set. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ ⦃x y z⦄, x ∈ D.carrier → y ∈ D.carrier → z ∈ D.carrier →
    x ∈ ball z r → y ∈ ball z r → x = y := by
  refine ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, ?_⟩
  intro x y z hx hy hz hxz hyz
  by_contra hne
  have hlt : dist x y < D.packingRadius := by
    have hsum_lt : dist x z + dist z y < D.packingRadius := by
      simpa [add_halves] using (add_lt_add hxz <| mem_ball'.mp hyz)
    exact lt_of_le_of_lt (dist_triangle x z y) hsum_lt
  exact (not_lt_of_ge <| D.le_dist_of_mem_ne hx hy hne) hlt

/-- The image of a Delone set under an isometry is a Delone set. -/
def map (f : X ≃ᵢ Y) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  uniformlyDiscrete := by
    refine ⟨D.packingRadius, D.packingRadius_pos, ?_⟩
    rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ hne
    simpa [f.dist_eq] using D.le_dist_of_mem_ne hx hx' (by grind)
  relativelyDense := by
    refine ⟨D.coveringRadius, D.coveringRadius_pos, ?_⟩
    intro y
    obtain ⟨x, hxD, hdist⟩ := D.dist_le_coveringRadius (f.symm y)
    refine ⟨f x, ⟨x, hxD, rfl⟩, ?_⟩
    have hdist' : dist y (f x) = dist (f.symm y) x := by
      simpa [f.apply_symm_apply y] using
        f.dist_eq (f.symm y) x
    simpa [hdist'] using hdist
}

@[ext] lemma ext {D E : DeloneSet X} (h : D.carrier = E.carrier) : D = E := by
  cases D; cases E; cases h; rfl

lemma map_id (D : DeloneSet X) : D.map (IsometryEquiv.refl X) = D := by
  ext x; constructor
  · rintro ⟨y, hyD, rfl⟩; exact hyD
  · intro hx; exact ⟨x, hx, rfl⟩

lemma map_comp {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.map (f.trans g) = (D.map f).map g := by
  ext z; constructor
  · rintro ⟨x, hxD, rfl⟩; exact ⟨f x, ⟨x, hxD, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hxD, rfl⟩, rfl⟩; exact ⟨x, hxD, rfl⟩

lemma map_symm (D : DeloneSet X) (f : X ≃ᵢ Y) : (D.map f).map f.symm = D := by
  ext x; constructor
  · rintro ⟨y, ⟨x₀, hx₀D, rfl⟩, rfl⟩; simpa
  · intro hx; exact ⟨f x, ⟨x, hx, rfl⟩, by simp⟩

end DeloneSet

end Delone
