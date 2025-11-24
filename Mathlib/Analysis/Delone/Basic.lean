/-
Copyright (c) 2025 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Isometry

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

* `DeloneSet.nonempty`
* `DeloneSet.dist_pos_of_ne`
* `DeloneSet.subset_ball_singleton`
* `DeloneSet.map`
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
lemma uniformlyDiscrete_mono {D E : Set X} (hDE : D ⊆ E) :
    UniformlyDiscrete E → UniformlyDiscrete D := by
  rintro ⟨r, hr, hsep⟩
  refine ⟨r, hr, fun x y hx hy hne ↦ ?_⟩
  exact hsep (hDE hx) (hDE hy) hne

/-- If `D ⊆ E` and `D` is relatively dense, then so is `E`. -/
lemma relativelyDense_mono {D E : Set X} (hDE : D ⊆ E) :
    RelativelyDense D → RelativelyDense E := by
  rintro ⟨R, hR, hcov⟩
  refine ⟨R, hR, fun x ↦ ?_⟩
  rcases hcov x with ⟨y, hyD, hxy⟩
  exact ⟨y, hDE hyD, hxy⟩

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
lemma nonempty [Inhabited X] (D : DeloneSet X) : D.carrier.Nonempty := by
  obtain ⟨R, hR, hcov⟩ := D.relativelyDense
  rcases hcov (default : X) with ⟨y, hyD, _⟩
  exact ⟨y, hyD⟩

/-- Distinct points in a Delone set are at positive distance. -/
lemma dist_pos_of_ne {D : DeloneSet X} {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    0 < dist x y := by
  obtain ⟨r, hr, hsep⟩ := D.uniformlyDiscrete
  exact lt_of_lt_of_le hr <| hsep hx hy hne

/-- At most one point of a Delone set lies in a sufficiently small ball. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ x y z, x ∈ D.carrier → y ∈ D.carrier → z ∈ D.carrier →
      dist x z < r / 2 → dist z y < r / 2 → x = y := by
  obtain ⟨ρ, hρ, hsep⟩ := D.uniformlyDiscrete
  refine ⟨ρ, hρ, fun x y z hx hy hz hxz hyz ↦ ?_⟩
  have hxy_lt : dist x y < ρ := by
    have := calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hxz hyz
      _ = ρ := by ring
    simpa using this
  by_contra hne
  exact lt_irrefl _ (lt_of_lt_of_le hxy_lt <| hsep hx hy hne)

/-- The image of a Delone set under an isometry is a Delone set. -/
def map (f : X ≃ᵢ Y) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  uniformlyDiscrete := by
    obtain ⟨r, hr, hsep⟩ := D.uniformlyDiscrete
    refine ⟨r, hr, ?_⟩
    rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ hne
    simpa using f.dist_eq x x' ▸ (hsep hx hx' (by grind))
  relativelyDense := by
    obtain ⟨R, hR, hcov⟩ := D.relativelyDense
    refine ⟨R, hR, fun y ↦ ?_⟩
    obtain ⟨x, hxD, hxR⟩ := hcov (f.symm y)
    refine ⟨f x, ⟨x, hxD, rfl⟩, ?_⟩
    have hdist : dist y (f x) = dist (f.symm y) x := by
      simpa [f.apply_symm_apply y] using
        f.dist_eq (f.symm y) x
    simpa [hdist] using hxR
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
