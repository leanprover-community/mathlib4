/-
Copyright (c) 2025.
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

* `Delone.UniformlyDiscrete (D : Set X)`
  There is a positive packing radius separating distinct points of `D`.

* `Delone.RelativelyDense (D : Set X)`
  There is a positive covering radius so that `R`-balls around `D` cover `X`.

* `DeloneSet X`
  A structure bundling a nonempty uniformly discrete and relatively dense set.

## Main results

* `DeloneSet.nonempty`
* `DeloneSet.exists_covering_radius`
* `DeloneSet.exists_packing_radius`
* `DeloneSet.dist_pos_of_ne`
* `DeloneSet.map` (image of a Delone set under an isometry is Delone)
-/

@[expose] public section

open Metric

namespace Delone

/-- A set `D` in a metric space is *uniformly discrete* if there exists `r > 0`
such that distinct points of `D` are at least distance `r` apart. -/
def UniformlyDiscrete {X : Type*} [MetricSpace X] (D : Set X) : Prop :=
  ∃ r > 0, ∀ ⦃x y⦄, x ∈ D → y ∈ D → x ≠ y → dist x y ≥ r

/-- A set `D` in a metric space is *relatively dense* if there exists `R > 0`
such that every point of the space is within distance `R` of some point in `D`. -/
def RelativelyDense {X : Type*} [MetricSpace X] (D : Set X) : Prop :=
  ∃ R > 0, ∀ x : X, ∃ y ∈ D, dist x y ≤ R

/-- The image of a uniformly discrete set under a subset relation is uniformly discrete. -/
lemma uniformlyDiscrete_mono {X} [MetricSpace X] {D E : Set X} (hDE : D ⊆ E) :
    UniformlyDiscrete E → UniformlyDiscrete D := by
  rintro ⟨r, hr, hsep⟩
  refine ⟨r, hr, ?_⟩
  intro x y hx hy hne
  exact hsep (hDE hx) (hDE hy) hne

/-- The image of a relatively dense set under a subset relation is relatively dense. -/
lemma relativelyDense_mono {X} [MetricSpace X] {D E : Set X} (hDE : D ⊆ E) :
    RelativelyDense D → RelativelyDense E := by
  rintro ⟨R, hR, hcov⟩
  refine ⟨R, hR, ?_⟩
  intro x
  rcases hcov x with ⟨y, hyD, hxy⟩
  exact ⟨y, hDE hyD, hxy⟩

end Delone

/-- A **Delone set** in a metric space: uniformly discrete and relatively dense. -/
structure DeloneSet (X : Type*) [MetricSpace X] where
  carrier : Set X
  uniformlyDiscrete : Delone.UniformlyDiscrete carrier
  relativelyDense : Delone.RelativelyDense carrier

attribute [simp] DeloneSet.carrier

namespace DeloneSet

variable {X : Type*} [MetricSpace X]

/-- A Delone set is nonempty. -/
lemma nonempty {X : Type*} [MetricSpace X] [Inhabited X] (D : DeloneSet X) :
    D.carrier.Nonempty := by
  rcases D.relativelyDense with ⟨R, hR, hcov⟩
  rcases hcov (default : X) with ⟨y, hyD, _⟩
  exact ⟨y, hyD⟩

/-- Extract the covering radius of a Delone set. -/
lemma exists_covering_radius (D : DeloneSet X) :
    ∃ R > 0, ∀ x : X, ∃ y ∈ D.carrier, dist x y ≤ R :=
  D.relativelyDense

/-- Extract the packing radius of a Delone set. -/
lemma exists_packing_radius (D : DeloneSet X) :
    ∃ r > 0, ∀ ⦃x y⦄, x ∈ D.carrier → y ∈ D.carrier → x ≠ y → dist x y ≥ r :=
  D.uniformlyDiscrete

/-- If two points of a Delone set are distinct, they are at positive distance. -/
lemma dist_pos_of_ne {D : DeloneSet X} {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) : 0 < dist x y := by
  rcases D.exists_packing_radius with ⟨r, hr, hsep⟩
  have hxy := hsep hx hy hne
  exact lt_of_lt_of_le hr hxy

/-- Every point of the space is within the covering radius of some point of a Delone set. -/
lemma exists_close_point (D : DeloneSet X) :
    ∃ R > 0, ∀ x : X, ∃ y ∈ D.carrier, dist x y ≤ R :=
D.exists_covering_radius

/-- A small ball contains at most one point of a Delone set. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ x y z,
      x ∈ D.carrier →
      y ∈ D.carrier →
      z ∈ D.carrier →
      dist x z < r / 2 →
      dist z y < r / 2 →
      x = y := by
  rcases D.exists_packing_radius with ⟨ρ, hρ, hsep⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x y z hx hy hz hxz hyz
  have hxy_lt : dist x y < ρ := by
    have := calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hxz hyz
      _ = ρ := by ring
    simpa using this
  by_contra hne
  have hge := hsep hx hy hne
  exact lt_irrefl _ (lt_of_lt_of_le hxy_lt hge)

/-- The image of a Delone set under an isometry is a Delone set. -/
def map {Y : Type*} [MetricSpace Y] (f : X ≃ᵢ Y) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  uniformlyDiscrete := by
    rcases D.uniformlyDiscrete with ⟨r, hr, hsep⟩
    refine ⟨r, hr, ?_⟩
    intro y y' hy hy' hne
    rcases hy with ⟨x, hx, rfl⟩
    rcases hy' with ⟨x', hx', rfl⟩
    have hxne : x ≠ x' := by grind
    have := hsep hx hx' hxne
    simpa using f.dist_eq x x' ▸ this
  relativelyDense := by
    rcases D.relativelyDense with ⟨R, hR, hcov⟩
    refine ⟨R, hR, ?_⟩
    intro y
    rcases hcov (f.symm y) with ⟨x, hxD, hxR⟩
    refine ⟨f x, ⟨x, hxD, rfl⟩, ?_⟩
    have hdist : dist y (f x) = dist (f.symm y) x := by
      simpa [f.apply_symm_apply y] using
        f.dist_eq (f.symm y) x
    simpa [hdist] using hxR
}

@[ext] lemma ext {X : Type*} [MetricSpace X] {D E : DeloneSet X}
    (h : D.carrier = E.carrier) : D = E := by
  cases D; cases E; cases h; rfl

lemma map_id (D : DeloneSet X) :
    D.map (IsometryEquiv.refl X) = D := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyD, rfl⟩
    exact hyD
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma map_comp
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (D : DeloneSet X)
    (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.map (f.trans g) = (D.map f).map g := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hxD, rfl⟩
    exact ⟨f x, ⟨x, hxD, rfl⟩, by simp⟩
  · intro hz
    rcases hz with ⟨y, hyf, rfl⟩
    rcases hyf with ⟨x, hxD, rfl⟩
    exact ⟨x, hxD, by simp⟩

lemma map_symm
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (D : DeloneSet X) (f : X ≃ᵢ Y) :
    (D.map f).map f.symm = D := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨x₀, hx₀D, rfl⟩
    simpa
  · intro hx
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp⟩

end DeloneSet
