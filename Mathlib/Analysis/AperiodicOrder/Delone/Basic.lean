/-
Copyright (c) 2026 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Cover

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **uniformly discrete**: there exists `packingRadius > 0` such that distinct points of `D`
  are separated by a distance strictly greater than `packingRadius`;
* **relatively dense**: there exists `coveringRadius > 0` such that every point of `X`
  lies within distance `coveringRadius` of some point of `D`.

The `DeloneSet` structure stores the set together with explicit radii witnessing
these properties. The definitions use metric entourages so that the theory fits
naturally into the uniformity framework.

Delone sets appear in discrete geometry, crystallography, aperiodic order, and tiling theory.

## Main definitions

* `Delone.DeloneSet X`: The main structure representing a Delone set in a metric space `X`.
* `DeloneSet.mapBilipschitz`: Transports a Delone set along a bilipschitz equivalence,
  scaling the radii.
* `DeloneSet.mapIsometry` Preserves the packing and covering radii exactly; see
  `mapIsometry_packingRadius` and `mapIsometry_coveringRadius`.

## Basic properties

* `packingRadius_lt_dist_of_mem_ne` : Distinct points in a Delone set are further apart than
  the packing radius.
* `dist_le_coveringRadius` : Every point of the space lies within the covering radius of the set.
* `subset_ball_singleton` : Any ball of sufficiently small radius contains at most one point of
  the set.

## Implementation notes

Delone sets are bundled as a structure rather than defined via a predicate (e.g. `IsDelone`).
This treats them as first-class objects for dynamical systems constructions (like hulls and patches)
and eliminates the need to manually pass proofs that these operations preserve the Delone property.
-/

@[expose] public section

open scoped Uniformity ENNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Delone

open Metric
open scoped NNReal

/-- A **Delone set** consists of a set together with explicit radii
witnessing uniform discreteness and relative denseness. -/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set. -/
  carrier : Set X
  /-- Radius such that distinct points of `carrier` are separated by more than `r`. -/
  packingRadius : ℝ≥0
  packingRadius_pos : 0 < packingRadius
  isSeparated_packingRadius : IsSeparated packingRadius carrier
  /-- Radius such that every point of the space is within `R` of `carrier`. -/
  coveringRadius : ℝ≥0
  coveringRadius_pos : 0 < coveringRadius
  isCover_coveringRadius : IsCover coveringRadius .univ carrier

attribute [simp] DeloneSet.carrier

namespace DeloneSet

lemma nonempty [Nonempty X] (D : DeloneSet X) : D.carrier.Nonempty :=
  D.isCover_coveringRadius.nonempty Set.univ_nonempty

lemma packingRadius_lt_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    D.packingRadius < dist x y := by
  have hsep : ENNReal.ofReal D.packingRadius < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.isSeparated_packingRadius hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep

lemma exists_dist_le_coveringRadius (D : DeloneSet X) (x : X) :
  ∃ y ∈ D.carrier, dist x y ≤ D.coveringRadius := by
  obtain ⟨y, hy, hdist⟩ := D.isCover_coveringRadius (x := x) (by trivial)
  exact ⟨y, hy, by simpa [edist_dist] using hdist⟩

lemma eq_of_mem_ball (D : DeloneSet X) {x y z : X} (hx : x ∈ D.carrier) (hy : y ∈ D.carrier)
    (hxz : x ∈ ball z (D.packingRadius / 2)) (hyz : y ∈ ball z (D.packingRadius / 2)) :
    x = y := by
  by_contra hne
  have htri := (dist_triangle x z y).trans_lt
    (add_lt_add (mem_ball.mp hxz) (by rwa [dist_comm, ← mem_ball]))
  rw [add_halves] at htri
  exact (D.packingRadius_lt_dist_of_mem_ne hx hy hne).not_gt htri

/-- There exists a radius `r > 0` such that any ball of radius `r`
centered at a point of `D` contains at most one point of `D`. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ {x y z}, x ∈ D.carrier → y ∈ D.carrier → x ∈ ball z r → y ∈ ball z r → x = y :=
  ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, fun hx hy => D.eq_of_mem_ball hx hy⟩

/-- Bilipschitz maps send Delone sets to Delone sets. -/
noncomputable def mapBilipschitz (f : X ≃ Y) (K₁ K₂ : ℝ≥0) (hK₁ : 0 < (K₁ : ℝ)) (hK₂ : 0 < (K₂ : ℝ))
    (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  packingRadius := D.packingRadius / K₁
  packingRadius_pos := div_pos D.packingRadius_pos hK₁
  isSeparated_packingRadius := D.isSeparated_packingRadius.image_antilipschitz hf₁ hK₁
  coveringRadius := K₂ * D.coveringRadius
  coveringRadius_pos := mul_pos hK₂ D.coveringRadius_pos
  isCover_coveringRadius := D.isCover_coveringRadius.image_lipschitz_of_surjective hf₂ f.surjective
}

/-- The image of a Delone set under an isometry. This is a specialization of
`DeloneSet.mapBiLipschitz` where the packing and covering radii are preserved because the
Lipschitz constants are both 1. -/
noncomputable def mapIsometry (D : DeloneSet X) (f : X ≃ᵢ Y) : DeloneSet Y :=
  D.mapBilipschitz f.toEquiv 1 1 zero_lt_one zero_lt_one
    f.isometry.antilipschitz f.isometry.lipschitz

@[simp] lemma mapIsometry_packingRadius (D : DeloneSet X) (f : X ≃ᵢ Y) :
  (D.mapIsometry f).packingRadius = D.packingRadius := by
  simp only [mapIsometry, mapBilipschitz, div_one]

@[simp] lemma mapIsometry_coveringRadius (D : DeloneSet X) (f : X ≃ᵢ Y) :
  (D.mapIsometry f).coveringRadius = D.coveringRadius := by
  simp only [mapIsometry, mapBilipschitz, IsometryEquiv.coe_toEquiv, div_one, one_mul]

/-- Extensionality for Delone sets. -/
@[ext] lemma ext {D E : DeloneSet X}
    (h_carrier : D.carrier = E.carrier)
    (h_packing : D.packingRadius = E.packingRadius)
    (h_covering : D.coveringRadius = E.coveringRadius) : D = E := by
  cases D; cases E; congr

lemma mapIsometry_id (D : DeloneSet X) : D.mapIsometry (IsometryEquiv.refl X) = D := by
  ext <;> simp only [mapIsometry, mapBilipschitz, IsometryEquiv.coe_toEquiv, div_one,
    one_mul, Set.mem_image]
  exact exists_eq_right

lemma mapIsometry_comp {Z : Type*} [MetricSpace Z]
    (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.mapIsometry (f.trans g) = (D.mapIsometry f).mapIsometry g := by
  ext <;> simp [mapIsometry, mapBilipschitz]

lemma mapIsometry_symm (D : DeloneSet X) (f : X ≃ᵢ Y) :
    (D.mapIsometry f).mapIsometry f.symm = D := by
  ext <;> simp [mapIsometry, mapBilipschitz]

end DeloneSet

end Delone
