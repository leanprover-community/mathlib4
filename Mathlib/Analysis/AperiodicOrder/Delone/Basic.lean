/-
Copyright (c) 2025 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **uniformly discrete**: there exists a sufficiently small scale at which
  distinct points of `D` are separated.
* **relatively dense**: there exists a sufficiently large scale at which
  every point of `X` is close to some point of `D`.

In metric terms, this means that there exist constants `r > 0` and `R > 0`
such that distinct points of `D` are at distance at least `r`, and every point
of `X` lies within distance `R` of `D`.

In this file, these notions are formulated in terms of **metric entourages**
(i.e. relations belonging to the uniformity), rather than directly using
metric inequalities. This makes the theory compatible with the general
uniform-space infrastructure.

Delone sets arise in discrete geometry, crystallography, quasicrystals,
aperiodic order, and tiling theory.

## Main definitions

* `UniformlyDiscrete (D : Set X)`
  Existence of an entourage separating distinct points of `D`.

* `RelativelyDense (D : Set X)`
  Existence of an entourage whose image of `D` covers the whole space.

* `DeloneSet X`
  A structure bundling a uniformly discrete and relatively dense set.

## Basic properties

* Canonical radii: `DeloneSet.coveringRadius`, `DeloneSet.packingRadius`,
  with corresponding bounds `dist_le_coveringRadius` and `le_dist_of_mem_ne`.
* `DeloneSet.dist_pos_of_ne`: distinct points lie at positive distance.
* `DeloneSet.subset_ball_singleton`: small balls contain at most one point of a Delone set.
* `DeloneSet.map`: Delone sets are preserved by isometries (with `map_id`, `map_comp`, `map_symm`).

## TODO

The definition `distLT` is a temporary metric-derived entourage used to
phrase the theory of Delone sets in terms of relations / entourages.

Once mathlib provides a canonical family of entourages indexed by a quantitative
parameter (e.g. `ℝ≥0`) for metric spaces, this definition should be removed and
all occurrences of `distLT ε` replaced by the corresponding canonical entourage.
-/

@[expose] public section

open scoped Uniformity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Metric

/-- The metric `ε`-entourage as a relation (a set of pairs). -/
def distLT (ε : ℝ) : SetRel X X :=
  {p : X × X | dist p.1 p.2 < ε}

/-- If `ε > 0`, then the metric entourage `distLT ε` belongs to the uniformity. -/
lemma distLT_mem_uniformity {ε : ℝ} (hε : 0 < ε) : distLT (X := X) ε ∈ 𝓤 X := by
  refine (mem_uniformity_dist).2 ?_
  refine ⟨ε, hε, ?_⟩
  exact fun ⦃a b⦄ a₁ ↦ a₁

/-- A set `D` is uniformly discrete if some metric entourage separates
distinct points of `D`. -/
def UniformlyDiscrete (D : Set X) : Prop :=
  ∃ r > 0, ∀ ⦃x y⦄, x ∈ D → y ∈ D → x ≠ y → (x, y) ∉ distLT (X := X) r

/-- A set `D` is relatively dense if some metric entourage covers the
whole space from `D`. -/
def RelativelyDense (D : Set X) : Prop :=
  ∃ R > 0, ∀ x : X, ∃ y ∈ D, (x, y) ∈ distLT (X := X) R

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
  obtain ⟨y, hyD, hxy⟩ := hcov x
  exact ⟨y, hDE hyD, hxy⟩

lemma RelativelyDense.cthickening_eq_univ
    {X : Type*} [MetricSpace X] {D : Set X} :
    RelativelyDense D → ∃ R > 0, cthickening R D = Set.univ := by
  rintro ⟨R, hRpos, hcov⟩
  refine ⟨R, hRpos, ?_⟩
  ext x; constructor
  · intro _; trivial
  · intro _; obtain ⟨y, hyD, hxy⟩ := hcov x
    have : dist x y ≤ R := by
      simpa [distLT] using (le_of_lt hxy)
    exact mem_cthickening_of_dist_le x y R D hyD this

end Metric

namespace Delone

open Metric

/-- A **Delone set** in a metric space: uniformly discrete and relatively dense. -/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set of a Delone set. -/
  (carrier : Set X)
  /-- Uniform discreteness: distinct points of the set are separated by a
  sufficiently small entourage. -/
  (uniformlyDiscrete : UniformlyDiscrete carrier)
  /-- Relative denseness: every point of the space is related by a bounded
  entourage to the set. -/
  (relativelyDense : RelativelyDense carrier)

attribute [simp] DeloneSet.carrier

namespace DeloneSet

/-- A Delone set is nonempty. -/
lemma nonempty [Nonempty X] (D : DeloneSet X) : Nonempty D.carrier := by
  obtain ⟨_, _, hcov⟩ := D.relativelyDense
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hyD, _⟩ := hcov x
  exact ⟨y, hyD⟩

/-- The **covering radius** of a Delone set: a chosen constant `R > 0` such that every
point of the ambient space lies within distance `R` of some point of the set. -/
noncomputable def coveringRadius (D : DeloneSet X) : ℝ :=
  Classical.choose D.relativelyDense

lemma coveringRadius_pos (D : DeloneSet X) : 0 < D.coveringRadius :=
  (Classical.choose_spec D.relativelyDense).1

lemma dist_le_coveringRadius (D : DeloneSet X) (x : X) :
    ∃ y ∈ D.carrier, dist x y ≤ D.coveringRadius := by
  obtain ⟨y, hy, hxy⟩ := (Classical.choose_spec D.relativelyDense).2 x
  refine ⟨y, hy, ?_⟩
  simpa [distLT] using (le_of_lt hxy)

/-- The **packing radius** of a Delone set: a chosen constant `r > 0` such that any
two distinct points of the set are at distance at least `r`. -/
noncomputable def packingRadius (D : DeloneSet X) : ℝ :=
  Classical.choose D.uniformlyDiscrete

lemma packingRadius_pos (D : DeloneSet X) : 0 < D.packingRadius :=
  (Classical.choose_spec D.uniformlyDiscrete).1

lemma le_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    D.packingRadius ≤ dist x y := by
  have hnot :
      (x, y) ∉ distLT (X := X) D.packingRadius :=
    (Classical.choose_spec D.uniformlyDiscrete).2 hx hy hne
  simpa [distLT] using (le_of_not_gt hnot)

lemma dist_pos_of_ne {D : DeloneSet X} {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    0 < dist x y :=
  lt_of_lt_of_le D.packingRadius_pos <| D.le_dist_of_mem_ne hx hy hne

/-- For a Delone set `D`, there exists a radius `r > 0` such that, for any
`z ∈ D`, the open ball `ball z r` contains at most one point of the Delone set. -/
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
    simpa [f.dist_eq, distLT] using D.le_dist_of_mem_ne hx hx' (by grind)
  relativelyDense := by
    obtain ⟨R, hR, hcov⟩ := D.relativelyDense
    refine ⟨R, hR, ?_⟩
    intro y; obtain ⟨x, hx, hxy⟩ := hcov (f.symm y)
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have hthis : dist (f.symm y) x < R := by
      simpa [distLT] using hxy
    have hdist : dist y (f x) = dist (f.symm y) x := by
      simpa using (f.dist_eq (f.symm y) x)
    simpa [distLT, hdist] using hthis
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
