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

* `UniformlyDiscreteWith D r`
  A set is uniformly discrete *with radius `r`*.

* `RelativelyDenseWith D R`
  A set is relatively dense *with radius `R`*.

* `IsUniformlyDiscrete D`, `IsRelativelyDense D`
  Existential versions.

* `DeloneSet X`
  Bundles a set together with explicit radii witnessing uniform discreteness
  and relative denseness.

## Basic properties

* Canonical radii: `DeloneSet.packingRadius`, `DeloneSet.coveringRadius`.
* Bounds: `dist_le_coveringRadius`, `le_dist_of_mem_ne`.
* `dist_pos_of_ne`: distinct points lie at positive distance.
* `subset_ball_singleton`: small balls contain at most one point of a Delone set.
* `map`: Delone sets are preserved by isometries.

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
def distLT (ε : ℝ) : SetRel X X := {p : X × X | dist p.1 p.2 < ε}

/-- If `ε > 0`, then the metric entourage `distLT ε` belongs to the uniformity. -/
lemma distLT_mem_uniformity {ε : ℝ} (hε : 0 < ε) : distLT ε ∈ 𝓤 X := by
  exact (mem_uniformity_dist).2 ⟨ε, hε, fun ⦃a b⦄ a₁ ↦ a₁⟩

/-- A set `D` is uniformly discrete *with radius `r`* if
distinct points of `D` are separated by the entourage `distLT r`. -/
def UniformlyDiscreteWith (D : Set X) (r : ℝ) : Prop :=
  0 < r ∧ ∀ ⦃x y⦄, x ∈ D → y ∈ D → x ≠ y → (x, y) ∉ distLT r

/-- A set `D` is relatively dense *with radius `R`* if
every point of `X` is related to `D` by `distLT R`. -/
def RelativelyDenseWith (D : Set X) (R : ℝ) : Prop :=
  0 < R ∧ ∀ x : X, ∃ y ∈ D, (x, y) ∈ distLT R

/-- A set is uniformly discrete if it is uniformly discrete with some radius. -/
def IsUniformlyDiscrete (D : Set X) : Prop :=
  ∃ r : ℝ, UniformlyDiscreteWith D r

/-- A set is relatively dense if it is relatively dense with some radius. -/
def IsRelativelyDense (D : Set X) : Prop :=
  ∃ R : ℝ, RelativelyDenseWith D R

/-- Monotonicity of uniform discreteness. -/
lemma UniformlyDiscreteWith.mono {D E : Set X} {r : ℝ} (hDE : D ⊆ E) :
    UniformlyDiscreteWith E r → UniformlyDiscreteWith D r := by
  rintro ⟨hr, h⟩
  exact ⟨hr, fun x y hx hy hne ↦ h (hDE hx) (hDE hy) hne⟩

/-- Monotonicity of relative denseness. -/
lemma RelativelyDenseWith.mono {D E : Set X} {R : ℝ} (hDE : D ⊆ E) :
    RelativelyDenseWith D R → RelativelyDenseWith E R := by
  rintro ⟨hR, hcov⟩
  refine ⟨hR, fun x ↦ ?_⟩
  obtain ⟨y, hyD, hxy⟩ := hcov x
  exact ⟨y, hDE hyD, hxy⟩

/-- Relative denseness implies the thickening covers the whole space. -/
lemma RelativelyDenseWith.cthickening_eq_univ {X : Type*} [MetricSpace X] {D : Set X} {R : ℝ} :
    RelativelyDenseWith D R → cthickening R D = Set.univ := by
  rintro ⟨hRpos, hcov⟩
  ext x; constructor
  · intro _; trivial
  · intro _; obtain ⟨y, hyD, hxy⟩ := hcov x
    have : dist x y ≤ R := by
      simpa [distLT] using (le_of_lt hxy)
    exact mem_cthickening_of_dist_le x y R D hyD this

end Metric

namespace Delone

open Metric

/-- A **Delone set** consists of a set together with explicit radii witnessing
uniform discreteness and relative denseness. -/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set. -/
  carrier : Set X
  /-- A radius witnessing uniform discreteness. -/
  r : ℝ
  hr : UniformlyDiscreteWith carrier r
  /-- A radius witnessing relative denseness. -/
  R : ℝ
  hR : RelativelyDenseWith carrier R

attribute [simp] DeloneSet.carrier

namespace DeloneSet

/-- The packing radius. -/
def packingRadius (D : DeloneSet X) : ℝ := D.r

lemma packingRadius_pos (D : DeloneSet X) : 0 < D.packingRadius := D.hr.1

/-- The covering radius. -/
def coveringRadius (D : DeloneSet X) : ℝ := D.R

lemma coveringRadius_pos (D : DeloneSet X) : 0 < D.coveringRadius := D.hR.1

/-- A Delone set is nonempty. -/
lemma nonempty [Nonempty X] (D : DeloneSet X) : Nonempty D.carrier := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hyD, _⟩ := D.hR.2 x
  exact ⟨y, hyD⟩

/-- Every point is within `coveringRadius` of the Delone set. -/
lemma dist_le_coveringRadius (D : DeloneSet X) (x : X) :
    ∃ y ∈ D.carrier, dist x y ≤ D.coveringRadius := by
  obtain ⟨y, hy, hxy⟩ := D.hR.2 x
  exact ⟨y, hy, le_of_lt hxy⟩

/-- Any two distinct points of a Delone set are at distance at least `packingRadius`. -/
lemma le_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    D.packingRadius ≤ dist x y :=
  not_lt.mp <| D.hr.2 hx hy hne

/-- Distinct points in a Delone set lie at positive distance. -/
lemma dist_pos_of_ne {D : DeloneSet X} {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    0 < dist x y :=
lt_of_lt_of_le D.packingRadius_pos <| D.le_dist_of_mem_ne hx hy hne

/-- For a Delone set `D`, there exists `r > 0` such that
for any `z ∈ D`, the ball `ball z r` contains at most one point of `D`. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ ⦃x y z⦄, x ∈ D.carrier → y ∈ D.carrier → z ∈ D.carrier →
      x ∈ ball z r → y ∈ ball z r → x = y := by
  refine ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, ?_⟩
  intro x y z hx hy hz hxz hyz
  by_contra hne
  have hlt : dist x y < D.packingRadius := by
    have hsum_lt :
        dist x z + dist z y < D.packingRadius := by
      simpa [add_halves] using
        (add_lt_add hxz <| mem_ball'.mp hyz)
    exact lt_of_le_of_lt (dist_triangle x z y) hsum_lt
  exact (not_lt_of_ge <| D.le_dist_of_mem_ne hx hy hne) hlt

/-- Isometries preserve Delone sets. -/
def map (f : X ≃ᵢ Y) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  r := D.r
  hr := by
    refine ⟨D.hr.1, ?_⟩
    rintro x y ⟨x₀, hx₀, rfl⟩ ⟨y₀, hy₀, rfl⟩ hne
    have : (x₀, y₀) ∉ distLT D.r := D.hr.2 hx₀ hy₀ ?_
    · simpa [distLT, f.dist_eq] using this
    · grind
  R := D.R
  hR := by
    refine ⟨D.hR.1, fun y ↦ ?_⟩
    obtain ⟨x, hx, hxR⟩ := D.hR.2 (f.symm y)
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have hxR' : dist (f.symm y) x < D.R := by
      simpa [distLT] using hxR
    have hdist : dist y (f x) = dist (f.symm y) x := by
      simpa using (f.dist_eq (f.symm y) x)
    simpa [distLT, hdist] using hxR'
}

/-- Extensionality for `DeloneSet`: equality of carrier and radii. -/
@[ext] lemma ext {D E : DeloneSet X} (h_carrier : D.carrier = E.carrier)
    (h_r : D.r = E.r) (h_R : D.R = E.R) : D = E := by
  cases D; cases E; cases h_carrier; cases h_r; cases h_R; rfl

lemma map_id (D : DeloneSet X) : D.map (IsometryEquiv.refl X) = D := by
  apply ext
  · ext x; constructor
    · rintro ⟨y, hyD, rfl⟩; simpa using hyD
    · intro hx; exact ⟨x, hx, rfl⟩
  · rfl
  · rfl

lemma map_comp {Z : Type*} [MetricSpace Z]
    (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.map (f.trans g) = (D.map f).map g := by
  apply ext
  · ext z; constructor
    · rintro ⟨x, hxD, rfl⟩
      exact ⟨f x, ⟨x, hxD, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hxD, rfl⟩, rfl⟩
      exact ⟨x, hxD, rfl⟩
  · rfl
  · rfl

lemma map_symm (D : DeloneSet X) (f : X ≃ᵢ Y) :
    (D.map f).map f.symm = D := by
  apply ext
  · ext x; constructor
    · rintro ⟨y, ⟨x₀, hx₀D, rfl⟩, rfl⟩; simpa
    · intro hx; exact ⟨f x, ⟨x, hx, rfl⟩, by simp⟩
  · rfl
  · rfl

end DeloneSet

end Delone
