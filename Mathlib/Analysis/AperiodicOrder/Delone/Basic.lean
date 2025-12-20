/-
Copyright (c) 2025 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.MetricSeparated

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **uniformly discrete**: there exists `r > 0` such that distinct points of `D`
  have distance **strictly greater** than `r`;
* **relatively dense**: there exists `R > 0` such that every point of `X`
  lies **strictly within distance `R`** of some point of `D`.

These notions are phrased in terms of metric entourages so that the theory
fits naturally into the uniformity framework.

Delone sets arise throughout discrete geometry, crystallography,
aperiodic order, and tiling theory.

## Main definitions

* `Metric.IsUniformlyDiscreteWith D r`
* `Metric.IsRelativelyDenseWith D R`
* `Metric.IsUniformlyDiscrete D`, `Metric.IsRelativelyDense D`
* `Delone.DeloneSet X`

## Basic properties

* Canonical radii: `DeloneSet.packingRadius`, `DeloneSet.coveringRadius`.
* Bounds: `packingRadius_lt_dist_of_mem_ne`, `dist_lt_coveringRadius`.
* `subset_ball_singleton`: small balls contain at most one point of a Delone set.
* `map`: Delone sets are preserved by isometries.

## TODO

`distLT` is a temporary entourage. When mathlib includes canonical quantitative
entourages for metric spaces, replace all `distLT` with that construction.
-/

@[expose] public section

open scoped Uniformity ENNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Metric

/-- The metric `ε`-entourage as a relation (a set of pairs). -/
def distLT (ε : ℝ) : SetRel X X := {p : X × X | dist p.1 p.2 < ε}

/-- If `ε > 0`, then the metric entourage `distLT ε` belongs to the uniformity. -/
lemma distLT_mem_uniformity {ε : ℝ} (hε : 0 < ε) : distLT ε ∈ 𝓤 X :=
  (mem_uniformity_dist).2 ⟨ε, hε, fun _ _ a₁ ↦ a₁⟩

/-- `D` is uniformly discrete with radius `r > 0` if every two distinct
points of `D` have distance strictly greater than `r`. -/
def IsUniformlyDiscreteWith (D : Set X) (r : ℝ) : Prop :=
  0 < r ∧ IsSeparated (ENNReal.ofReal r) D

/-- `D` is relatively dense with radius `R > 0` if every point of the space
lies strictly within distance `R` of some point of `D`. -/
def IsRelativelyDenseWith (D : Set X) (R : ℝ) : Prop :=
  0 < R ∧ ∀ x : X, ∃ y ∈ D, (x, y) ∈ distLT R

/-- `D` is uniformly discrete if it has some positive separation radius. -/
def IsUniformlyDiscrete (D : Set X) : Prop :=
  ∃ r : ℝ, IsUniformlyDiscreteWith D r

/-- `D` is relatively dense if it has some finite covering radius. -/
def IsRelativelyDense (D : Set X) : Prop :=
  ∃ R : ℝ, IsRelativelyDenseWith D R

/-- Monotonicity of uniform discreteness. -/
lemma IsUniformlyDiscreteWith.mono {D E : Set X} {r : ℝ} (hDE : D ⊆ E) :
    IsUniformlyDiscreteWith E r → IsUniformlyDiscreteWith D r := by
  rintro ⟨hr, hsep⟩
  refine ⟨hr, ?_⟩
  exact IsSeparated.subset hDE hsep

/-- Monotonicity of relative denseness. -/
lemma IsRelativelyDenseWith.mono {D E : Set X} {R : ℝ} (hDE : D ⊆ E) :
    IsRelativelyDenseWith D R → IsRelativelyDenseWith E R := by
  rintro ⟨hR, hcov⟩
  refine ⟨hR, fun x ↦ ?_⟩
  obtain ⟨y, hyD, hxy⟩ := hcov x
  exact ⟨y, hDE hyD, hxy⟩

/-- Relative denseness implies the thickening covers the whole space. -/
lemma IsRelativelyDenseWith.cthickening_eq_univ {X : Type*} [MetricSpace X] {D : Set X} {R : ℝ} :
    IsRelativelyDenseWith D R → cthickening R D = Set.univ := by
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
  hr : IsUniformlyDiscreteWith carrier r
  /-- A radius witnessing relative denseness. -/
  R : ℝ
  hR : IsRelativelyDenseWith carrier R

attribute [simp] DeloneSet.carrier

namespace DeloneSet

/-- The packing radius. -/
def packingRadius (D : DeloneSet X) : ℝ := D.r

lemma packingRadius_pos (D : DeloneSet X) : 0 < D.packingRadius := D.hr.1

/-- The covering radius. -/
def coveringRadius (D : DeloneSet X) : ℝ := D.R

lemma coveringRadius_pos (D : DeloneSet X) : 0 < D.coveringRadius := D.hR.1

/-- A Delone set is nonempty when the space is nonempty. -/
lemma nonempty [Nonempty X] (D : DeloneSet X) : Nonempty D.carrier := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hyD, _⟩ := D.hR.2 x
  exact ⟨y, hyD⟩

/-- Distinct points of `D` are separated by more than the `packingRadius`. -/
lemma packingRadius_lt_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) (hne : x ≠ y) :
    D.packingRadius < dist x y := by
  have hsep : ENNReal.ofReal D.r < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.hr.2 hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep

/-- Every point of the space lies strictly within the `coveringRadius` of `D`. -/
lemma dist_lt_coveringRadius (D : DeloneSet X) (x : X) :
    ∃ y ∈ D.carrier, dist x y < D.coveringRadius := by
  obtain ⟨y, hy, hxy⟩ := D.hR.2 x
  exact Filter.frequently_principal.mp fun a ↦ a hy hxy

/-- There exists a radius `r > 0` such that any ball of radius `r`
centered at a point of `D` contains at most one point of `D`. -/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ {x y z}, x ∈ D.carrier → y ∈ D.carrier → z ∈ D.carrier →
      x ∈ ball z r → y ∈ ball z r → x = y := by
  refine ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, ?_⟩
  intro x y z hx hy hz hxz hyz
  by_contra hne
  have hsum : dist x z + dist z y < D.packingRadius :=
    by simpa [add_halves, dist_comm] using
      add_lt_add (mem_ball.mp hxz) (mem_ball.mp hyz)
  have hxy_lt : dist x y < D.packingRadius :=
    lt_of_le_of_lt (dist_triangle x z y) hsum
  have hsep := D.packingRadius_lt_dist_of_mem_ne hx hy hne
  grind

/-- Isometries preserve Delone sets. -/
def map (f : X ≃ᵢ Y) (D : DeloneSet X) : DeloneSet Y := {
  carrier := f '' D.carrier
  r := D.r
  hr := by
    refine ⟨D.hr.1, ?_⟩
    rintro y ⟨x,  hx,  rfl⟩ y' ⟨x', hx', rfl⟩ hne
    have hsep : ENNReal.ofReal D.r < edist x x' := D.hr.2 hx hx' (by grind)
    simpa [f.edist_eq] using hsep
  R := D.R
  hR := by
    refine ⟨D.hR.1, fun y ↦ ?_⟩
    obtain ⟨x, hx, hxR⟩ := D.hR.2 (f.symm y)
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have hxR' : dist (f.symm y) x < D.R := by
      simpa [Metric.distLT] using hxR
    have hdist : dist y (f x) = dist (f.symm y) x := by
      simpa using f.dist_eq (f.symm y) x
    simpa [Metric.distLT, hdist] using hxR'
}

/-- Extensionality for Delone sets. -/
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
