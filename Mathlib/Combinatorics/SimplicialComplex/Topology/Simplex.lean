/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Standard simplices

For a finite vertex set `A : Finset U`, the **standard simplex** `Simplex A` consists of
barycentric coordinate functions `w : U → ℝ` that are supported on `A`, sum to `1` over `A`,
and take values in `[0, 1]`. This file develops the basic API for standard simplices, including
their topology, support, and the canonical “extend” and “shrink” maps.

This file is independent of the theory of simplicial complexes; it is intended for use in
constructions such as geometric realisation.

## Main definitions

* `Simplex A` : the standard simplex on the finite set `A`.
* `Simplex.supportFinset` : the vertices with non-zero barycentric weight.
* `Simplex.simplexEmbedding` : extend a simplex on `A` to any superset `B ⊇ A`.
* `Simplex.shrink` : restrict a simplex to its minimal support.

## Main results

* `Simplex.mem_supportFinset` : `v ∈ supportFinset p ↔ p v ≠ 0`.
* `Simplex.simplexEmbedding_apply` :
  the weight function is unchanged by `simplexEmbedding`. (`[simp]`)
* `Simplex.simplexEmbedding_shrink` :
  `shrink` is a left inverse to `simplexEmbedding` along the inclusion
  `supportFinset p ⊆ A`. (`[simp]`)
* `Simplex.supportFinset_simplexEmbedding` :
  the support is unchanged by `simplexEmbedding`. (`[simp]`)
* `Simplex.simplexEmbedding_continuous` :
  `simplexEmbedding` is continuous. (`[simp]`)

## Implementation notes

* We treat `Simplex A` as a structure with a coercion to `U → ℝ`. The topology on `Simplex A`
  is the topology induced by this coercion from the product topology on `U → ℝ`.
* The “extend” map is defined by reusing the same weight function and checking the axioms
  on the larger face; the “shrink” map filters down to the minimal support and reuses weights.

## Tags

simplex, barycentric coordinates, convex hull
-/

universe u

variable {U : Type u} [DecidableEq U]

/-- A point in the standard simplex on a finite vertex set `A`, defined by its
barycentric coordinates. -/
@[ext] structure Simplex (A : Finset U) where
  /-- The barycentric coordinate (weight) assigned to each vertex `v : U`.
  It is zero outside the support `A`. -/
  weight : U → ℝ
  /-- Outside the face `A`, the coordinates vanish. -/
  support_subset : ∀ ⦃v⦄, v ∉ A → weight v = 0
  /-- The barycentric coordinates sum to `1` over the face `A`. -/
  sum_eq_one : (∑ v ∈ A, weight v) = 1
  /-- Each coordinate lies in the closed interval `[0, 1]`. -/
  range_mem_Icc : ∀ v, weight v ∈ Set.Icc (0 : ℝ) 1

namespace Simplex

variable {A : Finset U}

/-- Coerces a `Simplex` to its underlying weight function. -/
instance : CoeFun (Simplex A) (fun _ ↦ U → ℝ) := ⟨Simplex.weight⟩

/-- The topology on a simplex is the subspace topology from the product topology on `U → ℝ`. -/
instance : TopologicalSpace (Simplex A) :=
  TopologicalSpace.induced (fun x ↦ (x : U → ℝ)) inferInstance

/-- The finite support of a point `p : Simplex A` (the vertices with non-zero weight). -/
noncomputable def supportFinset (p : Simplex A) : Finset U :=
  A.filter (fun v ↦ p v ≠ 0)

/-- A vertex `v` is in the support of `p` if and only if its weight `p v` is non-zero. -/
@[simp] lemma mem_supportFinset (p : Simplex A) {v : U} :
    v ∈ supportFinset p ↔ p v ≠ 0 := by
  by_cases hv : v ∈ A
  · simp [supportFinset, hv]
  · have : p v = 0 := p.support_subset hv
    simp [supportFinset, hv, this]

/-! ### Extension and shrink maps -/

section Extension

variable {A B : Finset U}

/-- Extends a simplex on `A` to a simplex on a superset `B ⊇ A`. -/
noncomputable def simplexEmbedding (hAB : A ⊆ B) :
    Simplex (U := U) A → Simplex (U := U) B :=
  fun p =>
  { weight := p
    support_subset := by
      intro v hvB
      have : v ∉ A := fun h ↦ hvB (hAB h)
      exact p.support_subset this
    sum_eq_one := by
      have hvanish :
          ∀ v ∈ B, v ∉ A → (p : U → ℝ) v = (0 : ℝ) := by
        intro v _ hvA; exact p.support_subset hvA
      have hsum : (∑ v ∈ B, p v) = ∑ v ∈ A, p v :=
        (Finset.sum_subset hAB hvanish).symm
      simpa [hsum] using p.sum_eq_one
    range_mem_Icc := p.range_mem_Icc }

omit [DecidableEq U] in
/-- The weight function of a simplex is unchanged by `simplexEmbedding`. -/
@[simp] lemma simplexEmbedding_apply {hAB : A ⊆ B}
    (p : Simplex A) {v : U} :
    (simplexEmbedding hAB p : U → ℝ) v = p v :=
  rfl

end Extension

section Shrink

variable {A : Finset U}

/-- Restricts a simplex to its minimal support. -/
noncomputable def shrink (p : Simplex A) :
    Simplex (supportFinset p) := by
  set A' := supportFinset p with hA'
  refine
  { weight := fun v ↦ p v
    support_subset := ?_
    sum_eq_one := ?_
    range_mem_Icc := p.range_mem_Icc }
  · intro v hv
    have h₁ : v ∈ A' ↔ p v ≠ 0 := mem_supportFinset p
    have : p v = 0 := by
      by_contra hne; exact hv ((h₁.mpr hne))
    simp [this]
  · have hsub : A' ⊆ A := by
      intro v hv; exact (Finset.mem_filter.1 hv).1
    have hvanish :
        ∀ v ∈ A, v ∉ A' → p v = 0 := by
      intro v _ hv
      have h₁ : v ∈ A' ↔ p v ≠ 0 := mem_supportFinset p
      by_contra hne; exact hv ((h₁.mpr hne))
    have hsum : (∑ v ∈ A', p v) = (∑ v ∈ A, p v) :=
      Finset.sum_subset hsub hvanish
    have : (∑ v ∈ A', p v) = 1 := by
      simpa [hsum] using p.sum_eq_one
    simpa [hA'] using this

/-- Extending a shrunk simplex back to the original vertex set recovers the original point. -/
@[simp] lemma simplexEmbedding_shrink (p : Simplex (U := U) A) :
    simplexEmbedding (U := U)
      (A := supportFinset p) (B := A)
      (by
        intro v hv; exact (Finset.mem_filter.1 hv).1)
      (shrink (U := U) p) = p := by
  ext v
  by_cases hv : v ∈ supportFinset p
  · simp [simplexEmbedding_apply, shrink]
  · have hpv0 : p v = 0 := by
      have h₁ : v ∈ supportFinset p ↔ p v ≠ 0 := mem_supportFinset p
      have : p v ≠ 0 → False := by
        intro hne; exact hv ((h₁.mpr hne))
      by_contra hne; exact this hne
    simp [simplexEmbedding_apply, shrink, hpv0]

end Shrink

omit [DecidableEq U] in
/-- The `simplexEmbedding` map is continuous. -/
@[simp] lemma simplexEmbedding_continuous {A B : Finset U} (hAB : A ⊆ B) :
    Continuous (simplexEmbedding hAB) := by
  -- prove continuity into the ambient product space `U → ℝ`
  have h₁ :
      Continuous fun p : Simplex (U := U) A ↦
        ((simplexEmbedding (U := U) hAB p : Simplex (U := U) B) : U → ℝ) := by
    simpa [simplexEmbedding_apply] using
      (continuous_induced_dom :
        Continuous fun p : Simplex (U := U) A ↦ (p : U → ℝ))
  -- the target `Simplex B` has the subspace topology, so this suffices
  simpa using (continuous_induced_rng.2 h₁)

/-- The support of a simplex is unchanged after embedding it in a larger simplex. -/
@[simp] lemma supportFinset_simplexEmbedding {A B : Finset U}
    (hAB : A ⊆ B) (p : Simplex (U := U) A) :
    supportFinset (simplexEmbedding (U := U) hAB p) = supportFinset p := by
  ext v; simp [simplexEmbedding_apply]

end Simplex
