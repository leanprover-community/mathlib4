/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Separation.DisjointCover

/-!
# Uniform approximation by products

We show that if `X, Y` are compact Hausdorff spaces with `X` profinite, then any continuous function
on `X × Y` valued in a ring (with a uniform structure) can be uniformly approximated by finite
sums of functions of the form `f x * g y`.
-/

open UniformSpace

open scoped Uniformity

namespace ContinuousMap

variable {X Y R V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y]
  [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] {S : Set (V × V)}

/-- A continuous function on `X × Y`, taking values in an `R`-module with a uniform structure,
can be uniformly approximated by sums of functions of the form `(x, y) ↦ f x • g y`.

Note that no continuity properties are assumed either for multiplication on `R`, or for the scalar
multiplication of `R` on `V`. -/
lemma exists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R]
    [MonoidWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x • h i y) ∈ S := by
  have hS' : {(f, g) | ∀ y, (f y, g y) ∈ S} ∈ 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
  refine ⟨n, fun i ↦ ⟨_, (U i).isClopen.continuous_indicator <| continuous_const (y := 1)⟩,
    v, fun x y ↦ ?_⟩
  convert hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x ∈ U i <;> simp [hi]

/-- A continuous function on `X × Y`, taking values in a ring `R` equipped with a uniformity
compatible with addition, can be uniformly approximated by sums of functions of the form
`(x, y) ↦ f x * g y`.

Note that no assumption is needed relating the multiplication on `R` to the uniformity. -/
lemma exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R]
    [IsUniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S ∈ 𝓤 R) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, R)),
    ∀ x y, (f (x, y), ∑ i, g i x * h i y) ∈ S :=
  exists_finite_sum_smul_approximation_of_mem_uniformity f hS

end ContinuousMap
