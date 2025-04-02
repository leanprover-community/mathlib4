/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Order.Disjointed
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Uniform approximation by locally constant functions

We show that if `X` is a profinite space, and `V` is a uniform space, then any continuous function
`X → V` can be uniformly approximated by locally constant functions.
-/

open UniformSpace Set

open TopologicalSpace (Opens Clopens IsOpenCover)

open scoped Uniformity Function

namespace ContinuousMap

variable {X Y V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [UniformSpace V] (f : C(X, V)) {S : Set (V × V)}

/--
For any continuous function on `X` and `S ∈ 𝓤 V`, there exists a finite cover of `X` by
pairwise-disjoint nonempty clopens, on each of which `f` varies within `S`.
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_uniformity (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧
    (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S) ∧ (univ : Set X) ⊆ ⋃ i, ↑(D i) ∧
    Pairwise (Disjoint on D) := by
  -- Find a neighbourhood of each point on which `f` varies within `S`
  have step1 (x) : ∃ U : Opens X, x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U, (f y, f z) ∈ S := by
    obtain ⟨R, hR, hR', hRS⟩ := comp_symm_of_uniformity hS
    obtain ⟨U, hUB, hUo, hUx⟩ := mem_nhds_iff.mp <|  (f.continuousAt x).preimage_mem_nhds
      <| UniformSpace.ball_mem_nhds _ hR
    exact ⟨⟨U, hUo⟩, hUx, fun y hy z hz ↦ hRS <| prodMk_mem_compRel (hR' <| hUB hy) (hUB hz)⟩
  choose U hUx hUS using step1
  have hUc : IsOpenCover U := by ext x; simpa using ⟨x, hUx x⟩
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j ↦ (hW₁ j).1, fun j y hy z hz ↦ ?_, hW₂, hW₃⟩
  exact match (hW₁ j).2 with | ⟨i, hi⟩ => hUS i y (hi hy) z (hi hz)

/--
Any continuous function from a profinite space to a uniform space can be uniformly approximated
by a function factoring through `Fin n`, for some `n`.
-/
lemma exists_fin_comp_of_mem_uniformity (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : X → Fin n) (h : Fin n → V), Continuous g ∧ ∀ x, (f x, h (g x)) ∈ S := by
  classical
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_uniformity f hS
  have h_uniq (x) : ∃! i, x ∈ E i := by
    refine match Set.mem_iUnion.mp (hEuniv <| mem_univ x) with
      | ⟨i, hi⟩ => ⟨i, hi, fun j hj ↦ hEdis.eq ?_⟩
    simpa [← Clopens.coe_disjoint, not_disjoint_iff] using ⟨x, hj, hi⟩
  choose g hg hg' using h_uniq -- for each `x`, `g x` is the unique `i` such that `x ∈ E i`
  have h_ex (i) : ∃ x, x ∈ E i := by
    simpa [← SetLike.coe_set_eq, ← nonempty_iff_ne_empty] using hEne i
  choose r hr using h_ex -- for each `i`, choose an `r i ∈ E i`
  refine ⟨n, g, f ∘ r, continuous_discrete_rng.mpr fun j ↦ ?_, fun x ↦ (hES _) _ (hg _) _ (hr _)⟩
  convert (E j).isOpen
  exact Set.ext fun x ↦ ⟨fun hj ↦ hj ▸ hg x, fun hx ↦ (hg' _ _ hx).symm⟩

/--
If `f` is a continuous map from a profinite space to a uniform space with a group structure, then
we can uniformly approximate `f` by finite products of indicator functions of clopen sets.
-/
@[to_additive "If `f` is a continuous map from a profinite space to a uniform space with an
additive group structure, then we can uniformly approximate `f` by finite sums of indicator
functions of clopen sets."]
lemma exists_sum_const_mulIndicator_approx [CommMonoid V] (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (U : Fin n → Clopens X) (v : Fin n → V),
    ∀ x, (f x, ∏ n, mulIndicator (U n) (fun _ ↦ v n) x) ∈ S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_fin_comp_of_mem_uniformity f hS
  refine ⟨n, fun i ↦ ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x ↦ ?_⟩
  convert hgh x
  exact (Fintype.prod_eq_single _ fun i hi ↦ mulIndicator_of_not_mem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

variable {R Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [TopologicalSpace R] [MonoidWithZero R]

/-- A continuous function on `X × Y` can be uniformly approximated by sums of functions of the
form `f x • g y`. -/
lemma exists_sum_smul_approx [AddCommGroup V] [IsUniformAddGroup V] [MulActionWithZero R V]
    (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x • h i y) ∈ S := by
  have hS' : {(f, g) | ∀ y, (f y, g y) ∈ S} ∈ 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_sum_const_indicator_approx f.curry hS'
  refine ⟨n, fun i ↦ ⟨_, (U i).isClopen.continuous_indicator <| continuous_const (y := 1)⟩,
    v, fun x y ↦ ?_⟩
  convert hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x ∈ U i <;> simp [hi]

/-- A continuous function on `X × Y` can be uniformly approximated by sums of functions of the form
`f x * g y`. -/
lemma exists_sum_mul_approx (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) [Ring V] [IsUniformAddGroup V]:
    ∃ (n : ℕ) (g : Fin n → C(X, V)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x * h i y) ∈ S :=
  exists_sum_smul_approx f hS

end ContinuousMap
