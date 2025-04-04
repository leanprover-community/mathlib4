/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Order.Disjointed
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.OfCompactT2

/-!
# Approximation by locally constant functions

We show that if `X` is a profinite space, then any continuous function from `X` to a T2 space
can be uniformly approximated by locally constant functions.
-/

open Set

open TopologicalSpace (Opens Clopens IsOpenCover)

open scoped Function Uniformity

namespace ContinuousMap

variable {X V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace V] [T2Space V] (f : C(X, V)) {S : Set (V × V)}

-- this lemma is private since it is immediately superseded by the next lemma
private lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_compact [CompactSpace V]
    (hS : S ∈ nhdsSet (.diagonal V)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧
    (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S) ∧ (univ : Set X) ⊆ ⋃ i, ↑(D i) ∧
    Pairwise (Disjoint on D) := by
  letI : UniformSpace V := uniformSpaceOfCompactT2
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
For any continuous function `X → V`, with `X` profinite and `V` Hausdorff, and `S` a
neighbourhood of the diagonal in `V × V`, there exists a finite cover of `X` by pairwise-disjoint
nonempty clopens, on each of which `f` varies within `S`.
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (.diagonal V)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧
    (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S) ∧ (univ : Set X) ⊆ ⋃ i, ↑(D i) ∧
    Pairwise (Disjoint on D) := by
  -- reduce to compact case by considering range of `f`
  let V' := Set.range f
  haveI : CompactSpace V' := isCompact_iff_compactSpace.mp <| isCompact_range (map_continuous f)
  let g : C(X, V') :=
  { toFun := V'.codRestrict f Set.mem_range_self, continuous_toFun := by fun_prop }
  suffices S.preimage (Prod.map (↑) (↑)) ∈ nhdsSet (.diagonal V') from
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_compact g this
  rw [mem_nhdsSet_iff_forall] at hS ⊢
  refine fun ⟨x, y⟩ hxy ↦ ContinuousAt.preimage_mem_nhds ?_ (hS ⟨x, y⟩ (Subtype.val_inj.mpr hxy))
  exact continuousAt_subtype_val.prodMap continuousAt_subtype_val

/--
Any continuous function from a profinite space to T2 space can be approximated by a function
factoring through `Fin n`, for some `n`.
-/
lemma exists_finite_approximation_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (.diagonal V)) :
    ∃ (n : ℕ) (g : X → Fin n) (h : Fin n → V), Continuous g ∧ ∀ x, (f x, h (g x)) ∈ S := by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
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

(Note no compatibility is assumed between the group structure on `V` and the uniform structure.)
-/
@[to_additive "If `f` is a continuous map from a profinite space to a uniform space with an
additive group structure, then we can uniformly approximate `f` by finite sums of indicator
functions of clopen sets.

(Note no compatibility is assumed between the group structure on `V` and the uniform structure.)"]
lemma exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal [CommMonoid V]
    (hS : S ∈ nhdsSet (.diagonal V)) :
    ∃ (n : ℕ) (U : Fin n → Clopens X) (v : Fin n → V),
    ∀ x, (f x, ∏ n, mulIndicator (U n) (fun _ ↦ v n) x) ∈ S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i ↦ ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x ↦ ?_⟩
  convert hgh x
  exact (Fintype.prod_eq_single _ fun i hi ↦ mulIndicator_of_not_mem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

/-!
## Functions on product spaces
-/
section product
variable {R Y V : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] [T2Space V] {S : Set (V × V)}

/-- A continuous function on `X × Y` can be uniformly approximated by sums of functions of the
form `f x • g y`. -/
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

/-- A continuous function on `X × Y` can be uniformly approximated by sums of functions of the form
`f x * g y`. -/
lemma exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R]
    [IsUniformAddGroup R] [T2Space R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S ∈ 𝓤 R) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, R)),
    ∀ x y, (f (x, y), ∑ i, g i x * h i y) ∈ S :=
  exists_finite_sum_smul_approximation_of_mem_uniformity f hS

end product

end ContinuousMap
