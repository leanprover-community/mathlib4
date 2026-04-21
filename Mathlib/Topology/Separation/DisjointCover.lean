/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Disjointed
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.OpenCover

/-!
# Disjoint covers of profinite spaces

We prove various results about covering profinite spaces by disjoint clopens, including

* `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`: any open cover of a
  profinite space can be refined to a finite cover by pairwise disjoint nonempty clopens.

* `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`: if `f : X → V` is continuous
  with `X` profinite, and `S` is a neighbourhood of the diagonal in `V × V`, then `f` can be
  `S`-approximated by a function factoring through `Fin n` for some `n`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Set TopologicalSpace

open scoped Function Finset Topology

namespace TopologicalSpace.IsOpenCover

variable {ι X : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X] {U : ι → Opens X}

/-- Any open cover of a profinite space can be refined to a finite cover by clopens. -/
lemma exists_finite_clopen_cover (hU : IsOpenCover U) : ∃ (n : ℕ) (V : Fin n → Clopens X),
    (∀ j, ∃ i, (V j : Set X) ⊆ U i) ∧ univ ⊆ ⋃ j, (V j : Set X) := by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x ↦ compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compactness to extract a finite subset of the `V`s which covers `X`.
  obtain ⟨t, ht⟩ : ∃ t, univ ⊆ ⋃ i ∈ t, V i :=
    isCompact_univ.elim_finite_subcover V (fun x ↦ (hV x).2) (fun x _ ↦ mem_iUnion.mpr ⟨x, hVx x⟩)
  -- Biject it noncanonically with `Fin n` for some `n`.
  refine ⟨_, fun j ↦ ⟨_, hV (t.equivFin.symm j)⟩, fun j ↦ ⟨_, hVU _⟩, fun x hx ↦ ?_⟩
  obtain ⟨m, hm, hm'⟩ := mem_iUnion₂.mp (ht hx)
  exact Set.mem_iUnion_of_mem (t.equivFin ⟨m, hm⟩) (by simpa)

/-- Any open cover of a profinite space can be refined to a finite cover by pairwise disjoint
nonempty clopens. -/
lemma exists_finite_nonempty_disjoint_clopen_cover (hU : IsOpenCover U) :
    ∃ (n : ℕ) (W : Fin n → Clopens X), (∀ j, W j ≠ ⊥ ∧ ∃ i, (W j : Set X) ⊆ U i)
    ∧ (univ : Set X) ⊆ ⋃ j, ↑(W j) ∧ Pairwise (Disjoint on W) := by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j ≠ ⊥}
  refine ⟨#t, fun k ↦ W (t.equivFin.symm k), fun k ↦ ⟨?_, ?_⟩, fun x hx ↦ ?_, ?_⟩
  · exact (Finset.mem_filter.mp (t.equivFin.symm k).2).2
  · exact match hVle (t.equivFin.symm k) with | ⟨i, hi⟩ => ⟨i, subset_trans (hWle _) hi⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp <| (hWun ▸ hVun) hx
    have : W j ≠ ⊥ := by simpa [← SetLike.coe_ne_coe, ← Set.nonempty_iff_ne_empty] using ⟨x, hj⟩
    exact mem_iUnion.mpr ⟨t.equivFin ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩⟩, by simpa⟩
  · exact hWd.comp_of_injective <| Subtype.val_injective.comp t.equivFin.symm.injective

end TopologicalSpace.IsOpenCover

namespace TopologicalSpace
variable {X : Type*} [TopologicalSpace X] {S : Set (X × X)}

/-- If `S` is any neighbourhood of the diagonal in a topological space `X`, any point of `X` has an
open neighbourhood `U` such that `U ×ˢ U ⊆ S`. -/
lemma exists_open_prod_subset_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal X)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ S := by
  have : S ∈ 𝓝 (x, x) := mem_nhdsSet_iff_forall.mp hS _ rfl
  obtain ⟨u, v, huo, hux, hvo, hvx, H⟩ := by rwa [mem_nhds_prod_iff'] at this
  exact ⟨_, huo.inter hvo, ⟨hux, hvx⟩, fun p hp ↦ H ⟨hp.1.1, hp.2.2⟩⟩

variable [CompactSpace X]

/-- If `S` is any neighbourhood of the diagonal in a compact topological space `X`, then there
exists a finite cover of `X` by opens `U i` such that `U i ×ˢ U i ⊆ S` for all `i`.

That the indexing set is a finset of `X` is an artifact of the proof; it could be any finite type.
-/
lemma exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact
    (hS : S ∈ nhdsSet (diagonal X)) :
    ∃ (t : Finset X) (U : t → Opens X), IsOpenCover U ∧ ∀ i, (U i : Set X) ×ˢ U i ⊆ S := by
  choose U hUo hUx hUp using exists_open_prod_subset_of_mem_nhds_diagonal hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hUo (fun x _ ↦ mem_iUnion.mpr ⟨_, hUx x⟩)
  refine ⟨t, fun i ↦ ⟨_, hUo i⟩, .of_sets _ ?_, (hUp ·)⟩
  simpa [iUnion_subtype, ← univ_subset_iff] using ht

variable [TotallyDisconnectedSpace X] [T2Space X]

/-- If `S` is any neighbourhood of the diagonal in a profinite topological space `X`, then there
exists a finite cover of `X` by disjoint nonempty clopens `U i` with `U i ×ˢ U i ⊆ S` for all `i`.
-/
private lemma exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite
    (hS : S ∈ nhdsSet (diagonal X)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧ (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (y, z) ∈ S)
    ∧ (univ : Set X) ⊆ ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  obtain ⟨t, U, hUc, hUS⟩ := exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact hS
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j ↦ (hW₁ j).1, fun j y hy z hz ↦ ?_, hW₂, hW₃⟩
  exact match (hW₁ j).2 with | ⟨i, hi⟩ => hUS i ⟨hi hy, hi hz⟩

end TopologicalSpace

namespace ContinuousMap

variable {X V : Type*} [TopologicalSpace X] [TopologicalSpace V] [TotallyDisconnectedSpace X]
  [T2Space X] [CompactSpace X] {S : Set (V × V)} (f : C(X, V))

/--
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbourhood of the
diagonal in `V × V`, there exists a finite cover of `X` by pairwise-disjoint nonempty clopens, on
each of which `f` varies within `S`.
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧ (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S)
    ∧ (univ : Set X) ⊆ ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  have : (f.prodMap f) ⁻¹' S ∈ nhdsSet (diagonal X) := by
    rw [mem_nhdsSet_iff_forall] at hS ⊢
    rintro ⟨x, y⟩ (rfl : x = y)
    exact (map_continuous _).continuousAt.preimage_mem_nhds (hS _ rfl)
  exact exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite this

/--
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbourhood of the
diagonal in `V × V`, the function `f` can be `S`-approximated by a function factoring through
`Fin n`, for some `n`. -/
lemma exists_finite_approximation_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (g : X → Fin n) (h : Fin n → V), Continuous g ∧ ∀ x, (f x, h (g x)) ∈ S := by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
  have h_uniq (x) : ∃! i, x ∈ E i := by
    refine match mem_iUnion.mp (hEuniv <| mem_univ x) with
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
If `f` is a continuous map from a profinite space to a topological space with a commutative monoid
structure, then we can approximate `f` by finite products of indicator functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.)
-/
@[to_additive /-- If `f` is a continuous map from a profinite space to a topological space with a
commutative additive monoid structure, then we can approximate `f` by finite sums of indicator
functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.) -/]
lemma exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal [CommMonoid V]
    (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (U : Fin n → Clopens X) (v : Fin n → V),
    ∀ x, (f x, ∏ n, mulIndicator (U n) (fun _ ↦ v n) x) ∈ S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i ↦ ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x ↦ ?_⟩
  convert hgh x
  exact (Fintype.prod_eq_single _ fun i hi ↦ mulIndicator_of_notMem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

end ContinuousMap
