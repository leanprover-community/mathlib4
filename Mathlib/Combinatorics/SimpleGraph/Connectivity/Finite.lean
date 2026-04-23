/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.FastInstance
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

@[expose] public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

theorem ConnectedComponent.card_le_card_of_le [Finite V] {G G' : SimpleGraph V} (h : G ≤ G') :
    Nat.card G'.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  Nat.card_le_card_of_surjective _ <| ConnectedComponent.surjective_map_ofLE h

section Fintype

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

instance : Fintype G.ConnectedComponent :=
  fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance : Decidable G.Preconnected :=
  inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)

instance : Decidable G.Connected :=
  decidable_of_iff (G.Preconnected ∧ (Finset.univ : Finset V).Nonempty) <| by
    rw [connected_iff, ← Finset.univ_nonempty_iff]

instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn (fun w ↦ decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

variable {G} in
lemma disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G ≤ G')
    (c' : ConnectedComponent G') [Fintype c'.supp]
    [DecidablePred fun c : G.ConnectedComponent ↦ c.supp ⊆ c'.supp] :
    .disjiUnion {c : ConnectedComponent G | c.supp ⊆ c'.supp} (fun c ↦ c.supp.toFinset)
      (fun x _ y _ hxy ↦ by simpa using pairwise_disjoint_supp_connectedComponent _ hxy) =
      c'.supp.toFinset :=
  Finset.coe_injective <| by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

end Fintype

/-- The odd components are the connected components of odd cardinality. This definition excludes
infinite components. -/
abbrev oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}

lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp [Finite V] {G'}
    (h : G ≤ G') (c' : ConnectedComponent G') :
    Odd {c ∈ G.oddComponents | c.supp ⊆ c'.supp}.ncard ↔ Odd c'.supp.ncard := by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp, ← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_setOf, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

lemma odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.card V) := by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent ↦ x.supp.ncard)).symm

lemma ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G ≤ G') :
     G'.oddComponents.ncard ≤ G.oddComponents.ncard := by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp ⊆ c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' ↦ ?_
    simpa [-Nat.card_eq_fintype_card, -Set.coe_setOf, h']
      using (c.odd_oddComponents_ncard_subset_supp _ h).2 hc
  let f : G'.oddComponents → G.oddComponents :=
    fun ⟨c, hc⟩ ↦ ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' ↦ ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

end SimpleGraph
