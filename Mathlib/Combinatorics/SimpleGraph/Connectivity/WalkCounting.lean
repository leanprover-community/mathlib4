/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Finite

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

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-! ### Walks of a given length -/

section WalkCounting

theorem set_walk_self_length_zero_eq (u : V) : {p : G.Walk u u | p.length = 0} = {Walk.nil} := by
  ext p
  simp

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
  exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n.succ} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases' p with _ _ w _ huw pwv
  · simp [eq_comm]
  · simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro rfl
      exact ⟨w, huw, pwv, rfl, rfl⟩
    · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
      rfl

variable [DecidableEq V]

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.getVert 1, match p with
    | ⟨.cons _ (.cons _ .nil), hp⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl
  right_inv _ := rfl

section LocallyFinite

variable [LocallyFinite G]

/-- The `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `SimpleGraph.coe_finsetWalkLength_eq` for the relationship between this `Finset` and
the set of length-`n` walks. -/
def finsetWalkLength (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩

theorem coe_finsetWalkLength_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
  induction' n with n ih generalizing u v
  · obtain rfl | huv := eq_or_ne u v <;> simp [finsetWalkLength, set_walk_length_zero_eq_of_ne, *]
  · simp only [finsetWalkLength, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_univ, Set.iUnion_true]
    ext p
    simp only [mem_neighborSet, Finset.coe_map, Embedding.coeFn_mk, Set.iUnion_coe_set,
      Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    congr!
    rename_i w _ q
    have := Set.ext_iff.mp (ih w v) q
    simp only [Finset.mem_coe, Set.mem_setOf_eq] at this
    rw [← this]

variable {G}

theorem Walk.mem_finsetWalkLength_iff_length_eq {n : ℕ} {u v : V} (p : G.Walk u v) :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

variable (G)

instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]

instance fintypeSubtypeWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
  fintypeSetWalkLength G u v n

theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  ext p
  simp [← coe_finsetWalkLength_eq]

/- See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card {p : G.Walk u v | p.length = n} = (G.finsetWalkLength n u v).card :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]

instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
  Fintype.ofFinset ((G.finsetWalkLength n u v).filter Walk.IsPath) <| by
    simp [Walk.mem_finsetWalkLength_iff_length_eq, and_comm]

end LocallyFinite

section Finite

variable [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [Walk.mem_finsetWalkLength_iff_length_eq]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

instance : Fintype G.ConnectedComponent :=
  @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance : Decidable G.Preconnected :=
  inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)

instance : Decidable G.Connected := by
  rw [connected_iff, ← Finset.univ_nonempty_iff]
  infer_instance

instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn (fun w ↦ decidable_of_iff (G.Reachable v w) $ by simp)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

lemma odd_card_odd_components (ho : Odd (Fintype.card V)) :
    Odd (Nat.card ({(c : ConnectedComponent G) | Odd (Nat.card c.supp)})) := by
  simp_rw [Nat.odd_iff_not_even]
  by_contra! hc
  simp_rw [← Nat.odd_iff_not_even] at hc
  rw [
    ← (set_fintype_card_eq_univ_iff _).mpr (@ConnectedComponent.iUnion_supp _ G),
    ← Set.toFinset_card, Nat.odd_iff_not_even] at ho
  apply ho
  have : Set.toFinset (⋃ (x : ConnectedComponent G), ConnectedComponent.supp x) =
      Finset.biUnion (Finset.univ : Finset (ConnectedComponent G))
      (fun x => (ConnectedComponent.supp x).toFinset) := by
    ext v
    simp only [Set.mem_toFinset, Set.mem_iUnion, ConnectedComponent.mem_supp_iff, exists_eq',
      Finset.mem_biUnion, Finset.mem_univ, true_and, true_iff]
  rw [this, Finset.card_biUnion (fun x _ y _ hxy ↦
    Set.disjoint_toFinset.mpr (ConnectedComponent.pairwise_disjoint_supp hxy))]

  simp only [Set.toFinset_card]
  simp_rw [Fintype.card_eq_nat_card]
  have : Even (Finset.filter (fun x : ConnectedComponent G ↦ Odd (Nat.card ↑x.supp)) Finset.univ).card := by
    simp only [Finset.subtype_univ, Finset.card_univ, Nat.card_eq_fintype_card]
    simp only [Nat.card_eq_fintype_card] at hc
    rw [Fintype.card_ofFinset] at hc
    exact hc
  exact Finset.even_sum_of_even_card_odd _ this

end Finite

end WalkCounting

end SimpleGraph
