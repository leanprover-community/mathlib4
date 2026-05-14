/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.NeZero
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Common
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

theorem set_walk_self_length_zero_eq (u : V) : {p : G.Walk u u | p.length = 0} = {Walk.nil} := by
  simp

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n.succ} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv =>
    simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image]
    grind

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.snd, match p with
    | ⟨.cons _ (.cons _ .nil), _⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl

section LocallyFinite

variable [DecidableEq V] [LocallyFinite G]

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
  induction n generalizing u v with
  | zero =>
    obtain rfl | huv := eq_or_ne u v <;> simp [finsetWalkLength, set_walk_length_zero_eq_of_ne, *]
  | succ n ih =>
    simp only [finsetWalkLength, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_univ, Set.iUnion_true, Finset.coe_map, Set.iUnion_coe_set]
    congr!
    grind

variable {G} in
theorem mem_finsetWalkLength_iff {n : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

/-- The `Finset` of walks from `u` to `v` with length less than `n`. See `finsetWalkLength` for
context. In particular, we use this definition for `SimpleGraph.Path.instFintype`. -/
def finsetWalkLengthLT (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  (Finset.range n).disjiUnion
    (fun l ↦ G.finsetWalkLength l u v)
    (fun l _ l' _ hne _ hsl hsl' p hp ↦
      have hl : p.length = l := mem_finsetWalkLength_iff.mp (hsl hp)
      have hl' : p.length = l' := mem_finsetWalkLength_iff.mp (hsl' hp)
      False.elim <| hne <| hl.symm.trans hl')

open Finset in
theorem coe_finsetWalkLengthLT_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLengthLT n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length < n} := by
  ext p
  simp [finsetWalkLengthLT, mem_finsetWalkLength_iff]

variable {G} in
theorem mem_finsetWalkLengthLT_iff {n : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ G.finsetWalkLengthLT n u v ↔ p.length < n :=
  Set.ext_iff.mp (G.coe_finsetWalkLengthLT_eq n u v) p

instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]

instance fintypeSubtypeWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.length = n}

theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  simp [← coe_finsetWalkLength_eq]

/- See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card {p : G.Walk u v | p.length = n} = #(G.finsetWalkLength n u v) :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]

instance fintypeSetWalkLengthLT (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length < n} :=
  Fintype.ofFinset (G.finsetWalkLengthLT n u v) fun p ↦ by
    rw [← Finset.mem_coe, coe_finsetWalkLengthLT_eq]

instance fintypeSubtypeWalkLengthLT (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length < n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.length < n}

instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
  Fintype.ofFinset {w ∈ G.finsetWalkLength n u v | w.IsPath} <| by
    simp [mem_finsetWalkLength_iff, and_comm]

instance fintypeSubtypePathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length = n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n}

instance fintypeSetPathLengthLT (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n} :=
  Fintype.ofFinset {w ∈ G.finsetWalkLengthLT n u v | w.IsPath} <| by
    simp [mem_finsetWalkLengthLT_iff, and_comm]

instance fintypeSubtypePathLengthLT (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length < n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n}

end LocallyFinite

section Fintype
variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

instance Path.instFintype {u v : V} : Fintype (G.Path u v) where
  elems := (univ (α := { p : G.Walk u v | p.IsPath ∧ p.length < Fintype.card V })).map
    ⟨fun p ↦ { val := p.val, property := p.prop.left },
     fun _ _ h ↦ SetCoe.ext <| Subtype.mk.injEq .. ▸ h⟩
  complete p := mem_map.mpr ⟨
    ⟨p.val, ⟨p.prop, p.prop.length_lt⟩⟩,
    ⟨mem_univ _, rfl⟩⟩

end Fintype
end SimpleGraph
