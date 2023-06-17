/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module wiedijk_100_theorems.konigsberg
! leanprover-community/mathlib commit 5563b1b49e86e135e8c7b556da5ad2f5ff881cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Trails
import Mathbin.Tactic.DeriveFintype

/-!
# The Königsberg bridges problem

We show that a graph that represents the islands and mainlands of Königsberg and seven bridges
between them has no Eulerian trail.
-/


namespace Konigsberg

/-- The vertices for the Königsberg graph; four vertices for the bodies of land and seven
vertices for the bridges. -/
@[nolint has_inhabited_instance]
inductive Verts : Type
  | V1
  | V2
  | V3
  | V4-- The islands and mainlands

  | B1
  | B2
  | B3
  | B4
  | B5
  | B6
  | B7
  deriving DecidableEq, Fintype
#align konigsberg.verts Konigsberg.Verts

-- The bridges
open Verts

/-- Each of the connections between the islands/mainlands and the bridges.
These are ordered pairs, but the data becomes symmetric in `konigsberg.adj`. -/
def edges : List (Verts × Verts) :=
  [(V1, B1), (V1, B2), (V1, B3), (V1, B4), (V1, B5), (B1, V2), (B2, V2), (B3, V4), (B4, V3),
    (B5, V3), (V2, B6), (B6, V4), (V3, B7), (B7, V4)]
#align konigsberg.edges Konigsberg.edges

/-- The adjacency relation for the Königsberg graph. -/
def adj (v w : Verts) : Bool :=
  (v, w) ∈ edges || (w, v) ∈ edges
#align konigsberg.adj Konigsberg.adj

/-- The Königsberg graph structure. While the Königsberg bridge problem
is usually described using a multigraph, the we use a "mediant" construction
to transform it into a simple graph -- every edge in the multigraph is subdivided
into a path of two edges. This construction preserves whether a graph is Eulerian.

(TODO: once mathlib has multigraphs, either prove the mediant construction preserves the
Eulerian property or switch this file to use multigraphs. -/
@[simps]
def graph : SimpleGraph Verts where
  Adj v w := adj v w
  symm := by
    dsimp [Symmetric, adj]
    decide
  loopless := by
    dsimp [Irreflexive, adj]
    decide
#align konigsberg.graph Konigsberg.graph

instance : DecidableRel graph.Adj := fun a b => decidable_of_bool (adj a b) Iff.rfl

/-- To speed up the proof, this is a cache of all the degrees of each vertex,
proved in `konigsberg.degree_eq_degree`. -/
@[simp]
def degree : Verts → ℕ
  | V1 => 5
  | V2 => 3
  | V3 => 3
  | V4 => 3
  | B1 => 2
  | B2 => 2
  | B3 => 2
  | B4 => 2
  | B5 => 2
  | B6 => 2
  | B7 => 2
#align konigsberg.degree Konigsberg.degree

@[simp]
theorem degree_eq_degree (v : Verts) : graph.degree v = degree v := by cases v <;> rfl
#align konigsberg.degree_eq_degree Konigsberg.degree_eq_degree

/-- The Königsberg graph is not Eulerian. -/
theorem not_isEulerian {u v : Verts} (p : graph.Walk u v) (h : p.IsEulerian) : False :=
  by
  have : {v | Odd (graph.degree v)} = {verts.V1, verts.V2, verts.V3, verts.V4} :=
    by
    ext w
    simp only [degree_eq_degree, Nat.odd_iff_not_even, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    cases w <;> simp
  have h := h.card_odd_degree
  simp_rw [this] at h 
  norm_num at h 
#align konigsberg.not_is_eulerian Konigsberg.not_isEulerian

end Konigsberg

