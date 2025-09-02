/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# The Königsberg bridges problem

We show that a graph that represents the islands and mainlands of Königsberg and seven bridges
between them has no Eulerian trail.
-/


namespace Konigsberg

/-- The vertices for the Königsberg graph; four vertices for the bodies of land and seven
vertices for the bridges. -/
inductive Verts : Type
  -- The islands and mainlands
  | V1 | V2 | V3 | V4
  -- The bridges
  | B1 | B2 | B3 | B4 | B5 | B6 | B7
  deriving DecidableEq, Fintype

open Verts

/-- Each of the connections between the islands/mainlands and the bridges.
These are ordered pairs, but the data becomes symmetric in `Konigsberg.adj`. -/
def edges : List (Verts × Verts) :=
  [(V1, B1), (V1, B2), (V1, B3), (V1, B4), (V1, B5),
   (B1, V2), (B2, V2), (B3, V4), (B4, V3), (B5, V3),
   (V2, B6), (B6, V4),
   (V3, B7), (B7, V4)]

/-- The adjacency relation for the Königsberg graph. -/
def adj (v w : Verts) : Bool := (v, w) ∈ edges || (w, v) ∈ edges

/-- The Königsberg graph structure. While the Königsberg bridge problem
is usually described using a multigraph, we use a "mediant" construction
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

instance : DecidableRel graph.Adj := fun a b => inferInstanceAs <| Decidable (adj a b)

/-- To speed up the proof, this is a cache of all the degrees of each vertex,
proved in `Konigsberg.degree_eq_degree`. -/
def degree : Verts → ℕ
  | V1 => 5 | V2 => 3 | V3 => 3 | V4 => 3
  | B1 => 2 | B2 => 2 | B3 => 2 | B4 => 2 | B5 => 2 | B6 => 2 | B7 => 2

@[simp]
lemma degree_eq_degree (v : Verts) : graph.degree v = degree v := by cases v <;> rfl

lemma not_even_degree_iff (w : Verts) : ¬Even (degree w) ↔ w = V1 ∨ w = V2 ∨ w = V3 ∨ w = V4 := by
  cases w <;> decide

lemma setOf_odd_degree_eq :
    {v | Odd (graph.degree v)} = {Verts.V1, Verts.V2, Verts.V3, Verts.V4} := by
  ext w
  simp [not_even_degree_iff, ← Nat.not_even_iff_odd]

/-- The Königsberg graph is not Eulerian. -/
theorem not_isEulerian {u v : Verts} (p : graph.Walk u v) (h : p.IsEulerian) : False := by
  have h := h.card_odd_degree
  have h' := setOf_odd_degree_eq
  apply_fun Fintype.card at h'
  rw [h'] at h
  simp at h

end Konigsberg
