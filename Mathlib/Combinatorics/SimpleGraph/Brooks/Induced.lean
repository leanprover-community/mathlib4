
import Mathlib.Combinatorics.SimpleGraph.Subgraph
set_option linter.style.header false

/-

Develop some API for induced subgraphs as SimpleGraphs, i.e.
`(⊤ : Subgraph G).induce s).spanningCoe`

-/
namespace SimpleGraph
open Subgraph

variable {α : Type*} (G : SimpleGraph α)

abbrev neighborSetIn (s : Set α) (a : α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.neighborSet a

lemma mem_neighborSetIn {s : Set α} {a v : α} :
  v ∈ G.neighborSetIn s a ↔ a ∈ s ∧ v ∈ s ∧ G.Adj a v := by simp

lemma neighborSetIn_eq_inter_of_mem {s : Set α} {a : α} (ha : a ∈ s) :
    G.neighborSetIn s a = G.neighborSet a ∩ s := by
  aesop

section withDecRel

variable [DecidableRel G.Adj] {s : Set α} [DecidablePred (· ∈ s)]

/-- If a graph is locally finite at a vertex, then so is a spanningCoe of a
subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

instance finiteAtCoe {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.spanningCoe.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

abbrev degreeIn (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)]  :=
  ((⊤ : Subgraph G).induce s).spanningCoe.degree a

lemma degreeIn_eq (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)] :
  G.degreeIn s a = ((⊤ : Subgraph G).induce s).degree a := by simp

variable {s t : Set α} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]

variable {a : α}  [Fintype (G.neighborSet a)]

lemma degreeIn.mono (h : s ⊆ t) : G.degreeIn s a ≤ G.degreeIn t a := by
  rw [degreeIn_eq, degreeIn_eq]
  exact (degree_le' _ _ (induce_mono_right h) a)

variable (a) in
lemma degreeIn_le_degree : G.degreeIn s a ≤ G.degree a := by
  rw [degreeIn_eq]
  exact degree_le _ _

lemma neighborSet_subset_of_degree_le_degreeIn (h : G.degree a ≤ G.degreeIn s a) :
      G.neighborSet a ⊆ s := by
  rw [degree, degreeIn_eq, ← finset_card_neighborSet_eq_degree] at h
  intro v ha
  apply ((⊤ : Subgraph G).induce s).neighborSet_subset_verts a
  rwa [← Set.mem_toFinset, Finset.eq_of_subset_of_card_le (fun v ↦ by simp) h, mem_neighborFinset]

lemma degreeIn_lt_degree {v : α} (hv : v ∈ G.neighborSet a ∧ v ∉ s) :
    G.degreeIn s a < G.degree a :=
  lt_of_le_of_ne (G.degreeIn_le_degree a)
    fun h ↦ hv.2 <| G.neighborSet_subset_of_degree_le_degreeIn h.symm.le hv.1
