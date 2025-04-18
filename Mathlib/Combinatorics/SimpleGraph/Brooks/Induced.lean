
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
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

/-- A `PartColoring n s` of `G` is a coloring of all vertices of `G` that is valid on the set `s` -/
abbrev PartColoring (n : ℕ) (s : Set α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.Coloring (Fin n)

/-- `G.PartColorable n s` is the predicate for existence of a `PartColoring n s` of `G`. -/
abbrev PartColorable (n : ℕ) (s : Set α) := ((⊤ : Subgraph G).induce s).spanningCoe.Colorable n

omit [DecidableRel G.Adj]
variable {G} {n : ℕ}
lemma PartColorable.succ_ofNotAdj  {s : Set α} (h : ∀ u v, u ∈ s → v ∈ s → ¬ G.Adj u v) :
    G.PartColorable (n + 1) s := ⟨⊥, by simpa⟩

lemma  PartColorable.union {s t : Set α} (hs : G.PartColorable n s) (ht : G.PartColorable n t)
  (h : ∀ u v, u ∈ s → v ∈ t → ¬ G.Adj u v) : G.PartColorable n (s ∪ t) := by
  classical
  obtain ⟨C₁⟩ := hs
  obtain ⟨C₂⟩ := ht
  exact ⟨(fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)), by
      simp only [Set.mem_union, ne_eq]
      intro v w hadj hf
      simp only [Subgraph.spanningCoe_adj, Subgraph.induce_adj, Set.mem_union,
        Subgraph.top_adj] at hadj
      cases hadj.1 with
      | inl hv =>
        cases hadj.2.1 with
        | inl hw =>
          rw [if_pos hv, if_pos hw] at hf;
          exact C₁.valid (by simpa using ⟨hv, hw, hadj.2.2⟩) hf
        | inr hw => exact h _  _ hv hw hadj.2.2
      | inr hv =>
        cases hadj.2.1 with
        | inl hw => exact h _ _  hw hv hadj.2.2.symm
        | inr hw =>
          split_ifs at hf with h1 h2 h3
          · exact h _  _ h1 hw hadj.2.2
          · exact h _  _ h1 hw hadj.2.2
          · exact h _  _ h3 hv hadj.2.2.symm
          · exact C₂.valid (by simpa using ⟨hv, hw, hadj.2.2⟩) hf⟩

omit [DecidablePred (· ∈ s)]
lemma  PartColorable.insertNotAdj {b : α} {hs : G.PartColorable (n + 1) s}
    (h : ∀ v, v ∈ s → ¬ G.Adj b v) : G.PartColorable (n + 1) (insert b s) := by
  rw [Set.insert_eq]
  apply PartColorable.union _ hs
  · intro u v hu hv hadj
    rw [Set.mem_singleton_iff] at hu
    exact h v hv (hu ▸ hadj)
  · exact ⟨⊥, by simp⟩

namespace PartColoring
protected def copy {s t} (C : G.PartColoring n s) (h : s = t) : G.PartColoring n t := h ▸ C

@[simp]
theorem copy_rfl {s} (C : G.PartColoring n s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartColoring n s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

def toColoring (C : G.PartColoring n Set.univ) : G.Coloring (Fin n) :=
    ⟨C, fun hab ↦ C.valid (by simpa using hab)⟩

end PartColoring

end withDecRel
end SimpleGraph
