import Mathlib.Combinatorics.SimpleGraph.Finite
set_option linter.style.header false
namespace SimpleGraph
variable {α : Type*} (G : SimpleGraph α)


lemma induce_spanningCoe_adj (G : SimpleGraph α) (s : Set α) {u v : α} :
    (G.induce s).spanningCoe.Adj u v ↔ G.Adj u v ∧ u ∈ s ∧ v ∈ s := by simp

section degreeOn
abbrev neighborOnSet (s : Set α) (a : α) : Set α := (G.induce s).spanningCoe.neighborSet a

@[simp]
lemma mem_neighborOnSet {s : Set α} {a v : α} :
    v ∈ G.neighborOnSet s a ↔ G.Adj a v ∧ a ∈ s ∧ v ∈ s := by
  rw [mem_neighborSet, induce_spanningCoe_adj]

variable {G} {s t : Set α} {a v : α}
lemma neighborOnSet.mono (h : s ⊆ t) : G.neighborOnSet s a ⊆ G.neighborOnSet t a := by
  intro x hx
  rw [mem_neighborOnSet] at *
  exact ⟨hx.1, h hx.2.1, h hx.2.2⟩

lemma neighborOnSet_subset_neighborSet : G.neighborOnSet s a ⊆ G.neighborSet a := by
  intro x hx
  rw [mem_neighborOnSet] at hx
  exact hx.1

/-- `G.degreeOn s a` is the number of neighbors of `a` in `s` -/
abbrev neighborOnFinset (s : Set α) (a : α) [Fintype (G.neighborOnSet s a)]
    : Finset α := (G.neighborOnSet s a).toFinset

variable [Fintype (G.neighborOnSet s a)]

@[simp]
lemma mem_neighborOnFinset :
    v ∈ G.neighborOnFinset s a ↔ G.Adj a v ∧ a ∈ s ∧ v ∈ s := by
  rw [Set.mem_toFinset, mem_neighborOnSet]

lemma neighborOnFinset_subset_neighborFinset  [Fintype (G.neighborSet a)] :
    G.neighborOnFinset s a ⊆ G.neighborFinset a := by
  intro x hx
  rw [mem_neighborOnFinset, mem_neighborFinset] at *
  exact hx.1

open Finset
abbrev degreeOn (s : Set α) (a : α) [Fintype (G.neighborOnSet s a)] : ℕ :=
    #(G.neighborOnFinset s a)


lemma degreeOn.mono (h : s ⊆ t) [Fintype (G.neighborOnSet t a)] :
    G.degreeOn s a ≤ G.degreeOn t a := by
  apply card_le_card
  intro x hx
  rw [mem_neighborOnFinset] at *
  exact ⟨hx.1, h hx.2.1, h hx.2.2⟩

lemma degreeOn_not_mem (h : a ∉ s) :
    G.degreeOn s a = 0 := by
  by_contra! hf
  rw [← Nat.pos_iff_ne_zero] at hf
  obtain ⟨v, hv⟩ := card_pos.1 hf
  rw [mem_neighborOnFinset] at hv
  exact h hv.2.1

variable [Fintype (G.neighborSet a)] (s) (a)
lemma degreeOn_le_degree : G.degreeOn s a ≤ G.degree a := by
  rw [degreeOn, degree]
  apply card_le_card
  intro m hm
  rw [mem_neighborOnFinset] at hm
  simpa using hm.1

variable {s} {a}
lemma subset_of_degree_le_degreeOn  (h : G.degree a ≤ G.degreeOn s a) :
    (∀ v, G.Adj a v → v ∈ s) := by
  rw [degree, degreeOn] at h
  have := eq_of_subset_of_card_le neighborOnFinset_subset_neighborFinset h
  intro v hv
  rw [← mem_neighborFinset, ← this, mem_neighborOnFinset] at hv
  exact hv.2.2

lemma degreeOn_lt_degree (hv : v ∈ G.neighborFinset a ∧ v ∉ s) :
    G.degreeOn s a < G.degree a :=
  lt_of_le_of_ne (degreeOn_le_degree s a) fun hf ↦
     hv.2 ((subset_of_degree_le_degreeOn  hf.symm.le) v <| (mem_neighborFinset ..).1 hv.1)

end degreeOn
end SimpleGraph
