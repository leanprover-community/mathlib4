import Mathlib.Combinatorics.SimpleGraph.Finite
set_option linter.style.header false
namespace SimpleGraph
variable {α : Type*} (G : SimpleGraph α)
open Set

section degreeIn
open Set

lemma induce_spanningCoe_adj (G : SimpleGraph α) (s : Set α) {u v : α} :
    (G.induce s).spanningCoe.Adj u v ↔ G.Adj u v ∧ u ∈ s ∧ v ∈ s := by simp

/-- The set of neighbors of `a` in the graph `G` that belong to the set `s`. (Note: this is not
`(G.induce s).spanningCoe.neighborSet a` since `a` may not belong to `s`. -/
abbrev neighborInSet (s : Set α) (a : α) : Set α := {v | G.Adj a v ∧ v ∈ s}

lemma neighborInSet_eq (s : Set α) (a : α) : G.neighborInSet s a =
  (G.induce (s.insert a)).spanningCoe.neighborSet a := by
  ext v
  simp only [mem_setOf_eq, mem_neighborSet, map_adj, comap_adj, Function.Embedding.subtype_apply,
      Subtype.exists, exists_and_left, exists_prop, existsAndEq, and_true, true_and,
      and_congr_right_iff]
  intro h
  constructor
  · intro hv
    exact ⟨Set.mem_insert .., Set.mem_insert_of_mem _ hv⟩
  · intro ⟨_, hv⟩
    exact Set.mem_of_mem_insert_of_ne hv h.ne.symm

lemma neighborInSet_subset_neighborSet (s : Set α) (a : α) :
    G.neighborInSet s a ⊆ G.neighborSet a := fun _ hx ↦ hx.1

lemma neighborInSet_subset_set (s : Set α) (a : α) : G.neighborInSet s a ⊆ s:= fun _ hx ↦ hx.2

instance (s : Set α) (a : α) [DecidableRel G.Adj] [Fintype (G.neighborSet a)]
    [DecidablePred (· ∈ s)] : Fintype (G.neighborInSet s a) :=
  Set.fintypeSubset _ (G.neighborInSet_subset_neighborSet s a)

@[simp]
lemma mem_neighborInSet {s : Set α} {a v : α} :
    v ∈ G.neighborInSet s a ↔ G.Adj a v ∧ v ∈ s := by rfl

variable {G} {s t : Set α} {a v : α}
lemma neighborInSet.mono (h : s ⊆ t) : G.neighborInSet s a ⊆ G.neighborInSet t a :=
  fun _ hx ↦ ⟨hx.1, h hx.2⟩

/-- `G.degreeIn s a` is the number of neighbors of `a` in `s` -/
abbrev neighborInFinset (s : Set α) (a : α) [Fintype (G.neighborInSet s a)] : Finset α :=
    (G.neighborInSet s a).toFinset

variable [Fintype (G.neighborInSet s a)]
@[simp]
lemma mem_neighborInFinset :
    v ∈ G.neighborInFinset s a ↔ G.Adj a v ∧ v ∈ s := by
  simp

lemma neighborInFinset_subset_neighborFinset [Fintype (G.neighborSet a)] :
    G.neighborInFinset s a ⊆ G.neighborFinset a := by
  intro x hx
  rw [mem_neighborInFinset, mem_neighborFinset] at *
  exact hx.1

lemma neighborInFinset_subset_set :
    (G.neighborInFinset s a : Set α) ⊆ s := by
  intro x hx
  rw [coe_toFinset] at hx
  exact hx.2

open Finset
variable (G) in
abbrev degreeIn (s : Set α) (a : α) [Fintype (G.neighborInSet s a)] : ℕ :=
    #(G.neighborInFinset s a)

lemma degreeIn.mono (h : s ⊆ t) [Fintype (G.neighborInSet t a)] :
    G.degreeIn s a ≤ G.degreeIn t a := by
  apply Finset.card_le_card
  intro x hx
  rw [mem_neighborInFinset] at *
  exact ⟨hx.1, h hx.2⟩

variable (s) (a) [Fintype (G.neighborSet a)]
lemma degreeIn_le_degree : G.degreeIn s a ≤ G.degree a := by
  rw [degreeIn, degree]
  apply Finset.card_le_card
  intro m hm
  rw [mem_neighborInFinset] at hm
  simpa using hm.1

lemma degree_le_degreeIn_iff : G.degree a ≤ G.degreeIn s a ↔ ∀ v, G.Adj a v → v ∈ s:= by
  constructor <;> rw [degree, degreeIn]
  · intro heq _ hx
    have := Finset.eq_of_subset_of_card_le neighborInFinset_subset_neighborFinset heq
    rw [ ← mem_neighborFinset,← this] at hx
    exact neighborInFinset_subset_set hx
  · intro hs
    apply Finset.card_le_card
    intro x hx
    rw [mem_neighborInFinset, mem_neighborFinset] at *
    exact ⟨hx, hs _ hx⟩

lemma degreeIn_lt_degree (hv : v ∈ G.neighborFinset a ∧ v ∉ s) :
    G.degreeIn s a < G.degree a :=
  lt_of_le_of_ne (degreeIn_le_degree s a) <| fun hf ↦ hv.2
    <| (degree_le_degreeIn_iff ..).1 hf.symm.le _ ((mem_neighborFinset ..).1 hv.1)

end degreeIn
end SimpleGraph
