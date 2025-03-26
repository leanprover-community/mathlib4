import Mathlib.Combinatorics.SimpleGraph.Finite
set_option linter.style.header false
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
open Finset

section degreeOn

variable  [DecidableRel G.Adj] [Fintype α]
open Finset

variable [DecidableEq α]
variable (G) in
abbrev degreeOn (s : Finset α) (a : α) : ℕ := #(G.neighborFinset a ∩ s)

lemma degreeOn.mono {s t : Finset α} {a : α} (h : s ⊆ t) : G.degreeOn s a ≤ G.degreeOn t a :=
    card_le_card fun _ hv ↦ mem_inter.2 ⟨(mem_inter.1 hv).1, h (mem_inter.1 hv).2⟩

lemma degreeOn_erase (s : Finset α) (a : α) : G.degreeOn (s.erase a) a = G.degreeOn s a := by
  apply le_antisymm (degreeOn.mono <| erase_subset ..)
  apply card_le_card
  intro v hv
  rw [mem_inter, mem_neighborFinset] at *
  use hv.1, mem_erase_of_ne_of_mem (fun hf ↦ G.loopless _ (hf ▸ hv.1)) hv.2

lemma degreeOn_le_degree (s : Finset α) (a : α) :
    G.degreeOn s a ≤ G.degree a := by
  rw [degreeOn, degree]
  apply card_le_card
  intro m hm
  simp only [mem_inter, mem_neighborFinset] at *
  exact hm.1

lemma degree_le_degreeOn_iff (s : Finset α) (a : α) :
    G.degree a ≤ G.degreeOn s a ↔ G.neighborFinset a ⊆ s := by
  constructor <;> rw [degree, degreeOn]
  · intro heq _ hx
    exact (mem_inter.1 ((eq_of_subset_of_card_le (inter_subset_left) heq).symm ▸ hx)).2
  · intro hs
    apply card_le_card fun _ hx ↦ mem_inter.2 ⟨hx, hs hx⟩

lemma degreeOn_lt_degree {a v : α} {s : Finset α} (hv : v ∈ G.neighborFinset a ∧ v ∉ s) :
    G.degreeOn s a < G.degree a :=
  lt_of_le_of_ne (degreeOn_le_degree s a) fun hf ↦
     hv.2 ((degree_le_degreeOn_iff ..).1 hf.symm.le hv.1)

end degreeOn
end SimpleGraph
