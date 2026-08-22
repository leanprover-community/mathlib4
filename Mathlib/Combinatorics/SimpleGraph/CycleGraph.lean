/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Definition of cycle graphs

This file defines and proves several fact about cycle graphs on `n` vertices and the cycle around
the cycle graph when `n ≥ 3`.

## Main declarations

* `SimpleGraph.cycleGraph n`: the cycle graph over `Fin n`.
* `(SimpleGraph.cycleGraph n).cycle`: the cycle around `cycleGraph (n + 3)` starting at 0.
-/

@[expose] public section

namespace SimpleGraph

open Walk

/-- Cycle graph over `Fin n` -/
def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
  | 0 | 1 => ⊥
  | _ + 2 => {
    Adj a b := a - b = 1 ∨ b - a = 1
  }

instance : (n : ℕ) → DecidableRel (cycleGraph n).Adj
  | 0 | 1 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 2 => by unfold cycleGraph; infer_instance

theorem cycleGraph_zero_adj {u v : Fin 0} : ¬(cycleGraph 0).Adj u v := id

theorem cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥ := Subsingleton.elim _ _
theorem cycleGraph_one_eq_bot : cycleGraph 1 = ⊥ := Subsingleton.elim _ _
theorem cycleGraph_zero_eq_top : cycleGraph 0 = ⊤ := Subsingleton.elim _ _
theorem cycleGraph_one_eq_top : cycleGraph 1 = ⊤ := Subsingleton.elim _ _

theorem cycleGraph_two_eq_top : cycleGraph 2 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

theorem cycleGraph_three_eq_top : cycleGraph 3 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

theorem cycleGraph_one_adj {u v : Fin 1} : ¬(cycleGraph 1).Adj u v := by
  simp [cycleGraph_one_eq_bot]

theorem cycleGraph_adj {n : ℕ} {u v : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 := Iff.rfl

theorem cycleGraph_adj' {n : ℕ} {u v : Fin n} :
    (cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1 := by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]

theorem cycleGraph_neighborSet {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]

theorem cycleGraph_neighborFinset {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1} := by
  simp [neighborFinset, cycleGraph_neighborSet]

theorem cycleGraph_degree_two_le {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1} := by
  rw [SimpleGraph.degree, cycleGraph_neighborFinset]

theorem cycleGraph_degree_three_le {n : ℕ} {v : Fin (n + 3)} :
    (cycleGraph (n + 3)).degree v = 2 := by
  rw [cycleGraph_degree_two_le, Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

theorem pathGraph_le_cycleGraph {n : ℕ} : pathGraph n ≤ cycleGraph n := by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]

theorem cycleGraph_preconnected {n : ℕ} : (cycleGraph n).Preconnected :=
  (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

theorem cycleGraph_connected {n : ℕ} : (cycleGraph (n + 1)).Connected :=
  (pathGraph_connected n).mono pathGraph_le_cycleGraph

section cycle

set_option backward.privateInPublic true in
private def cycleGraph.cycleCons (n : ℕ) : ∀ m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Eulerian cycle of `cycleGraph (n + 3)` -/
def cycleGraph.cycle (n : ℕ) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle

private theorem cycleGraph.length_cycle_cons (n : ℕ) :
    ∀ m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph.cycleCons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph.cycleCons
    simp only [Walk.length_cons]
    rw [cycleGraph.length_cycle_cons n]

variable {n : ℕ}

@[simp, grind =]
theorem cycleGraph.length_cycle : (cycleGraph.cycle n).length = n + 3 := by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle

private theorem cycleGraph.getVert_cycleCons (m : Fin (n + 3)) (i : ℕ) (hi : i ≤ m.val) :
    (cycleGraph.cycleCons n m).getVert i = (m - i) % (n + 3) := by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]

theorem cycleGraph.getVert_cycle {m : ℕ} (hm : m ≤ n + 3) :
    (cycleGraph.cycle n).getVert m = ⟨(n + 3 - m) % (n + 3), Nat.mod_lt _ (by lia)⟩ := by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

theorem cycleGraph.isPath_tail_cycle : (cycleGraph.cycle n).tail.IsPath := by
  refine isPath_iff_injective_get_support _ |>.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

theorem cycleGraph.isCycle_cycle : (cycleGraph.cycle n).IsCycle :=
  isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

end cycle

section IsContained

variable {V : Type*} {G : SimpleGraph V}

lemma cycleGraph_isContained_iff {n : ℕ} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h' ↦ ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
    refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom <| cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (isCycle_map_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n ↦ p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x ≠ y := fun _ ↦ by simp_all
      wlog hle : x > y
      · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia) |>.symm
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
        exact p.isChain_adj_support.getElem _ _ |>.symm
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
      have := IsPath.mk' <| (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

/-

theorem cycles {k : ℕ} : (cycleGraph <| 2 * k + 1)ᶜ.cliqueNum = k + 1 := by
-/

#check indepNum
  #check cycleGraph
  #check Fin.isEmpty'
  #check uniqueOfSubsingleton

  #check Set.Iio
example {P : ℕ → Prop} : ∃ i, P i → ∀(n: ℕ), n = 0 ∨ n = 1 → P 0 ∨ P 1 := by
  aesop?
theorem cycleGraph_one_indepNum : (cycleGraph 1)ᶜ.cliqueNum = 1 := by{
  simp only [cliqueNum_compl, cycleGraph, indepNum]
  have thee : ∀(s : Finset (Fin 1)) , s = ∅ ∨ s = {0} := by
    intro s
    have : s.card ≤ 1 := card_finset_fin_le s
    have : s.card = 0 ∨ s.card = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp this 
    grind [Finset.card_eq_zero, Finset.card_eq_one]
  have the2 (n : ℕ): (∃ s , (⊥ :SimpleGraph (Fin 1)).IsNIndepSet n s )→  (⊥ :SimpleGraph (Fin 1)).IsNIndepSet n ∅ ∨ (⊥ :SimpleGraph (Fin 1)).IsNIndepSet n {0} := by
    intro h
    aesop
    rcases thee w with t|t
    aesop
    aesop
  have {n : ℕ}: (∃ s, (⊥ :SimpleGraph (Fin 1)).IsNIndepSet n s) ↔ (n= 0 ∨ n = 1) := by{
    constructor
    · intro h'
      obtain ⟨s,h'⟩ := h'
      have : s = {0} ∨ s = ∅ := by {
        have : s.card ≤ 1 := card_finset_fin_le s
        have : s.card = 0 ∨ s.card = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp this 
        grind [Finset.card_eq_zero, Finset.card_eq_one]
      }
      rcases this with this|this
      · rw [this] at h'
        have := h'.2
        simp at this
        grind
      · grind [isNIndepSet_iff]
    · intro h'
      rcases h' with h'|h'
      · use ∅
        rw [h'] ; simp [isNIndepSet_iff]
      · use {0}
        rw [h'] ; simp [isNIndepSet_iff]
}
  simp_all only
  have : {n | n = 0 ∨ n = 1} = {0,1} := by
    aesop
  rw [this]
  simp
}
#check cycleGraph_one_indepNum

theorem cycles {k : ℕ} (hk : k ≥ 1) : (cycleGraph <| 2 * k + 1)ᶜ.cliqueNum = k + 1 := by
  induction k
  sorry
  have : {n | ∃ s, (⊥ : SimpleGraph <| Fin 1).IsNIndepSet n s} = {0} := by
    ext x
    constructor
    intro h
    simp at h
    rcases h with ⟨s,h⟩
    simp
    sorry


  have t22223 : ∀(s : Finset (Fin 1)) , s = {0} ∨ s = ∅ := by
    intro s
    #check Fin.forall_fin_one
    have : s.card ≤ 1 := by{
      exact card_finset_fin_le s

    }
    #check Finset.card_eq_one
    have : s.card = 0 ∨ s.card = 1 := by
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp this 
    rw [Finset.card_eq_one,Finset.card_eq_zero] at this
    rcases this with this|this
    right ; assumption
    left 
    obtain ⟨a,this⟩ := this
    cases  a ; expose_names
    simp at isLt
    simp_all

     
  --have tttttt : ∀(n : ℕ) ( , ((⊥ : SimpleGraph (Fin 1)).IsNIndepSet n s)
  simp_all
  have {α : Type} : ((⊥ : SimpleGraph (α)).IsNIndepSet 0 ∅)  := by
  {
    rw [isNIndepSet_iff]
    constructor
    simp
    exact Finset.card_empty
  }
  have this2 {n : ℕ} (s : Finset (Fin 1) ) :  (⊥ : SimpleGraph <| Fin 1 ).IsNIndepSet (s.card) s  := by
    constructor
   -- intro h
    unfold IsIndepSet
    intro  ; simp
    have : s.card < 1 := by
      simp_all only [Finset.card_empty, Order.lt_one_iff]
    rfl

   


  rw [SimpleGraph.cycleGraph_one_eq_bot]
  unfold indepNum
  have {n : ℕ}: (∃ s, ( (⊥ : SimpleGraph (Fin 1)).IsNIndepSet n s)) ↔ n = 0 := by
    constructor
    intro h
    obtain ⟨s,h⟩ := h
    have := h.card_eq
    have this2 := h.isIndepSet 
    unfold IsIndepSet at this2
    have helper : (⊥ : SimpleGraph (Fin 1)) = (⊤ : SimpleGraph (Fin 1)) := by {
      ext v w
      simp?
      #check Fin
      exact Subsingleton.elim v w
    }

    simp at this2

    sorry
    intro h
    rw [h]
    use ∅
    constructor
    unfold IsIndepSet
    have : ∀(u v), ¬(⊥ : SimpleGraph (Fin 1)).Adj u v := by
      intro u v
      exact (disjoint_edge ⊥).mp fun ⦃x⦄ a a_1 => a

    simp only [Finset.coe_empty, Set.pairwise_empty] 
    exact Finset.card_empty
  sorry

end IsContained

end SimpleGraph
