/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Order.CompletePartialOrder

/-!
# The Girth-Diameter Inequality

In this file we prove that for any connected finite graph `G`, we have `G.girth ≤ 2 * G.ediam + 1`.

Although the proof formalization is completed, this file is still in progress as I polish the
styling, ideally I want to put the main result in `girth.lean` instead of creating this file.

-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

@[simp]
lemma Walk.drop_length {u v : V} (p : G.Walk u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]

lemma Walk.drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]

lemma take_support_sublist_succ {u v} (p : G.Walk u v) (n : ℕ) :
    (p.take n).support.Sublist (p.take (n + 1)).support := by
  induction n generalizing p u with
  | zero => cases p <;> simp [Walk.take]
  | succ _ ih => cases p <;> simp [Walk.take, ih]

lemma drop_support_sublist_succ {u v} (p : G.Walk u v) (n : ℕ) :
    (p.drop (n + 1)).support.Sublist (p.drop n).support := by
  induction n generalizing p u with
  | zero =>
    rw [Walk.drop_zero, ← Walk.tail]
    cases p <;> simp
  | succ _ ih => cases p <;> simp [Walk.drop, ih]

lemma take_support_sublist_le {u v n k} (p : G.Walk u v) (h : n ≤ k) :
    (p.take n).support.Sublist (p.take k).support := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  induction t with
  | zero => rfl
  | succ t ih => exact (ih (n.le_add_right t)).trans <| take_support_sublist_succ p (n + t)

lemma drop_support_sublist_le {u v n k} (p : G.Walk u v) (h : n ≤ k) :
    (p.drop k).support.Sublist (p.drop n).support := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  induction t with
  | zero => rfl
  | succ t ih => exact (drop_support_sublist_succ p (n + t)).trans <| ih (n.le_add_right t)

lemma take_length_le {u v n} {p : G.Walk u v} (h : p.length ≤ n) :
    p.take n = p.copy rfl (p.getVert_of_length_le h).symm := by
  induction n generalizing p u with
  | zero => cases p <;> simp [Walk.take] at h ⊢
  | succ n ih =>
    cases p
    · simp [Walk.take]
    rw [Walk.length_cons, add_le_add_iff_right] at h
    simp [Walk.take, ih h]

lemma drop_length_le {u v n} {p : G.Walk u v} (h : p.length ≤ n) :
    p.drop n = Walk.nil.copy (p.getVert_of_length_le h).symm rfl := by
  induction n generalizing p u with
  | zero => cases p <;> simp [Walk.drop] at h ⊢
  | succ n ih =>
    cases p
    · simp [Walk.drop]
    rw [Walk.length_cons, add_le_add_iff_right] at h
    simp [Walk.drop, ih h]

lemma take_support_sublist {u v n} (p : G.Walk u v) :
    (p.take n).support.Sublist p.support := by
  by_cases h : n ≤ p.length
  · have : p.support = (p.take p.length).support := by simp [take_length_le le_rfl]
    exact this ▸ take_support_sublist_le p h
  simp [take_length_le (not_le.mp h).le]

lemma drop_support_sublist {u v n} (p : G.Walk u v) :
    (p.drop n).support.Sublist p.support := by
  by_cases h : n ≤ p.length
  · have : p.support = (p.drop 0).support := by cases p <;> simp [Walk.drop]
    exact this ▸ drop_support_sublist_le p n.zero_le
  simp [drop_length_le (not_le.mp h).le]

lemma Walk.IsPath.take_isPath_le {u v n k} {p : G.Walk u v} (h : (p.take k).IsPath) (hle : n ≤ k) :
    (p.take n).IsPath := by
  rw [Walk.isPath_def] at h ⊢
  exact (take_support_sublist_le p hle).nodup h

lemma Walk.IsPath.drop_isPath_le {u v n k} {p : G.Walk u v} (h : (p.drop k).IsPath) (hle : k ≤ n) :
    (p.drop n).IsPath := by
  rw [Walk.isPath_def] at h ⊢
  exact (drop_support_sublist_le p hle).nodup h

lemma Walk.IsPath.take_isPath {u v} {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.take n).IsPath := by
  cases le_or_gt n p.length with
  | inl hp =>
    have : (p.take p.length).IsPath := by simpa [take_length_le rfl.le]
    exact this.take_isPath_le hp
  | inr hp => simpa [take_length_le hp.le]

lemma Walk.IsPath.drop_isPath {u v} {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath := by
  have : (p.drop 0).IsPath := by rwa [Walk.drop_zero, isPath_copy]
  exact this.drop_isPath_le n.zero_le

lemma Walk.dropLast_support_concat_eq_support {u v} {p : G.Walk u v} (h : ¬ p.Nil) :
    p.dropLast.support.concat v = p.support := by
  simp_rw [← support_concat _ (adj_penultimate h), ← p.concat_dropLast (adj_penultimate h)]

lemma Walk.tail_length {u v} (p : G.Walk u v) :
    p.tail.length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons => simp

lemma IsCycle.tail_not_nil {u} {p : G.Walk u u} (h : p.IsCycle) :
    ¬ p.tail.Nil := by
  rw [Walk.nil_iff_length_eq]
  apply Nat.ne_zero_of_lt (b := 1)
  have := h.three_le_length
  rw [← Walk.length_tail_add_one h.not_nil] at this
  omega

lemma Walk.cons_dropLast {u v w} (p : G.Walk u v) (hp : ¬ p.Nil) (h : G.Adj w u) :
    cons h p.dropLast = (cons h p).dropLast.copy rfl (p.penultimate_cons_of_not_nil h hp) := by
  cases p <;> simp at hp ⊢

lemma IsCycle.dropLast_isPath {u} {p : G.Walk u u} (h : p.IsCycle) :
    p.dropLast.IsPath := by
  let L := p.tail.dropLast.support
  have hu : L.concat u = p.tail.support := by
    simp only [L]
    rw [Walk.dropLast_support_concat_eq_support]
    exact tail_not_nil h
  have hL : u :: L = p.dropLast.support := by
    rw [← Walk.support_cons, Walk.cons_dropLast, Walk.support_copy, p.cons_tail_eq h.not_nil]
    exact tail_not_nil h
  rw [Walk.isPath_def, ← hL]
  apply (L.concat_perm u).nodup
  rw [hu, Walk.support_tail_of_not_nil _ h.not_nil]
  exact h.support_nodup

lemma IsCycle.take_isPath_of_lt_length {u n} {p : G.Walk u u} (hp : p.IsCycle) (h : n < p.length) :
    (p.take n).IsPath := by
  have h : (p.take n).support.Sublist (p.dropLast).support := by
    rw [Walk.dropLast]
    exact take_support_sublist_le p (Nat.le_sub_one_of_lt h)
  rw [Walk.isPath_def]
  apply h.nodup
  rw [← Walk.isPath_def]
  exact IsCycle.dropLast_isPath hp

lemma Walk.take_le_length {u v} {p : G.Walk u v} (n : ℕ) (hl : n ≤ p.length) :
    (p.take n).length = n := by
  induction p generalizing n with
  | nil =>
    rw [length_nil, nonpos_iff_eq_zero] at hl
    simp [hl, take]
  | cons ha p ih =>
    cases n with
    | zero => simp [take]
    | succ n =>
      rw [length_cons, add_le_add_iff_right] at hl
      simp [take, ih n hl]

lemma Walk.take_length {u v} {p : G.Walk u v} (n : ℕ) :
    (p.take n).length = n ⊓ p.length := by
  cases lt_or_ge n p.length with
  | inl hl => rw [min_eq_left_of_lt hl, take_le_length n hl.le]
  | inr hl => rwa [take_length_le hl, Walk.length_copy, right_eq_inf]

lemma Walk.exists_getVert_ne_of_ne {u v} {p q : G.Walk u v} (h : p ≠ q) :
    ∃ k, p.getVert k ≠ q.getVert k := by
  contrapose! h
  exact ext_getVert h

lemma diam_le_ediam : G.diam ≤ G.ediam :=
  G.ediam.coe_toNat_le_self

lemma Walk.IsPath.getVert_eq_iff_eq {u v} {p : G.Walk u v} (hp : p.IsPath) {n k} (hn : n ≤ p.length)
    (hk : k ≤ p.length) (h : p.getVert n = p.getVert k) :
    n = k :=
  hp.getVert_injOn hn hk h

lemma Walk.exists_getVert_succ_of_edges_mem {u v a b} (p : G.Walk u v) (h : s(a, b) ∈ p.edges) :
    ∃ n < p.length, a = p.getVert n ∧ b = p.getVert (n + 1) ∨
      a = p.getVert (n + 1) ∧ b = p.getVert n := by
  induction p with
  | nil => simp at h
  | cons ha p ih =>
    simp at h
    cases h with
    | inl h =>
      use 0
      simpa
    | inr h =>
      obtain ⟨n, hn⟩ := ih h
      use n + 1
      simpa

lemma mk_isCycle_adj_isPath_one_lt_length {u v} {p : G.Walk u v} (hadj : G.Adj u v) (h : p.IsPath)
    (hp: 1 < p.length) :
    (p.cons hadj.symm).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  apply And.intro h
  intro hvu
  apply Walk.exists_getVert_succ_of_edges_mem at hvu
  obtain ⟨n, hl, hn⟩ := hvu
  cases hn with
  | inl hn =>
    obtain ⟨hn₁, hn₂⟩ := hn
    nth_rw 1 [← p.getVert_zero] at hn₂
    apply h.getVert_injOn (by simp) at hn₂
    · simp at hn₂
    simpa
  | inr hn =>
    have : n = 0 := by
      apply h.getVert_injOn (Set.mem_setOf_eq ▸ hl.le) (Set.mem_setOf_eq ▸ zero_le _)
      rw [p.getVert_zero, ← hn.2]
    simp only [this, zero_add, Walk.getVert_zero, and_true] at hn
    have : p.length = 1 := by
      apply h.getVert_injOn (Set.mem_setOf_eq ▸ rfl.le) (Set.mem_setOf_eq ▸ hp.le)
      rwa [p.getVert_length]
    rw [this] at hp
    contradiction

lemma Walk.drop_getVert {u v} (p : G.Walk u v) (i j : ℕ) :
    (p.drop i).getVert j = p.getVert (j + i) := by
  induction p generalizing i with
  | nil => simp [drop]
  | cons ha p ih =>
    cases i with
    | zero => simp [drop]
    | succ i =>
      simp_rw [getVert_cons_succ, drop]
      exact ih i

lemma Walk.take_getVert {u v} (p : G.Walk u v) (n m : ℕ) :
    (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m with
  | nil => simp [take]
  | cons => cases n <;> cases m <;> simp_all [take]

lemma isAcyclic_of_subsingleton [Subsingleton V] :
    G.IsAcyclic := by
  intro v w
  by_contra h
  have heq := subsingleton_iff.mp ‹_›
  have h₁ := w.tail.getVert_eq_support_getElem? <| Nat.zero_le _
  have h₂ := Walk.tail_length _ ▸ w.tail.getVert_eq_support_getElem? rfl.le
  suffices w.tail.support[0]? = w.tail.support[w.length - 1]? by
    rw [Walk.support_tail_of_not_nil _ h.not_nil] at this
    apply List.getElem?_inj (by
      simp only [List.length_tail, Walk.length_support, add_tsub_cancel_right]
      exact lt_of_lt_of_le (show 0 < 3 by decide) h.three_le_length) h.support_nodup at this
    symm at this
    apply Nat.le_of_sub_eq_zero at this
    have := h.three_le_length.trans this
    contradiction
  rw [← h₁, ← h₂]
  simp only [Walk.getVert_zero, Walk.getVert_tail, Option.some.injEq]
  rw [Nat.sub_add_cancel ((show 1 ≤ 3 by decide).trans h.three_le_length)]
  exact heq _ _

lemma Walk.IsTrail.append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail) (h_disjoint : p.edges.Disjoint q.edges) :
    (p.append q).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
  exact ⟨hp.edges_nodup, hq.edges_nodup, fun _ x _ y ↦ ne_of_mem_of_not_mem x (h_disjoint.symm y)⟩

lemma Walk.IsPath.mem_edge_mem_support_tail {u v a b : V} {p : G.Walk u v} (hp : p.IsPath)
    (he : s(a, b) ∈ p.edges) :
    a ∈ p.support.tail ∨ b ∈ p.support.tail := by
  induction p with
  | nil => simp at he
  | cons ha p ih =>
    simp only [support_cons, List.tail_cons]
    simp only [edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at he
    rcases he with ⟨he | he⟩ | he
    · simp [he.2]
    · simp [he.1]
    · exact Or.inl <| fst_mem_support_of_mem_edges p he

lemma Walk.edge_getVert {u v a b} (p : G.Walk u v) (h : s(a, b) ∈ p.edges) :
    ∃ k < p.length, a = p.getVert k ∧ b = p.getVert k.succ ∨
      b = p.getVert k ∧ a = p.getVert k.succ:= by
  induction p with
  | nil => simp at h
  | cons ha p ih =>
    simp at h
    cases h with
    | inl h => cases h with
      | inl h =>
        use 0
        simp only [length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt,
          or_true, getVert_zero, Nat.succ_eq_add_one, zero_add, getVert_cons_succ, true_and]
        apply Or.inl
        simp [h.1, h.2]
      | inr h =>
        use 0
        simp only [length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt,
          or_true, getVert_zero, Nat.succ_eq_add_one, zero_add, getVert_cons_succ, true_and]
        apply Or.inr
        simp [h.1, h.2]
    | inr h =>
      obtain ⟨k, h, hk⟩ := ih h
      cases hk with
      | inl hk =>
        use k + 1
        apply And.intro
        · simp only [length_cons, add_lt_add_iff_right]
          omega
        apply Or.inl
        simpa
      | inr hk =>
        use k + 1
        apply And.intro
        · simp only [length_cons, add_lt_add_iff_right]
          omega
        apply Or.inr
        simpa

lemma List.mem_tail {α k} (L : List α) (h : 0 < k) (hk : k < L.length) :
    L[k]'hk ∈ L.tail := by
  induction L with
  | nil => simp at hk
  | cons a L ih =>
    conv_rhs =>
      lhs
      rw [(Nat.sub_eq_iff_eq_add h).mp rfl]
    simp

lemma Walk.IsPath.exists_of_edges {u v a b : V} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hep : s(a, b) ∈ p.edges) (heq : s(a, b) ∈ q.edges) (hl : 1 < p.length) :
    ∃ z, z ∈ p.support.tail ∧ z ∈ q.support.tail := by
  apply Walk.edge_getVert at hep
  apply Walk.edge_getVert at heq
  obtain ⟨k₁, hl₁, h₁⟩ := hep
  obtain ⟨k₂, hl₂, h₂⟩ := heq
  cases h₁ with
  | inl h₁ => cases h₂ with
    | inl h₂ =>
      use b
      nth_rw 1 [h₁.2]
      nth_rw 1 [h₂.2]
      simp only [Nat.succ_eq_add_one]
      apply And.intro
      · rw [p.getVert_eq_support_getElem hl₁]
        apply List.mem_tail
        exact Nat.zero_lt_succ k₁
      · rw [q.getVert_eq_support_getElem hl₂]
        apply List.mem_tail
        exact Nat.zero_lt_succ k₂
    | inr h₂ =>
      cases k₁
      · simp only [getVert_zero, Nat.succ_eq_add_one, zero_add] at h₁
        use b
        apply And.intro
        · rw [h₁.2, p.getVert_eq_support_getElem hl₁]
          exact List.mem_tail _ Nat.one_pos _
        · cases k₂
          · simp only [getVert_zero, Nat.succ_eq_add_one, zero_add] at h₂
            have : v = p.getVert p.length := (getVert_length p).symm
            nth_rw 1 [← h₂.1, h₁.2] at this
            apply hp.getVert_injOn hl.le (by simp) at this
            rw [← this] at hl
            contradiction
          rw [h₂.1, q.getVert_eq_support_getElem hl₂.le]
          apply List.mem_tail
          simp
      use a
      nth_rw 1 [h₁.1, h₂.2]
      apply And.intro
      · rw [p.getVert_eq_support_getElem hl₁.le]
        apply List.mem_tail
        simp
      rw [q.getVert_eq_support_getElem hl₂]
      apply List.mem_tail
      simp
  | inr h₁ => cases h₂ with
    | inl h₂ =>
      cases k₁
      · use a
        simp only [getVert_zero, Nat.succ_eq_add_one, zero_add] at h₁
        apply And.intro
        · rw [h₁.2, p.getVert_eq_support_getElem hl₁]
          apply List.mem_tail
          simp
        cases k₂
        · simp only [getVert_zero, Nat.succ_eq_add_one, zero_add] at h₂
          obtain ⟨_, h₁⟩ := h₁
          nth_rw 1 [h₂.1, ← p.getVert_length] at h₁
          apply hp.getVert_injOn (by simp) hl.le at h₁
          rw [h₁] at hl
          contradiction
        rw [h₂.1, q.getVert_eq_support_getElem hl₂.le]
        apply List.mem_tail
        simp
      use b
      nth_rw 1 [h₁.1, h₂.2]
      apply And.intro
      · rw [p.getVert_eq_support_getElem hl₁.le]
        apply List.mem_tail
        simp
      rw [q.getVert_eq_support_getElem hl₂]
      apply List.mem_tail
      simp
    | inr h₂ =>
      use a
      nth_rw 1 [h₁.2, h₂.2]
      apply And.intro
      · rw [p.getVert_eq_support_getElem hl₁]
        apply List.mem_tail
        simp
      rw [q.getVert_eq_support_getElem hl₂]
      apply List.mem_tail
      simp

lemma isPath_append_isCycle {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · apply Walk.IsTrail.append hp.toIsTrail hq.toIsTrail
    intro x h₁ h₂
    have : ∃ a b, x = s(a, b) := ⟨x.out.1, x.out.2, Prod.mk.eta ▸ (Quot.out_eq x).symm⟩
    obtain ⟨a, b, hx⟩ := this
    subst hx
    obtain ⟨z, hz₁, hz₂⟩ := Walk.IsPath.exists_of_edges hp h₁ h₂ hn
    exact h hz₁ hz₂
  · rw [ne_eq, ← Walk.nil_iff_eq_nil, Walk.not_nil_iff_lt_length, Walk.length_append]
    omega
  · rw [Walk.tail_support_append, List.nodup_append]
    exact ⟨p.support.tail_sublist.nodup (p.isPath_def.mp hp), q.support.tail_sublist.nodup
      (q.isPath_def.mp hq), fun _ x _ y ↦ ne_of_mem_of_not_mem x (h.symm y)⟩

lemma Walk.mem_take_support {u v x n} {p : G.Walk u v} (h : x ∈ (p.take n).support) :
    ∃ k, k ≤ n ∧ x = p.getVert k := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨k, h₁, h₂⟩ := h
  cases le_or_gt n p.length with
  | inl hn =>
    rw [length_support, take_length, inf_of_le_left hn] at h₁
    rw [← Walk.getVert_eq_support_getElem, Walk.take_getVert, inf_of_le_right
      (Nat.le_of_lt_succ h₁)] at h₂
    · use k, Nat.le_of_lt_succ h₁, h₂.symm
    rw [take_length, inf_of_le_left hn]
    exact Nat.le_of_lt_succ h₁
  | inr hn =>
    rw [length_support, take_length, inf_of_le_right hn.le] at h₁
    rw [← Walk.getVert_eq_support_getElem, Walk.take_getVert, inf_of_le_right
      (h₁.le.trans hn)] at h₂
    · use k, h₁.le.trans hn, h₂.symm
    rw [take_length, inf_of_le_right hn.le]
    exact Nat.le_of_lt_succ h₁

lemma List.mem_tail_nodup {α a} {L : List α} (h : a ∈ L.tail) (hL : L.Nodup) :
    a ∈ L ∧ a ≠ L[0]'(L.length_pos_iff.mpr (L.ne_nil_of_mem (L.mem_of_mem_tail h))) := by
  induction L with
  | nil =>
    simp at h
  | cons b hb ih =>
    simp only [List.mem_cons, List.getElem_cons_zero, ne_eq]
    by_contra hc
    rw [not_and_or] at hc
    cases hc with
    | inl hc =>
      rw [not_or] at hc
      exact hc.2 h
    | inr hc =>
      rw [not_not] at hc
      rw [hc, List.tail_cons] at h
      rw [List.nodup_cons] at hL
      exact hL.1 h

lemma List.mem_dropLast_nodup {α a} {L : List α} (h : a ∈ L.dropLast) (hL : L.Nodup) :
    a ∈ L ∧
    a ≠ L.getLast ((ne_of_apply_ne List.dropLast fun a ↦ (List.ne_nil_of_mem h) a.symm).symm) := by
  apply And.intro
  · exact List.mem_of_mem_dropLast h
  by_contra! hc
  have : L = L.dropLast ++ [a] := by rw [hc, List.dropLast_concat_getLast]
  rw [this, List.nodup_append] at hL
  obtain ⟨_, _, hL⟩ := hL
  rw [← List.disjoint_iff_ne, List.disjoint_singleton] at hL
  exact hL h

section takeAt

/-- The walk obtained by taking the `j` darts of a walk after `i` darts. -/
def Walk.takeAt {u v} (p : G.Walk u v) {i j : ℕ} (h : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl <| by rw [p.drop_getVert i (j - i), Nat.sub_add_cancel h]

lemma Walk.IsPath.takeAt_isPath {u v} {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ} (h : i ≤ j) :
    (p.takeAt h).IsPath := by
  simp only [takeAt, isPath_copy]
  exact (drop_isPath hp i).take_isPath (j - i)

lemma Walk.takeAt_length_le {u v} (p : G.Walk u v) {i j : ℕ} (h : i ≤ j) :
    (p.takeAt h).length ≤ p.length := by
  simp [takeAt, Walk.take_length]

lemma Walk.takeAt_length {u v} (p : G.Walk u v) {i j : ℕ} (h : i ≤ j) :
    (p.takeAt h).length = min j p.length - i := by
  rw [takeAt, length_copy, take_length, drop_length, j.sub_min_sub_right p.length i]

lemma Walk.mem_takeAt_support {u v x} {p : G.Walk u v} {i j : ℕ} {h : i ≤ j}
    (hx : x ∈ (p.takeAt h).support) :
    ∃ k ∈ Finset.Icc i j, x = p.getVert k := by
  simp_rw [Finset.mem_Icc]
  rw [takeAt, support_copy] at hx
  apply mem_take_support at hx
  simp_rw [drop_getVert] at hx
  obtain ⟨k, h₁, h₂⟩ := hx
  use i + k, ⟨i.le_add_right k, (Nat.le_sub_iff_add_le' h).mp h₁⟩
  rwa [add_comm]

lemma Walk.takeAt_support_sublist {u v} (p : G.Walk u v) {i j : ℕ} (h : i ≤ j) :
    (p.takeAt h).support.Sublist p.support := by
  have : (p.takeAt h).support.Sublist (p.drop i).support := by
    simp only [takeAt, support_copy]
    exact take_support_sublist (p.drop i)
  exact this.trans (drop_support_sublist p)

lemma Walk.mem_support_of_mem_takeAt_support {u v x} {p : G.Walk u v} {i j : ℕ} {h : i ≤ j}
    (hx : x ∈ (p.takeAt h).support) :
    x ∈ p.support :=
  (p.takeAt_support_sublist h).mem hx

end takeAt

variable [Nonempty V] [Finite V]

theorem egirth_le_two_mul_girth_add_one (h : ¬ G.IsAcyclic) (hc : G.Connected) :
    G.egirth ≤ 2 * G.ediam + 1 := by
  by_cases h₀ : G.ediam = 0
  · rw [ediam_eq_zero_iff_subsingleton] at h₀
    exact (h isAcyclic_of_subsingleton).elim
  by_contra hf
  obtain ⟨x₀, w, hw₁, hw₂⟩ := exists_egirth_eq_length.mpr h
  rw [not_le] at hf
  suffices ∃ x₀, ∃ c : G.Walk x₀ x₀, c.IsCycle ∧ c.length < G.egirth by
    obtain ⟨_, _, hw, h⟩ := this
    exact not_le.mpr h <| egirth_le_length hw
  let pw := w.take (G.diam + 1)
  have diam_lt_w_length : G.diam + 1 < w.length := calc
    G.diam + 1 ≤ 2 * G.diam + 1 := two_mul G.diam ▸ (G.diam + 1).le_add_left G.diam
    _ < _ := ENat.coe_lt_coe.mp (lt_of_le_of_lt (add_le_add
      (mul_le_mul_left' G.ediam.coe_toNat_le_self 2) rfl.le) (hw₂ ▸ hf))
  have pw_length : pw.length = G.diam + 1 := by
    rw [Walk.take_length]
    simpa using Nat.le_of_succ_le diam_lt_w_length
  let t := G.dist x₀ (w.getVert (G.diam + 1))
  obtain ⟨p, hp₁, hp₂⟩ := hc.exists_path_of_dist x₀ (w.getVert (G.diam + 1))
  have t_le_diam : t ≤ G.diam := dist_le_diam <| connected_iff_ediam_ne_top.mp hc
  have p_t_eq_pw_diam_succ : p.getVert t = pw.getVert (G.diam + 1) := by
    rw [p.getVert_of_length_le hp₂.le, pw.getVert_of_length_le]
    rw [Walk.take_le_length]
    exact diam_lt_w_length.le
  have pw_isPath : pw.IsPath := IsCycle.take_isPath_of_lt_length hw₁ diam_lt_w_length
  let S : Set ℕ := {n | p.getVert n ≠ pw.getVert n}
  have p_length_lt_pw_length : p.length < pw.length := by
      apply lt_of_le_of_lt (le_of_eq_of_le hp₂ t_le_diam)
      rw [Walk.take_le_length, lt_add_iff_pos_right, Nat.lt_one_iff]
      rw [hw₂] at hf
      exact diam_lt_w_length.le
  have S_nonempty : S.Nonempty := by
    apply Walk.exists_getVert_ne_of_ne
    exact fun a ↦ p_length_lt_pw_length.ne (congrArg Walk.length a)
  let j := WellFounded.min Nat.lt_wfRel.wf S S_nonempty
  have j_in_S : j ∈ S := WellFounded.min_mem WellFoundedRelation.wf S S_nonempty
  have j_min (m : ℕ) (h : m ∈ S) : j ≤ m := WellFounded.min_le _ h S_nonempty
  have lt_j {i} (h : i < j) : p.getVert i = pw.getVert i := by
    contrapose! h
    exact j_min i h
  have j_pos : 0 < j := by
    by_contra!
    rw [nonpos_iff_eq_zero] at this
    rw [Set.mem_setOf, this] at j_in_S
    simp at j_in_S
  have j_lt_t : j < t := by
    by_contra ht
    rw [not_lt] at ht
    cases ht.lt_or_eq with
    | inl ht =>
      have : pw.getVert t = pw.getVert (G.diam + 1) := by
        rw [← p_t_eq_pw_diam_succ, lt_j ht]
      apply Walk.IsPath.getVert_eq_iff_eq pw_isPath (dist_le pw) at this
      · omega
      · apply le_of_eq
        rw [Walk.take_le_length]
        exact diam_lt_w_length.le
    | inr ht =>
      -- create a cycle strictly smaller than the girth like this:
      /-
          p.getVert (t - 1) ------ p.getVert t
            \                        \
             \                        \
            (pw.getVert t) -- ... -- (pw.getVert G.diam)
      -/
      have : (pw.drop (t - 1)).IsPath := by
        have : (pw.copy (pw.getVert_zero).symm rfl).IsPath := by rwa [Walk.isPath_copy]
        rw [← pw.drop_zero] at this
        exact this.drop_isPath_le (t - 1).zero_le
      have hl : 1 < (pw.drop (t - 1)).length := by
        have ha : G.Adj (pw.getVert (t - 1)) (pw.getVert t) := by
          nth_rw 2 [← t.sub_add_cancel (ht ▸ j_pos)]
          apply Walk.adj_getVert_succ
          omega
        have : (pw.drop (t - 1)).length = ((pw.drop t).cons ha).length := by
          simp only [Walk.drop_length, Walk.length_cons]
          omega
        rw [this]
        simpa [t] using hp₂ ▸ p_length_lt_pw_length
      have hadj : G.Adj (pw.getVert (t - 1)) (w.getVert (G.diam + 1)) := by
        have p_t : p.getVert t = w.getVert (G.diam + 1) := by
          rw [p_t_eq_pw_diam_succ, Walk.take_getVert, min_self]
        have : G.Adj (p.getVert (t - 1)) (p.getVert t) := by
          nth_rw 2 [← t.sub_add_cancel (ht ▸ j_pos)]
          apply Walk.adj_getVert_succ
          omega
        rw [← ht] at lt_j
        specialize lt_j (i := t - 1) <| by omega
        rwa [p_t, lt_j] at this
      have := mk_isCycle_adj_isPath_one_lt_length hadj this hl
      have hlen : ((pw.drop (t - 1)).cons hadj.symm).length < G.egirth := by
        simp only [Walk.length_cons, Walk.drop_length]
        have : pw.length - (t - 1) + 1 ≤ 2 * G.diam + 1 := calc
          pw.length - (t - 1) + 1 = G.diam + 1 - t + 2 := by
            simp only [Nat.add_right_cancel_iff, pw, Walk.take_length]
            omega
          _ ≤ G.diam + 2 := by omega
          _ ≤ _ := by omega
        rw [← ENat.coe_le_coe] at this
        apply lt_of_le_of_lt this
        push_cast
        have : 2 * ↑G.diam + 1 ≤ 2 * G.ediam + 1 := by
          apply add_le_add ?_ rfl.le
          simp [diam_le_ediam]
        apply lt_of_le_of_lt this
        assumption
      apply G.egirth_le_length at this
      rw [← not_lt] at this
      exact this hlen
  let S' : Set ℕ := {k | j < k ∧ p.getVert k ∈ pw.support}
  have S'_nonempty : S'.Nonempty := by
    use t
    apply And.intro j_lt_t
    rw [p_t_eq_pw_diam_succ]
    exact pw.getVert_mem_support (G.diam + 1)
  let k := WellFounded.min Nat.lt_wfRel.wf S' S'_nonempty
  have k_in_S' : k ∈ S' := WellFounded.min_mem WellFoundedRelation.wf S' S'_nonempty
  have k_min (m : ℕ) (h : m ∈ S') : k ≤ m := WellFounded.min_le _ h S'_nonempty
  have ioo_j_k {i} (h' : j < i) (h : i < k) : p.getVert i ∉ pw.support := by
    contrapose! h
    apply k_min
    rw [Set.mem_setOf]
    exact ⟨h', h⟩
  have k_le_t : k ≤ t := by
    apply k_min
    apply And.intro j_lt_t
    rw [p_t_eq_pw_diam_succ]
    exact pw.getVert_mem_support (G.diam + 1)
  have : ∃ m ≤ G.diam + 1, p.getVert k = pw.getVert m := by
    obtain ⟨_, h⟩ := Set.mem_setOf.mp k_in_S'
    simp_rw [← pw_length]
    rw [List.mem_iff_getElem] at h
    obtain ⟨n, hn, h⟩ := h
    rw [Walk.length_support] at hn
    rw [← Walk.getVert_eq_support_getElem _ (Nat.le_of_lt_succ hn)] at h
    use n, Nat.le_of_lt_succ hn, h.symm
  obtain ⟨m, hm₁, hm₂⟩ := this
  have j_lt_k : j < k := Set.mem_setOf.mp k_in_S'.1
  have j_le_m : j ≤ m := by
    by_contra! hmj
    rw [← lt_j hmj] at hm₂
    have : k ≤ p.length := by
      apply k_min
      rw [Set.mem_setOf]
      exact And.intro (Nat.lt_of_lt_of_eq j_lt_t hp₂.symm) <| by simp
    apply Walk.IsPath.getVert_injOn hp₁ this (lt_of_lt_of_le (hmj.trans j_lt_k) this).le at hm₂
    exact (hmj.trans j_lt_k).ne hm₂.symm
  let Cp : G.Walk (p.getVert (j - 1)) (p.getVert k) :=
    p.takeAt (lt_of_le_of_lt (j.sub_le 1) j_lt_k).le
  have Cp_isPath : Cp.IsPath := hp₁.takeAt_isPath (lt_of_le_of_lt (Nat.sub_le j 1) j_lt_k).le
  have Cp_length : Cp.length ≤ p.length :=
    p.takeAt_length_le (lt_of_le_of_lt (j.sub_le 1) j_lt_k).le
  let Cpw : G.Walk (p.getVert k) (p.getVert (j - 1)) :=
    (pw.takeAt ((j.sub_le 1).trans j_le_m)).reverse.copy hm₂.symm <| by
      rw [lt_j]
      simpa
  have Cpw_isPath : Cpw.IsPath := by
    rw [Walk.isPath_copy, Walk.isPath_reverse_iff]
    exact pw_isPath.takeAt_isPath ((j.sub_le 1).trans j_le_m)
  have Cpw_length : Cpw.length ≤ pw.length := by
    rw [Walk.length_copy, Walk.length_reverse]
    exact pw.takeAt_length_le ((j.sub_le 1).trans j_le_m)
  by_cases hj_mem : p.getVert j ∈ pw.support
  -- create a cycle strictly smaller than the girth like this:
  /-
      p.getVert (j - 1) ------ p.getVert j
        \                        \
         \                        \
        (pw.getVert j) -- ... -- (pw.getVert i - 1)
  -/
  · rw [List.mem_iff_getElem] at hj_mem
    obtain ⟨i, hi₁, hi₂⟩ := hj_mem
    rw [Walk.length_support] at hi₁
    rw [← Walk.getVert_eq_support_getElem _ (Nat.le_of_lt_succ hi₁)] at hi₂
    have hji : j < i := by
      apply lt_of_le_of_ne
      · by_contra! hc
        specialize lt_j hc
        rw [hi₂] at lt_j
        apply hp₁.getVert_injOn at lt_j
        · exact hc.ne lt_j
        · rw [Set.mem_setOf]
          apply le_of_lt
          apply lt_of_lt_of_le hc
          rw [hp₂]
          exact (lt_of_lt_of_le j_lt_k k_le_t).le
        rw [hp₂, Set.mem_setOf_eq]
        exact (lt_of_lt_of_le j_lt_k k_le_t).le
      contrapose! hi₂
      rw [← hi₂]
      rw [Set.mem_setOf] at j_in_S
      exact j_in_S.symm
    have hji_pred : j - 1 < i := lt_of_le_of_lt (j.sub_le 1) hji
    let c : G.Walk (pw.getVert (j - 1)) (pw.getVert i) := pw.takeAt hji_pred.le
    have path : c.IsPath := pw_isPath.takeAt_isPath hji_pred.le
    have length : 1 < c.length := by
      rw [Walk.takeAt_length, inf_of_le_left (Nat.le_of_lt_succ hi₁)]
      omega
    have adj : G.Adj (pw.getVert (j - 1)) (pw.getVert i) := by
      rw [hi₂, ← lt_j (Nat.sub_one_lt_of_lt j_pos)]
      nth_rw 2 [ ← Nat.sub_add_cancel j_pos]
      rw [Nat.succ_eq_add_one, zero_add]
      apply p.adj_getVert_succ
      omega
    have := mk_isCycle_adj_isPath_one_lt_length adj path length
    use pw.getVert i, Walk.cons adj.symm c, this
    simp only [Walk.length_cons]
    have h₁ : c.length + 1 ≤ G.diam + 1 + 1 :=
      add_le_add ((pw.takeAt_length_le hji_pred.le).trans pw_length.le) rfl.le
    have h₂ : G.diam + 1 + 1 ≤ 2 * G.diam + 1 := by omega
    have h₃ : 2 * G.diam + 1 ≤ 2 * G.ediam + 1 := by
      apply add_le_add ?_ rfl.le
      simp [diam_le_ediam]
    apply lt_of_le_of_lt ?_ hf
    apply le_trans ?_ h₃
    norm_cast
    exact h₁.trans h₂
  have Cp_tail_not_in_Cpw_tail : ∀ x, x ∈ Cp.support.tail → x ∉ Cpw.support.tail := by
    intro x hx
    dsimp [Cp, Cpw] at hx ⊢
    simp only [Walk.support_copy, Walk.support_reverse, List.tail_reverse, List.mem_reverse]
    apply List.mem_tail_nodup at hx
    obtain ⟨h₁, h₂⟩ := hx Cp_isPath.support_nodup
    apply Walk.mem_takeAt_support at h₁
    obtain ⟨i, hi₁, hi₂⟩ := h₁
    intro hc
    apply List.mem_dropLast_nodup at hc
    specialize hc <| by
      have := Cpw_isPath.support_nodup
      simp only [Walk.support_copy, Walk.support_reverse, List.nodup_reverse, Cpw] at this
      exact this
    obtain ⟨h₃, h₄⟩ := hc
    by_cases hik : i = k
    · simp only [Walk.getLast_support, ne_eq] at h₄
      rw [hik] at hi₂
      rw [hi₂] at h₄
      exact h₄ hm₂
    have : i < k := lt_of_le_of_ne (Finset.mem_Icc.mp hi₁).2 hik
    have := ioo_j_k (i := i)
    specialize this <| by
      apply lt_of_le_of_ne
      · rw [Finset.mem_Icc] at hi₁
        have h₁ : j - 1 ≠ i := by
          rw [← Walk.getVert_eq_support_getElem _ (Nat.zero_le _)] at h₂
          simp only [Walk.getVert_zero, ne_eq, hi₂] at h₂
          contrapose! h₂
          rw [h₂]
        omega
      · apply Walk.mem_support_of_mem_takeAt_support at h₃
        rw [hi₂] at h₃
        contrapose! h₃
        rwa [← h₃]
    specialize this ‹_›
    apply Walk.mem_support_of_mem_takeAt_support at h₃
    rw [hi₂] at h₃
    exact this h₃
  let C : G.Walk (p.getVert (j - 1)) (p.getVert (j - 1)) := Cp.append Cpw
  have C_isCycle : C.IsCycle := by
    apply isPath_append_isCycle Cp_isPath Cpw_isPath Cp_tail_not_in_Cpw_tail
    rw [Walk.takeAt_length]
    omega
  have C_length : C.length < G.egirth := by
    rw [Walk.length_append]
    apply lt_of_le_of_lt ?_ hf
    have : Cp.length + Cpw.length ≤ 2 * G.diam + 1 := calc
      _ ≤ p.length + pw.length := add_le_add Cp_length Cpw_length
      _ ≤ _ := by
        rw [two_mul, add_assoc]
        exact add_le_add (hp₂ ▸ t_le_diam) pw_length.le
    have : (Cp.length + Cpw.length : ℕ∞) ≤ (2 * G.diam + 1 : ℕ∞) := by norm_cast
    exact this.trans <| add_le_add (by simp [diam_le_ediam]) rfl.le
  use p.getVert (j - 1), C

end SimpleGraph
