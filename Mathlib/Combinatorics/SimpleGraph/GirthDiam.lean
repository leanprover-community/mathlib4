import Mathlib
namespace SimpleGraph

namespace Walk

variable {V} {G : SimpleGraph V}

lemma IsPath.exists_of_edges {u v a b : V} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hep : s(a, b) ∈ p.edges) (heq : s(a, b) ∈ q.edges) (hl : 1 < p.length) :
    ∃ z, z ∈ p.support.tail ∧ z ∈ q.support.tail := by
  apply Walk.getVert_of_edge at hep
  apply Walk.getVert_of_edge at heq
  obtain ⟨k₁, hl₁, h₁⟩ := hep
  obtain ⟨k₂, hl₂, h₂⟩ := heq
  cases h₁ with
  | inl h₁ => cases h₂ with
    | inl h₂ =>
      use b
      nth_rw 1 [h₁.2, h₂.2, p.getVert_eq_support_getElem hl₁, q.getVert_eq_support_getElem hl₂]
      exact ⟨List.mem_tail _ (Nat.zero_lt_succ k₁) _, List.mem_tail _ (Nat.zero_lt_succ k₂) _⟩
    | inr h₂ =>
      cases k₁
      · use b
        apply And.intro <| h₁.2 ▸ p.getVert_eq_support_getElem hl₁ ▸ List.mem_tail _ Nat.one_pos _
        cases k₂
        · have h : v = p.getVert p.length := (getVert_length p).symm
          rw [getVert_zero] at h₂
          nth_rw 1 [← h₂.1, h₁.2] at h
          rw [← hp.getVert_injOn hl.le (by simp) h] at hl
          contradiction
        · simp [List.mem_tail, h₂.1, q.getVert_eq_support_getElem hl₂.le]
      · use a
        nth_rw 1 [h₁.1, h₂.2, p.getVert_eq_support_getElem hl₁.le, q.getVert_eq_support_getElem hl₂]
        simp [List.mem_tail]
  | inr h₁ => cases h₂ with
    | inl h₂ =>
      cases k₁
      · use a
        apply And.intro <| h₁.2 ▸ p.getVert_eq_support_getElem hl₁ ▸ List.mem_tail _ Nat.one_pos _
        cases k₂
        · obtain ⟨_, h₁⟩ := h₁
          nth_rw 1 [h₂.1, getVert_zero, ← p.getVert_length] at h₁
          rw [hp.getVert_injOn (by simp) hl.le h₁] at hl
          contradiction
        · simp [List.mem_tail,h₂.1, q.getVert_eq_support_getElem hl₂.le]
      use b
      nth_rw 1 [h₁.1, h₂.2]
      apply And.intro <;>
      simp [List.mem_tail, p.getVert_eq_support_getElem hl₁.le, q.getVert_eq_support_getElem hl₂]
    | inr h₂ =>
      use a
      nth_rw 1 [h₁.2, h₂.2, p.getVert_eq_support_getElem hl₁, q.getVert_eq_support_getElem hl₂]
      simp [List.mem_tail]

lemma isPath_append_isCycle' {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [append_isTrail_iff_edges_disjoint hp.isTrail hq.isTrail]
    intro x h₁ h₂
    have : ∃ a b, x = s(a, b) := ⟨x.out.1, x.out.2, Prod.mk.eta ▸ (Quot.out_eq x).symm⟩
    obtain ⟨_, _, hx⟩ := this
    subst hx
    obtain ⟨z, hz₁, hz₂⟩ := Walk.IsPath.exists_of_edges hp h₁ h₂ hn
    exact h hz₁ hz₂
  · rw [ne_eq, ← Walk.nil_iff_eq_nil, Walk.not_nil_iff_lt_length, Walk.length_append]
    omega
  · rw [Walk.tail_support_append, List.nodup_append]
    exact ⟨p.support.tail_sublist.nodup (p.isPath_def.mp hp), q.support.tail_sublist.nodup
      (q.isPath_def.mp hq), fun _ x _ y ↦ ne_of_mem_of_not_mem x (h.symm y)⟩

lemma isPath_append_isCycle {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length ⊔ q.length) :
    (p.append q).IsCycle := by
  cases lt_sup_iff.mp hn with
  | inl hn => exact isPath_append_isCycle' hp hq h hn
  | inr hn =>
    have := isPath_append_isCycle' hq hp (List.disjoint_left.mpr h.symm) hn
    rw [isCycle_def] at this ⊢
    obtain ⟨h₁, h₂, h₃⟩ := this
    refine ⟨?_, ?_, ?_⟩
    · rw [isTrail_def, edges_append] at h₁ ⊢
      exact List.nodup_append_comm.mp h₁
    · rw [ne_eq, ← length_eq_zero_iff.not, length_append] at h₂ ⊢
      rwa [add_comm]
    · simp only [support_append, ne_eq, support_ne_nil, not_false_eq_true,
        List.tail_append_of_ne_nil] at h₃ ⊢
      exact List.nodup_append_comm.mp h₃

theorem cycle_from_two_paths {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (h : p ≠ q) :
    ∃ w, w ∈ p.support ++ q.support ∧
    ∃ c : G.Walk w w, c.IsCycle ∧ c.length ≤ p.length + q.length := by
  induction hs : p.length + q.length using Nat.strong_induction_on generalizing u v with | h s ih =>
  by_cases! hw : ∃ w ∈ p.support, w ∈ q.support ∧ w ≠ u ∧ w ≠ v
  · classical
    obtain ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! htake : p.takeUntil w hwp ≠ q.takeUntil w hwq
    · obtain ⟨x, hx, c, hc⟩ := ih ((p.takeUntil w hwp).length + (q.takeUntil w hwq).length)
        (hs ▸ Nat.add_lt_add (length_takeUntil_lt hwp hwv) (length_takeUntil_lt hwq hwv))
        (hp.takeUntil hwp) (hq.takeUntil hwq) htake rfl
      use x
      apply And.intro
      · cases List.mem_append.mp hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_takeUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_takeUntil_subset _ ‹_›
      · use c, hc.1, hc.2.trans
        <| hs ▸ Nat.add_le_add (p.length_takeUntil_le hwp) (q.length_takeUntil_le hwq)
    · have hdrop : p.dropUntil w hwp ≠ q.dropUntil w hwq := by
        contrapose! h
        rw [← p.take_spec hwp, ← q.take_spec hwq, htake, h]
      obtain ⟨x, hx, c, hc⟩ := ih ((p.dropUntil w hwp).length + (q.dropUntil w hwq).length)
        (hs ▸ Nat.add_lt_add (length_dropUntil_lt hwp hwu) (length_dropUntil_lt hwq hwu))
        (hp.dropUntil hwp) (hq.dropUntil hwq) hdrop rfl
      use x
      apply And.intro
      · cases List.mem_append.mp hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_dropUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_dropUntil_subset _ ‹_›
      · use c, hc.1, hc.2.trans
        <| hs ▸ Nat.add_le_add (p.length_dropUntil_le hwp) (q.length_dropUntil_le hwq)
  · use u, by simp, p.append q.reverse
    refine ⟨isPath_append_isCycle hp ((isPath_reverse_iff q).mpr hq) ?_ ?_, by simpa using hs.le⟩
    · intro a hap haq
      specialize hw a (List.mem_of_mem_tail hap) <| by
        rw [support_reverse, List.tail_reverse, List.mem_reverse] at haq
        exact List.mem_of_mem_dropLast haq
      have : u ∉ p.support.tail := (List.nodup_cons.mp (p.support_eq_cons ▸ hp.support_nodup)).1
      have : a ≠ u := by
        contrapose! this
        rwa [this] at hap
      rw [hw this, support_reverse, List.tail_reverse, List.mem_reverse] at haq
      have := (List.nodup_concat _ _).mp <| q.support_eq_concat ▸ hq.support_nodup
      tauto
    · rw [length_reverse, lt_sup_iff]
      by_contra! hpq
      obtain ⟨hpl, hql⟩ := hpq
      rw [Nat.le_one_iff_eq_zero_or_eq_one] at hpl hql
      rcases hpl with hpl | hpl <;> rcases hql with hql | hql
      · have := (nil_iff_length_eq.mpr hpl).eq
        subst this
        simp [length_eq_zero_iff.mp hpl, length_eq_zero_iff.mp hql] at h
      · exact (adj_of_length_eq_one hql).ne (nil_iff_length_eq.mpr hpl).eq
      · exact (adj_of_length_eq_one hpl).ne (nil_iff_length_eq.mpr hql).eq
      · contrapose! h
        apply ext_getVert_le_length (by rw [hpl, hql]) (fun k hk ↦ ?_)
        cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hpl ▸ hk)
        · simp [‹_›]
        · subst ‹_›
          nth_rw 1 [← hpl, ← hql, getVert_length, getVert_length]

end Walk

end SimpleGraph
