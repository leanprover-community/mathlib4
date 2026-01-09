import Mathlib
namespace SimpleGraph

namespace Walk

variable {V} {G : SimpleGraph V}

lemma IsTrail.append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail) (h_disjoint : p.edges.Disjoint q.edges) :
    (p.append q).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
  exact ⟨hp.edges_nodup, hq.edges_nodup, fun _ x _ y ↦ ne_of_mem_of_not_mem x (h_disjoint.symm y)⟩

lemma getVert_of_edge {u v a b} (p : G.Walk u v) (h : s(a, b) ∈ p.edges) :
    ∃ k < p.length, a = p.getVert k ∧ b = p.getVert k.succ ∨
      b = p.getVert k ∧ a = p.getVert k.succ:= by
  induction p with
  | nil => simp at h
  | cons ha p ih =>
    rw [edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h
    cases h
    · use 0
      simp only [length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getVert_zero,
        Nat.succ_eq_add_one, zero_add, getVert_cons_succ, true_and]
      grind
    · obtain ⟨k, h, hk⟩ := ih ‹_›
      use k + 1
      simp only [length_cons, add_lt_add_iff_right, getVert_cons_succ, Nat.succ_eq_add_one]
      grind

lemma List.mem_tail {α k} (L : List α) (h : 0 < k) (hk : k < L.length) :
    L[k]'hk ∈ L.tail := by
  cases L
  · simp
  · grind

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

lemma isPath_append_isCycle' {u v} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · apply hp.isTrail.append hq.isTrail
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
  rw [lt_sup_iff] at hn
  cases hn with
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

lemma length_dropUntil_lt {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huv : u ≠ v)
    [DecidableEq V] :
    (p.dropUntil u h).length < p.length := by
  cases p with
  | nil => simp [huv] at h
  | cons =>
    simp only [support_cons, List.mem_cons, huv, false_or] at h
    simpa [dropUntil, huv.symm] using Order.lt_add_one_iff.mpr <| length_le_of_isSubwalk
      <| isSubwalk_dropUntil _ h

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
      · rw [List.mem_append] at hx
        cases hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_takeUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_takeUntil_subset _ ‹_›
      · use c, hc.1
        apply hc.2.trans
        exact hs ▸ Nat.add_le_add (p.length_takeUntil_le hwp) (q.length_takeUntil_le hwq)
    · have hdrop : p.dropUntil w hwp ≠ q.dropUntil w hwq := by
        contrapose! h
        rw [← p.take_spec hwp, ← q.take_spec hwq, htake, h]
      obtain ⟨x, hx, c, hc⟩ := ih ((p.dropUntil w hwp).length + (q.dropUntil w hwq).length)
        (hs ▸ Nat.add_lt_add (length_dropUntil_lt hwp hwu) (length_dropUntil_lt hwq hwu))
        (hp.dropUntil hwp) (hq.dropUntil hwq) hdrop rfl
      use x
      apply And.intro
      · rw [List.mem_append] at hx
        cases hx
        · exact List.mem_append.mpr <| Or.inl <| p.support_dropUntil_subset _ ‹_›
        · exact List.mem_append.mpr <| Or.inr <| q.support_dropUntil_subset _ ‹_›
      · use c, hc.1
        apply hc.2.trans
        exact hs ▸ Nat.add_le_add (p.length_dropUntil_le hwp) (q.length_dropUntil_le hwq)
  · use u, by simp, p.append q.reverse
    apply And.intro
    · apply isPath_append_isCycle hp ((isPath_reverse_iff q).mpr hq)
      · intro a hap haq
        have : p.support.tail ⊆ p.support := by exact List.tail_subset p.support
        specialize hw a (List.mem_of_mem_tail hap) <| by
          rw [support_reverse, List.tail_reverse, List.mem_reverse] at haq
          exact List.mem_of_mem_dropLast haq
        have : u ∉ p.support.tail := by
          have : p.support = u :: p.support.tail := support_eq_cons p
          have : p.support.Nodup := hp.support_nodup
          rw [support_eq_cons p, List.nodup_cons] at this
          exact this.1
        have : a ≠ u := by
          contrapose! this
          rwa [this] at hap
        apply hw at this
        rw [this] at haq
        simp only [support_reverse, List.tail_reverse, List.mem_reverse] at haq
        have : v ∈ q.support := end_mem_support q
        rw [Walk.support_eq_concat] at this
        have : (q.support.dropLast.concat v).Nodup := q.support_eq_concat ▸ hq.support_nodup
        rw [List.nodup_concat] at this
        tauto
      · rw [length_reverse, lt_sup_iff]
        by_contra! hpq
        obtain ⟨hpl, hql⟩ := hpq
        rw [Nat.le_one_iff_eq_zero_or_eq_one] at hpl hql
        rcases hpl with hpl | hpl <;> rcases hql with hql | hql
        · have := (nil_iff_length_eq.mpr hpl).eq
          subst this
          rw [length_eq_zero_iff] at hpl hql
          simp [hpl, hql] at h
        · exact (adj_of_length_eq_one hql).ne (nil_iff_length_eq.mpr hpl).eq
        · exact (adj_of_length_eq_one hpl).ne (nil_iff_length_eq.mpr hql).eq
        · have : p = q := by
            apply ext_getVert_le_length (by rw [hpl, hql]) (fun k hk ↦ ?_)
            rw [hpl, Nat.le_one_iff_eq_zero_or_eq_one] at hk
            cases hk
            · simp [‹_›]
            · subst ‹_›
              nth_rw 1 [← hpl, ← hql, getVert_length, getVert_length]
          contradiction
    simpa using hs.le

end Walk

end SimpleGraph
