/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Order.Partition.Equipartition

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are "as close as possible" to unions of parts of `Q`. By
"as close as possible", we mean that each part of `P` can be written as the union of some parts of
`Q` along with at most `m` other elements.

## Main declarations

* `Finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `Finpartition.exists_equipartition_card_eq`: We can find equipartitions of arbitrary size.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset Nat

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : ℕ} {P : Finpartition s}

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, we can
find a new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the
union of parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and
(provided `m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size
`m` and hence `a + b` parts in total. -/
theorem equitabilise_aux (hs : a * m + b * (m + 1) = #s) :
    ∃ Q : Finpartition s,
      (∀ x : Finset α, x ∈ Q.parts → #x = m ∨ #x = m + 1) ∧
        (∀ x, x ∈ P.parts → #(x \ {y ∈ Q.parts | y ⊆ x}.biUnion id) ≤ m) ∧
          #{i ∈ Q.parts | #i = m + 1} = b := by
  -- Get rid of the easy case `m = 0`
  obtain rfl | m_pos := m.eq_zero_or_pos
  · refine ⟨⊥, by simp, ?_, by simpa [Finset.filter_true_of_mem] using hs.symm⟩
    simp only [le_zero_iff, card_eq_zero, mem_biUnion, exists_prop, mem_filter, id,
      and_assoc, sdiff_eq_empty_iff_subset, subset_iff]
    exact fun x hx a ha =>
      ⟨{a}, mem_map_of_mem _ (P.le hx ha), singleton_subset_iff.2 ha, mem_singleton_self _⟩
  -- Prove the case `m > 0` by strong induction on `s`
  induction s using Finset.strongInduction generalizing a b with | H s ih => _
  -- If `a = b = 0`, then `s = ∅` and we can partition into zero parts
  by_cases hab : a = 0 ∧ b = 0
  · simp only [hab.1, hab.2, add_zero, zero_mul, eq_comm, card_eq_zero, Finset.bot_eq_empty] at hs
    subst hs
    -- Porting note: to synthesize `Finpartition ∅`, `have` is required
    have : P = Finpartition.empty _ := Unique.eq_default (α := Finpartition ⊥) P
    exact ⟨Finpartition.empty _, by simp, by simp [this], by simp [hab.2]⟩
  simp_rw [not_and_or, ← Ne.eq_def, ← pos_iff_ne_zero] at hab
  -- `n` will be the size of the smallest part
  set n := if 0 < a then m else m + 1 with hn
  -- Some easy facts about it
  obtain ⟨hn₀, hn₁, hn₂, hn₃⟩ : 0 < n ∧ n ≤ m + 1 ∧ n ≤ a * m + b * (m + 1) ∧
      ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #s - n := by
    rw [hn, ← hs]
    split_ifs with h <;> rw [tsub_mul, one_mul]
    · refine ⟨m_pos, le_succ _, le_add_right (Nat.le_mul_of_pos_left _ ‹0 < a›), ?_⟩
      rw [tsub_add_eq_add_tsub (Nat.le_mul_of_pos_left _ h)]
    · refine ⟨succ_pos', le_rfl,
        le_add_left (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›), ?_⟩
      rw [← add_tsub_assoc_of_le (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›)]
  /- We will call the inductive hypothesis on a partition of `s \ t` for a carefully chosen `t ⊆ s`.
    To decide which, however, we must distinguish the case where all parts of `P` have size `m` (in
    which case we take `t` to be an arbitrary subset of `s` of size `n`) from the case where at
    least one part `u` of `P` has size `m + 1` (in which case we take `t` to be an arbitrary subset
    of `u` of size `n`). The rest of each branch is just tedious calculations to satisfy the
    induction hypothesis. -/
  by_cases h : ∀ u ∈ P.parts, #u < m + 1
  · obtain ⟨t, hts, htn⟩ := exists_subset_card_eq (hn₂.trans_eq hs)
    have ht : t.Nonempty := by rwa [← card_pos, htn]
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
      rw [card_sdiff ‹t ⊆ s›, htn, hn₃]
    obtain ⟨R, hR₁, _, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset hts ‹t.Nonempty›) (if 0 < a then a - 1 else a)
        (if 0 < a then b else b - 1) (P.avoid t) hcard
    refine ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel hts), ?_, ?_, ?_⟩
    · simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, htn, hn]
      exact ite_eq_or_eq _ _ _
    · exact fun x hx => (card_le_card sdiff_subset).trans (Nat.lt_succ_iff.1 <| h _ hx)
    simp_rw [extend_parts, filter_insert, htn, n, m.succ_ne_self.symm.ite_eq_right_iff]
    split_ifs with ha
    · rw [hR₃, if_pos ha]
    rw [card_insert_of_notMem, hR₃, if_neg ha, tsub_add_cancel_of_le]
    · exact hab.resolve_left ha
    · intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
  push_neg at h
  obtain ⟨u, hu₁, hu₂⟩ := h
  obtain ⟨t, htu, htn⟩ := exists_subset_card_eq (hn₁.trans hu₂)
  have ht : t.Nonempty := by rwa [← card_pos, htn]
  have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
    rw [card_sdiff (htu.trans <| P.le hu₁), htn, hn₃]
  obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
    @ih (s \ t) (sdiff_ssubset (htu.trans <| P.le hu₁) ht) (if 0 < a then a - 1 else a)
      (if 0 < a then b else b - 1) (P.avoid t) hcard
  refine
    ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel <| htu.trans <| P.le hu₁), ?_, ?_, ?_⟩
  · simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, htn, hn]
    exact ite_eq_or_eq _ _ _
  · conv in _ ∈ _ => rw [← insert_erase hu₁]
    simp only [and_imp, mem_insert, forall_eq_or_imp, Ne, extend_parts]
    refine ⟨?_, fun x hx => (card_le_card ?_).trans <| hR₂ x ?_⟩
    · simp only [filter_insert, if_pos htu, biUnion_insert, mem_erase, id]
      obtain rfl | hut := eq_or_ne u t
      · rw [sdiff_eq_empty_iff_subset.2 subset_union_left]
        exact bot_le
      refine
        (card_le_card fun i => ?_).trans
          (hR₂ (u \ t) <| P.mem_avoid.2 ⟨u, hu₁, fun i => hut <| i.antisymm htu, rfl⟩)
      simpa using fun hi₁ hi₂ hi₃ =>
        ⟨⟨hi₁, hi₂⟩, fun x hx hx' => hi₃ _ hx <| hx'.trans sdiff_subset⟩
    · apply sdiff_subset_sdiff Subset.rfl (biUnion_subset_biUnion_of_subset_left _ _)
      exact filter_subset_filter _ (subset_insert _ _)
    simp only [avoid, ofErase, mem_erase, mem_image, bot_eq_empty]
    exact
      ⟨(nonempty_of_mem_parts _ <| mem_of_mem_erase hx).ne_empty, _, mem_of_mem_erase hx,
        (disjoint_of_subset_right htu <|
            P.disjoint (mem_of_mem_erase hx) hu₁ <| ne_of_mem_erase hx).sdiff_eq_left⟩
  simp only [extend_parts, filter_insert, htn, hn, m.succ_ne_self.symm.ite_eq_right_iff]
  split_ifs with h
  · rw [hR₃, if_pos h]
  · rw [card_insert_of_notMem, hR₃, if_neg h, Nat.sub_add_cancel (hab.resolve_left h)]
    intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)

variable (h : a * m + b * (m + 1) = #s)

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, build a
new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the union of
parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and (provided
`m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size `m` and
hence `a + b` parts in total. -/
noncomputable def equitabilise : Finpartition s :=
  (P.equitabilise_aux h).choose

variable {h}

theorem card_eq_of_mem_parts_equitabilise :
    t ∈ (P.equitabilise h).parts → #t = m ∨ #t = m + 1 :=
  (P.equitabilise_aux h).choose_spec.1 _

theorem equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

variable (P h)

theorem card_filter_equitabilise_big : #{u ∈ (P.equitabilise h).parts | #u = m + 1} = b :=
  (P.equitabilise_aux h).choose_spec.2.2

theorem card_filter_equitabilise_small (hm : m ≠ 0) :
    #{u ∈ (P.equitabilise h).parts | #u = m} = a := by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h, ← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u ∈ (P.equitabilise h).parts | #u = m} ∪ {u ∈ (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or, filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union, sum_const_nat fun x hx => (mem_filter.1 hx).2,
    sum_const_nat fun x hx => (mem_filter.1 hx).2, P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)

theorem card_parts_equitabilise (hm : m ≠ 0) : #(P.equitabilise h).parts = a + b := by
  rw [← filter_true_of_mem fun x => card_eq_of_mem_parts_equitabilise, filter_or,
    card_union_of_disjoint, P.card_filter_equitabilise_small _ hm, P.card_filter_equitabilise_big]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11187): was `infer_instance`
  exact disjoint_filter.2 fun x _ h₀ h₁ => Nat.succ_ne_self m <| h₁.symm.trans h₀

theorem card_parts_equitabilise_subset_le :
    t ∈ P.parts → #(t \ {u ∈ (P.equitabilise h).parts | u ⊆ t}.biUnion id) ≤ m :=
  (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

variable (s)

/-- We can find equipartitions of arbitrary size. -/
theorem exists_equipartition_card_eq (hn : n ≠ 0) (hs : n ≤ #s) :
    ∃ P : Finpartition s, P.IsEquipartition ∧ #P.parts = n := by
  rw [← pos_iff_ne_zero] at hn
  have : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul, mul_add, ← add_assoc,
      tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le), mul_one, add_comm,
      mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne', tsub_add_cancel_of_le (mod_lt _ hn).le]

end Finpartition
