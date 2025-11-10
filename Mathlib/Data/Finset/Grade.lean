/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.Grade
import Mathlib.Order.Nat

/-!
# Finsets and multisets form a graded order

This file characterises atoms, coatoms and the covering relation in finsets and multisets. It also
proves that they form a `ℕ`-graded order.

## Main declarations

* `Multiset.instGradeMinOrder_nat`: Multisets are `ℕ`-graded
* `Finset.instGradeMinOrder_nat`: Finsets are `ℕ`-graded
-/

open Order

variable {α : Type*}

namespace Multiset
variable {s t : Multiset α} {a : α}

@[simp] lemma covBy_cons (s : Multiset α) (a : α) : s ⋖ a ::ₘ s :=
  ⟨lt_cons_self _ _, fun t hst hts ↦ (covBy_succ _).2 (card_lt_card hst) <| by
    simpa using card_lt_card hts⟩

lemma _root_.CovBy.exists_multiset_cons (h : s ⋖ t) : ∃ a, a ::ₘ s = t :=
  (lt_iff_cons_le.1 h.lt).imp fun _a ha ↦ ha.eq_of_not_lt <| h.2 <| lt_cons_self _ _

lemma covBy_iff : s ⋖ t ↔ ∃ a, a ::ₘ s = t :=
  ⟨CovBy.exists_multiset_cons, by rintro ⟨a, rfl⟩; exact covBy_cons _ _⟩

lemma _root_.CovBy.card_multiset (h : s ⋖ t) : card s ⋖ card t := by
  obtain ⟨a, rfl⟩ := h.exists_multiset_cons; rw [card_cons]; exact covBy_succ _

lemma isAtom_iff : IsAtom s ↔ ∃ a, s = {a} := by simp [← bot_covBy_iff, covBy_iff, eq_comm]

@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Multiset α) := isAtom_iff.2 ⟨_, rfl⟩

instance instGradeMinOrder : GradeMinOrder ℕ (Multiset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_multiset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

@[simp] lemma grade_eq (m : Multiset α) : grade ℕ m = card m := rfl

end Multiset

namespace Finset
variable {s t : Finset α} {a : α}

/-- Finsets form an order-connected suborder of multisets. -/
lemma ordConnected_range_val : Set.OrdConnected (Set.range val : Set <| Multiset α) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨⟨t, Multiset.nodup_of_le ht.2 s.2⟩, rfl⟩⟩

/-- Finsets form an order-connected suborder of sets. -/
lemma ordConnected_range_coe : Set.OrdConnected (Set.range ((↑) : Finset α → Set α)) :=
  ⟨by rintro _ _ _ ⟨s, rfl⟩ t ht; exact ⟨_, (s.finite_toSet.subset ht.2).coe_toFinset⟩⟩

@[simp] lemma val_wcovBy_val : s.1 ⩿ t.1 ↔ s ⩿ t :=
  ordConnected_range_val.apply_wcovBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

@[simp] lemma val_covBy_val : s.1 ⋖ t.1 ↔ s ⋖ t :=
  ordConnected_range_val.apply_covBy_apply_iff ⟨⟨_, val_injective⟩, val_le_iff⟩

@[simp] lemma coe_wcovBy_coe : (s : Set α) ⩿ t ↔ s ⩿ t :=
  ordConnected_range_coe.apply_wcovBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

@[simp] lemma coe_covBy_coe : (s : Set α) ⋖ t ↔ s ⋖ t :=
  ordConnected_range_coe.apply_covBy_apply_iff ⟨⟨_, coe_injective⟩, coe_subset⟩

alias ⟨_, _root_.WCovBy.finset_val⟩ := val_wcovBy_val
alias ⟨_, _root_.CovBy.finset_val⟩ := val_covBy_val
alias ⟨_, _root_.WCovBy.finset_coe⟩ := coe_wcovBy_coe
alias ⟨_, _root_.CovBy.finset_coe⟩ := coe_covBy_coe

@[simp] lemma covBy_cons (ha : a ∉ s) : s ⋖ s.cons a ha := by simp [← val_covBy_val]

lemma _root_.CovBy.exists_finset_cons (h : s ⋖ t) : ∃ a, ∃ ha : a ∉ s, s.cons a ha = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_exists_cons_subset.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_cons _).symm⟩

lemma covBy_iff_exists_cons : s ⋖ t ↔ ∃ a, ∃ ha : a ∉ s, s.cons a ha = t :=
  ⟨CovBy.exists_finset_cons, by rintro ⟨a, ha, rfl⟩; exact covBy_cons _⟩

lemma _root_.CovBy.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covBy_val.2 h).card_multiset

section DecidableEq
variable [DecidableEq α]

@[simp] lemma wcovBy_insert (s : Finset α) (a : α) : s ⩿ insert a s := by simp [← coe_wcovBy_coe]
@[simp] lemma erase_wcovBy (s : Finset α) (a : α) : s.erase a ⩿ s := by simp [← coe_wcovBy_coe]

lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
  (wcovBy_insert _ _).covBy_of_lt <| ssubset_insert ha

@[simp] lemma empty_covBy_singleton (a : α) : ∅ ⋖ ({a} : Finset α) :=
  insert_empty_eq (β := Finset α) a ▸ covBy_insert <| notMem_empty a

@[simp] lemma erase_covBy (ha : a ∈ s) : s.erase a ⋖ s := ⟨erase_ssubset ha, (erase_wcovBy _ _).2⟩

lemma _root_.CovBy.exists_finset_insert (h : s ⋖ t) : ∃ a ∉ s, insert a s = t := by
  simpa using h.exists_finset_cons

lemma _root_.CovBy.exists_finset_erase (h : s ⋖ t) : ∃ a ∈ t, t.erase a = s := by
  simpa only [← coe_inj, coe_erase] using h.finset_coe.exists_set_sdiff_singleton

lemma covBy_iff_exists_insert : s ⋖ t ↔ ∃ a ∉ s, insert a s = t := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_insert, ← coe_inj, coe_insert, mem_coe]

lemma covBy_iff_card_sdiff_eq_one : t ⋖ s ↔ t ⊆ s ∧ (s \ t).card = 1 := by
  rw [covBy_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [card_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 <| superset_of_eq ha <| mem_singleton_self _).2, ?_⟩
    rw [insert_eq, ← ha, sdiff_union_of_subset hts]

lemma covBy_iff_exists_erase : s ⋖ t ↔ ∃ a ∈ t, t.erase a = s := by
  simp only [← coe_covBy_coe, Set.covBy_iff_exists_sdiff_singleton, ← coe_inj, coe_erase, mem_coe]

end DecidableEq

@[simp] lemma isAtom_singleton (a : α) : IsAtom ({a} : Finset α) :=
  ⟨singleton_ne_empty a, fun _ ↦ eq_empty_of_ssubset_singleton⟩

protected lemma isAtom_iff : IsAtom s ↔ ∃ a, s = {a} := by
  simp [← bot_covBy_iff, covBy_iff_exists_cons, eq_comm]

section Fintype
variable [Fintype α] [DecidableEq α]

lemma isCoatom_compl_singleton (a : α) : IsCoatom ({a}ᶜ : Finset α) := (isAtom_singleton a).compl

protected lemma isCoatom_iff : IsCoatom s ↔ ∃ a, s = {a}ᶜ := by
  simp_rw [← isAtom_compl, Finset.isAtom_iff, compl_eq_iff_isCompl, eq_compl_iff_isCompl]

end Fintype

/-- Finsets are multiset-graded. This is not very meaningful mathematically but rather a handy way
to record that the inclusion `Finset α ↪ Multiset α` preserves the covering relation. -/
instance instGradeMinOrder_multiset : GradeMinOrder (Multiset α) (Finset α) where
  grade := val
  grade_strictMono := val_strictMono
  covBy_grade _ _ := CovBy.finset_val
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

@[simp] lemma grade_multiset_eq (s : Finset α) : grade (Multiset α) s = s.1 := rfl

instance instGradeMinOrder_nat : GradeMinOrder ℕ (Finset α) where
  grade := card
  grade_strictMono := card_strictMono
  covBy_grade _ _ := CovBy.card_finset
  isMin_grade s hs := by rw [isMin_iff_eq_bot.1 hs]; exact isMin_bot

@[simp] lemma grade_eq (s : Finset α) : grade ℕ s = s.card := rfl

end Finset
