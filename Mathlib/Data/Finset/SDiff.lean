/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Difference of finite sets

## Main declarations

* `Finset.instSDiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `Finset.instGeneralizedBooleanAlgebra`: Finsets almost have a Boolean algebra structure

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice OrderedCommMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance instSDiff : SDiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le (Multiset.sub_le_self ..) s₁.2⟩⟩

@[simp]
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl

@[simp, grind =]
theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  mem_sub_of_nodup s.2

@[simp]
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ := by grind

instance : GeneralizedBooleanAlgebra (Finset α) where
  sup_inf_sdiff := by grind
  inf_inf_sdiff := by grind

theorem notMem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by grind

@[deprecated (since := "2025-05-23")] alias not_mem_sdiff_of_mem_right := notMem_sdiff_of_mem_right

theorem notMem_sdiff_of_notMem_left (h : a ∉ s) : a ∉ s \ t := by simp [h]

@[deprecated (since := "2025-05-23")]
alias not_mem_sdiff_of_not_mem_left := notMem_sdiff_of_notMem_left

theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t := by grind

theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ := by grind

/-- See also `Finset.sdiff_inter_right_comm`. -/
lemma inter_sdiff_assoc (s t u : Finset α) : (s ∩ t) \ u = s ∩ (t \ u) := inf_sdiff_assoc ..

/-- See also `Finset.inter_sdiff_assoc`. -/
lemma sdiff_inter_right_comm (s t u : Finset α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..

lemma inter_sdiff_left_comm (s t u : Finset α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..

@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left

protected theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  _root_.sdiff_self

theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

@[simp]
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

@[simp]
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[simp]
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot

@[mono, gcongr]
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v := by grind

theorem sdiff_subset_sdiff_iff_subset {r : Finset α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s := by
  simpa only [← le_eq_subset] using sdiff_le_sdiff_iff_le hs ht

@[simp, grind =, norm_cast]
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff

@[simp]
theorem union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right _ _

@[simp]
theorem sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left _ _

theorem union_sdiff_left (s t : Finset α) : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self

theorem union_sdiff_right (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem union_sdiff_cancel_left (h : Disjoint s t) : (s ∪ t) \ s = t :=
  h.sup_sdiff_cancel_left

theorem union_sdiff_cancel_right (h : Disjoint s t) : (s ∪ t) \ t = s :=
  h.sup_sdiff_cancel_right

theorem union_sdiff_symm : s ∪ t \ s = t ∪ s \ t := by simp [union_comm]

theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _

theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  _root_.sdiff_idem

theorem subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  le_iff_subset.symm.trans le_sdiff

@[simp]
theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[grind =]
theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp]
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff

theorem insert_sdiff_of_notMem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
    insert x s \ t = insert x (s \ t) := by grind

@[deprecated (since := "2025-05-23")] alias insert_sdiff_of_not_mem := insert_sdiff_of_notMem

theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t := by grind

@[simp] lemma insert_sdiff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by grind

@[simp] lemma insert_sdiff_cancel (ha : a ∉ s) : insert a s \ s = {a} := by grind

@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)

lemma insert_sdiff_insert' (hab : a ≠ b) (ha : a ∉ s) : insert a s \ insert b s = {a} := by
  ext; aesop

lemma cons_sdiff_cons (hab : a ≠ b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by grind

theorem sdiff_insert_of_notMem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  grind

@[deprecated (since := "2025-05-23")] alias sdiff_insert_of_not_mem := sdiff_insert_of_notMem

@[simp] theorem sdiff_subset {s t : Finset α} : s \ t ⊆ s := le_iff_subset.mp sdiff_le

theorem sdiff_ssubset (h : t ⊆ s) (ht : t.Nonempty) : s \ t ⊂ s := by grind

theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff

theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup

theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem Nontrivial.sdiff_singleton_nonempty {c : α} {s : Finset α} (hS : s.Nontrivial) :
    (s \ {c}).Nonempty := by grind

theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t ∩ (s \ u) :=
  _root_.sdiff_sdiff_left'

theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

theorem sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u :=
  sdiff_sdiff_eq_sdiff_sup h

theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self

theorem sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t :=
  _root_.sdiff_sdiff_eq_self h

theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} :
    s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf

theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_self_iff_disjoint'

theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h

end Sdiff

end Finset
