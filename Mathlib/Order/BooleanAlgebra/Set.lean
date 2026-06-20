/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Tauto

/-!
# Boolean algebra of sets

This file proves that `Set α` is a Boolean algebra, and proves results about set difference and
complement.

## Notation

* `sᶜ` for the complement of `s`

## Tags

set, sets, subset, subsets, complement
-/

@[expose] public section

assert_not_exists RelIso

open Function

namespace Set
variable {α β : Type*} {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

instance : HImp (Set α) where
  himp s t := {x | x ∈ s → x ∈ t}

@[simp] theorem mem_himp_iff : a ∈ s ⇨ t ↔ a ∈ s → a ∈ t := .rfl

instance instBooleanAlgebra : BooleanAlgebra (Set α) :=
  fast_instance% { (inferInstance : BooleanAlgebra (α → Prop)) with }

theorem himp_def : s ⇨ t = t ∪ sᶜ := himp_eq

/-- See also `Set.sdiff_inter_right_comm`. -/
lemma inter_sdiff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) := inf_sdiff_assoc ..

@[deprecated (since := "2026-06-03")] alias inter_diff_assoc := inter_sdiff_assoc

/-- See also `Set.inter_sdiff_assoc`. -/
lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..

lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..

theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel := sdiff_union_sdiff_cancel

/-- A version of `sdiff_union_sdiff_cancel` with more general hypotheses. -/
theorem sdiff_union_sdiff_cancel' (hi : s ∩ u ⊆ t) (hu : t ⊆ s ∪ u) : (s \ t) ∪ (t \ u) = s \ u :=
  sdiff_sup_sdiff_cancel' hi hu

@[deprecated (since := "2026-06-03")] alias diff_union_diff_cancel' := sdiff_union_sdiff_cancel'

theorem sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u :=
  sdiff_sdiff_eq_sdiff_sup h

@[deprecated (since := "2026-06-03")] alias diff_diff_eq_sdiff_union := sdiff_sdiff_eq_sdiff_union

theorem inter_sdiff_distrib_left (s t u : Set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
  inf_sdiff_distrib_left _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_left := inter_sdiff_distrib_left

theorem inter_sdiff_distrib_right (s t u : Set α) : (s \ t) ∩ u = (s ∩ u) \ (t ∩ u) :=
  inf_sdiff_distrib_right _ _ _

@[deprecated (since := "2026-06-03")] alias inter_diff_distrib_right := inter_sdiff_distrib_right

theorem sdiff_inter_distrib_right (s t r : Set α) : (t ∩ r) \ s = (t \ s) ∩ (r \ s) :=
  inf_sdiff

@[deprecated (since := "2026-06-03")] alias diff_inter_distrib_right := sdiff_inter_distrib_right

/-! ### Lemmas about complement -/

theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h

theorem compl_setOf {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl

theorem notMem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h

theorem notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not

@[simp]
theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  compl_inf_eq_bot

@[simp]
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot

@[simp]
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup

theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  compl_top

@[simp]
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

theorem compl_ne_univ : sᶜ ≠ univ ↔ s.Nonempty :=
  compl_univ_iff.not.trans nonempty_iff_ne_empty.symm

lemma inl_compl_union_inr_compl {s : Set α} {t : Set β} :
    Sum.inl '' sᶜ ∪ Sum.inr '' tᶜ = (Sum.inl '' s ∪ Sum.inr '' t)ᶜ := by
  grind

theorem nonempty_compl : sᶜ.Nonempty ↔ s ≠ univ :=
  (ne_univ_iff_exists_notMem s).symm

theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
  ext fun _ => or_iff_not_and_not

theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
  ext fun _ => and_iff_not_or_not

@[simp]
theorem union_compl_self (s : Set α) : s ∪ sᶜ = univ :=
  eq_univ_iff_forall.2 fun _ => em _

@[simp]
theorem compl_union_self (s : Set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]

theorem compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  @compl_le_iff_compl_le _ s _ _

theorem subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
  @le_compl_iff_le_compl _ _ _ t

@[simp]
theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
  @compl_le_compl_iff_le (Set α) _ _ _

@[gcongr] theorem compl_subset_compl_of_subset (h : t ⊆ s) : sᶜ ⊆ tᶜ := compl_subset_compl.2 h

theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le

theorem compl_subset_iff_union {s t : Set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  Iff.symm <| eq_univ_iff_forall.trans <| forall_congr' fun _ => or_iff_not_imp_left

theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr' fun _ => and_imp.trans <| imp_congr_right fun _ => imp_iff_not_or

theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ tᶜ).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans <| exists_congr fun x => by simp).symm

lemma subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s := le_compl_iff_disjoint_left
lemma subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t := le_compl_iff_disjoint_right
lemma disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t ⊆ s := disjoint_compl_left_iff
lemma disjoint_compl_right_iff_subset : Disjoint s tᶜ ↔ s ⊆ t := disjoint_compl_right_iff

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_left⟩ := disjoint_compl_left_iff_subset
alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_right⟩ := disjoint_compl_right_iff_subset

@[simp] lemma nonempty_compl_of_nontrivial [Nontrivial α] (x : α) : Set.Nonempty {x}ᶜ := exists_ne x

lemma mem_compl_singleton_iff : a ∈ ({b} : Set α)ᶜ ↔ a ≠ b := .rfl

lemma compl_singleton_eq (a : α) : {a}ᶜ = {x | x ≠ a} := rfl

@[simp]
lemma compl_ne_eq_singleton (a : α) : {x | x ≠ a}ᶜ = {a} := compl_compl _

@[simp]
lemma subset_compl_singleton_iff : s ⊆ {a}ᶜ ↔ a ∉ s := subset_compl_comm.trans singleton_subset_iff

/-! ### Lemmas about set difference -/

theorem notMem_sdiff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx

@[deprecated (since := "2026-06-03")] alias notMem_diff_of_mem := notMem_sdiff_of_mem

theorem mem_of_mem_sdiff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left

@[deprecated (since := "2026-06-03")] alias mem_of_mem_diff := mem_of_mem_sdiff

theorem notMem_of_mem_sdiff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right

@[deprecated (since := "2026-06-03")] alias notMem_of_mem_diff := notMem_of_mem_sdiff

theorem sdiff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [sdiff_eq, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_eq_compl_inter := sdiff_eq_compl_inter

theorem sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff

@[deprecated (since := "2026-06-03")] alias diff_nonempty := sdiff_nonempty

theorem sdiff_subset {s t : Set α} : s \ t ⊆ s := show s \ t ≤ s from sdiff_le

@[deprecated (since := "2026-06-03")] alias diff_subset := sdiff_subset

theorem sdiff_subset_compl (s t : Set α) : s \ t ⊆ tᶜ :=
  sdiff_eq_compl_inter ▸ inter_subset_left

@[deprecated (since := "2026-06-03")] alias diff_subset_compl := sdiff_subset_compl

theorem union_sdiff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂

@[deprecated (since := "2026-06-03")] alias union_diff_cancel' := union_sdiff_cancel'

theorem union_sdiff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel := union_sdiff_cancel

theorem union_sdiff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left <| disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_left := union_sdiff_cancel_left

theorem union_sdiff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right <| disjoint_iff_inf_le.2 h

@[deprecated (since := "2026-06-03")] alias union_diff_cancel_right := union_sdiff_cancel_right

@[simp]
theorem union_sdiff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self

@[deprecated (since := "2026-06-03")] alias union_diff_left := union_sdiff_left

@[simp]
theorem union_sdiff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias union_diff_right := union_sdiff_right

theorem union_sdiff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff

@[deprecated (since := "2026-06-03")] alias union_diff_distrib := union_sdiff_distrib

@[simp]
theorem inter_sdiff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right

@[deprecated (since := "2026-06-03")] alias inter_diff_self := inter_sdiff_self

@[simp]
theorem inter_union_sdiff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t

@[deprecated (since := "2026-06-03")] alias inter_union_diff := inter_union_sdiff

@[simp]
theorem sdiff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s := by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[deprecated (since := "2026-06-03")] alias diff_union_inter := sdiff_union_inter

@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_sdiff _ _

theorem subset_inter_union_compl_left (s t : Set α) : t ⊆ s ∩ t ∪ sᶜ := by
  simp [inter_union_distrib_right]

theorem subset_inter_union_compl_right (s t : Set α) : s ⊆ s ∩ t ∪ tᶜ := by
  simp [inter_union_distrib_right]

theorem union_inter_compl_left_subset (s t : Set α) : (s ∪ t) ∩ sᶜ ⊆ t := by
  simp [union_inter_distrib_right]

theorem union_inter_compl_right_subset (s t : Set α) : (s ∪ t) ∩ tᶜ ⊆ s := by
  simp [union_inter_distrib_right]

@[gcongr]
theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  sdiff_le_sdiff

@[deprecated (since := "2026-06-03")] alias diff_subset_diff := sdiff_subset_sdiff

theorem sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_left := sdiff_subset_sdiff_left

theorem sdiff_subset_sdiff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›

@[deprecated (since := "2026-06-03")] alias diff_subset_diff_right := sdiff_subset_sdiff_right

theorem sdiff_subset_sdiff_iff_subset {r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht

@[deprecated (since := "2026-06-03")]
alias diff_subset_diff_iff_subset := sdiff_subset_sdiff_iff_subset

theorem compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm

@[deprecated (since := "2026-06-03")] alias compl_eq_univ_diff := compl_eq_univ_sdiff

@[simp]
theorem empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff

@[deprecated (since := "2026-06-03")] alias empty_diff := empty_sdiff

theorem sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[deprecated (since := "2026-06-03")] alias diff_eq_empty := sdiff_eq_empty

@[simp]
theorem sdiff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot

@[deprecated (since := "2026-06-03")] alias diff_empty := sdiff_empty

@[simp]
theorem sdiff_univ (s : Set α) : s \ univ = ∅ :=
  sdiff_eq_empty.2 (subset_univ s)

@[deprecated (since := "2026-06-03")] alias diff_univ := sdiff_univ

theorem sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left

@[deprecated (since := "2026-06-03")] alias diff_diff := sdiff_sdiff

-- the following statement contains parentheses to help the reader
theorem sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  _root_.sdiff_sdiff_comm

@[deprecated (since := "2026-06-03")] alias diff_diff_comm := sdiff_sdiff_comm

@[simp]
theorem sdiff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  sdiff_le_iff

@[deprecated (since := "2026-06-03")] alias diff_subset_iff := sdiff_subset_iff

theorem subset_sdiff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  le_sdiff_sup

@[deprecated (since := "2026-06-03")] alias subset_diff_union := subset_sdiff_union

theorem sdiff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset sdiff_subset h) (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias diff_union_of_subset := sdiff_union_of_subset

theorem sdiff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm

@[deprecated (since := "2026-06-03")] alias diff_subset_comm := sdiff_subset_comm

theorem sdiff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

@[deprecated (since := "2026-06-03")] alias diff_inter := sdiff_inter

theorem sdiff_inter_sdiff : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm

@[deprecated (since := "2026-06-03")] alias diff_inter_diff := sdiff_inter_sdiff

theorem sdiff_compl : s \ tᶜ = s ∩ t :=
  _root_.sdiff_compl

@[deprecated (since := "2026-06-03")] alias diff_compl := sdiff_compl

theorem compl_sdiff : (t \ s)ᶜ = s ∪ tᶜ :=
  Eq.trans _root_.compl_sdiff himp_eq

@[deprecated (since := "2026-06-03")] alias compl_diff := compl_sdiff

theorem sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'

@[deprecated (since := "2026-06-03")] alias diff_diff_right := sdiff_sdiff_right

theorem inter_sdiff_right_comm : (s ∩ t) \ u = s \ u ∩ t := by
  rw [sdiff_eq, sdiff_eq, inter_right_comm]

@[deprecated (since := "2026-06-03")] alias diff_inter_right_comm := inter_sdiff_right_comm

@[simp]
theorem union_sdiff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _

@[deprecated (since := "2026-06-03")] alias union_diff_self := union_sdiff_self

@[simp]
theorem sdiff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _

@[deprecated (since := "2026-06-03")] alias diff_union_self := sdiff_union_self

@[simp]
theorem sdiff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias diff_inter_self := sdiff_inter_self

@[simp]
theorem sdiff_inter_self_eq_sdiff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[deprecated (since := "2026-06-03")] alias diff_inter_self_eq_diff := sdiff_inter_self_eq_sdiff

@[simp]
theorem sdiff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

@[deprecated (since := "2026-06-03")] alias diff_self_inter := sdiff_self_inter

theorem sdiff_self {s : Set α} : s \ s = ∅ :=
  _root_.sdiff_self

@[deprecated (since := "2026-06-03")] alias diff_self := sdiff_self

theorem sdiff_sdiff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  _root_.sdiff_sdiff_right_self

@[deprecated (since := "2026-06-03")] alias diff_diff_right_self := sdiff_sdiff_right_self

theorem sdiff_sdiff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

@[deprecated (since := "2026-06-03")] alias diff_diff_cancel_left := sdiff_sdiff_cancel_left

theorem union_eq_sdiff_union_sdiff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

@[deprecated (since := "2026-06-03")]
alias union_eq_diff_union_diff_union_inter := union_eq_sdiff_union_sdiff_union_inter

@[simp] lemma sdiff_sep_self (s : Set α) (p : α → Prop) : s \ {a ∈ s | p a} = {a ∈ s | ¬ p a} :=
  sdiff_self_inter

lemma disjoint_sdiff_left : Disjoint (t \ s) s := disjoint_sdiff_self_left

lemma disjoint_sdiff_right : Disjoint s (t \ s) := disjoint_sdiff_self_right

-- TODO: prove this in terms of a Boolean algebra lemma
lemma disjoint_sdiff_inter : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right inter_subset_right disjoint_sdiff_left

lemma subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u := le_iff_subset.symm.trans le_sdiff

@[deprecated (since := "2026-06-03")] alias subset_diff := subset_sdiff

lemma disjoint_of_subset_iff_left_eq_empty (h : s ⊆ t) : Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

@[simp]
lemma sdiff_ssubset_left_iff : s \ t ⊂ s ↔ (s ∩ t).Nonempty :=
  sdiff_lt_left.trans <| by rw [not_disjoint_iff_nonempty_inter, inter_comm]

@[deprecated (since := "2026-06-03")] alias diff_ssubset_left_iff := sdiff_ssubset_left_iff

lemma _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty (hst : s ⊆ t) (hs : s.Nonempty) :
    t \ s ⊂ t := by
  simpa [inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")]
alias _root_.HasSubset.Subset.diff_ssubset_of_nonempty :=
  _root_.HasSubset.Subset.sdiff_ssubset_of_nonempty

lemma ssubset_iff_sdiff_singleton : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t \ {a} := by
  grind

lemma sdiff_singleton_subset_iff : s \ {a} ⊆ t ↔ s ⊆ insert a t := by
  simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_subset_iff := sdiff_singleton_subset_iff

lemma subset_sdiff_singleton (h : s ⊆ t) (ha : a ∉ s) : s ⊆ t \ {a} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 ha

@[deprecated (since := "2026-06-03")] alias subset_diff_singleton := subset_sdiff_singleton

lemma subset_insert_sdiff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← sdiff_singleton_subset_iff]

@[deprecated (since := "2026-06-03")]
alias subset_insert_diff_singleton := subset_insert_sdiff_singleton

lemma sdiff_insert_of_notMem (h : a ∉ s) : s \ insert a t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias diff_insert_of_notMem := sdiff_insert_of_notMem

@[simp]
lemma insert_sdiff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_mem := insert_sdiff_of_mem

lemma insert_sdiff_of_notMem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  grind

@[deprecated (since := "2026-06-03")] alias insert_diff_of_notMem := insert_sdiff_of_notMem

lemma insert_sdiff_self_of_notMem (h : a ∉ s) : insert a s \ {a} = s := by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_self_of_notMem := insert_sdiff_self_of_notMem

@[simp] lemma insert_sdiff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by
  ext; simp +contextual [or_and_left, em, ha]

@[deprecated (since := "2026-06-03")] alias insert_diff_self_of_mem := insert_sdiff_self_of_mem

lemma insert_sdiff_subset : insert a s \ t ⊆ insert a (s \ t) := by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

@[deprecated (since := "2026-06-03")] alias insert_diff_subset := insert_sdiff_subset

lemma insert_erase_invOn :
    InvOn (insert a) (fun s ↦ s \ {a}) {s : Set α | a ∈ s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha ↦ insert_sdiff_self_of_mem ha, fun _s ↦ insert_sdiff_self_of_notMem⟩

@[simp]
lemma sdiff_singleton_eq_self (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [h]

@[deprecated (since := "2026-06-03")] alias diff_singleton_eq_self := sdiff_singleton_eq_self

lemma sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a ∈ s := by simp

@[deprecated (since := "2026-06-03")] alias diff_singleton_ssubset := sdiff_singleton_ssubset

@[simp]
lemma insert_sdiff_singleton : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_sdiff_self, -union_singleton, -singleton_union]

@[deprecated (since := "2026-06-03")] alias insert_diff_singleton := insert_sdiff_singleton

lemma insert_sdiff_singleton_comm (hab : a ≠ b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_sdiff_distrib,
    sdiff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[deprecated (since := "2026-06-03")]
alias insert_diff_singleton_comm := insert_sdiff_singleton_comm

@[simp]
lemma insert_sdiff_insert : insert a (s \ insert a t) = insert a (s \ t) := by
  rw [← union_singleton (s := t), ← sdiff_sdiff, insert_sdiff_singleton]

@[deprecated (since := "2026-06-03")] alias insert_diff_insert := insert_sdiff_insert

lemma mem_sdiff_singleton : a ∈ s \ {b} ↔ a ∈ s ∧ a ≠ b := .rfl

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton := mem_sdiff_singleton

lemma mem_sdiff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_sdiff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm

@[deprecated (since := "2026-06-03")] alias mem_diff_singleton_empty := mem_sdiff_singleton_empty

lemma subset_insert_iff : s ⊆ insert a t ↔ s ⊆ t ∨ (a ∈ s ∧ s \ {a} ⊆ t) := by
  grind

lemma pair_sdiff_left (hab : a ≠ b) : ({a, b} : Set α) \ {a} = {b} := by
  rw [insert_sdiff_of_mem _ (mem_singleton a), sdiff_singleton_eq_self (by simpa)]

@[deprecated (since := "2026-06-03")] alias pair_diff_left := pair_sdiff_left

lemma pair_sdiff_right (hab : a ≠ b) : ({a, b} : Set α) \ {b} = {a} := by
  rw [pair_comm, pair_sdiff_left hab.symm]

@[deprecated (since := "2026-06-03")] alias pair_diff_right := pair_sdiff_right

/-! ### If-then-else for sets -/

/-- `ite` for sets: `Set.ite t s s' ∩ t = s ∩ t`, `Set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, sdiff_inter_self, inter_assoc, inter_self, union_empty]

@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, sdiff_compl, union_comm, sdiff_eq]

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]

@[simp]
theorem ite_sdiff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[deprecated (since := "2026-06-03")] alias ite_diff_self := ite_sdiff_self

@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_sdiff _ _

@[simp]
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t := by simp [Set.ite]

@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.ite]

@[simp]
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]

@[simp]
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]

@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]

@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.ite]

theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (sdiff_subset_sdiff_left h')

theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union inter_subset_left sdiff_subset

theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ inter_subset_left inter_subset_right

theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' := by
  ext x
  unfold Set.ite
  push _ ∈ _
  tauto

theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by
  rw [ite_inter_inter, ite_same]

theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) :
    t.ite s₁ s₂ ∩ s = s₁ ∩ s := by rw [← ite_inter, ← h, ite_same]

theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' := by
  simp only [subset_def, ← forall_and]
  refine forall_congr' fun x => ?_
  by_cases hx : x ∈ t <;> simp [*, Set.ite]

theorem ite_eq_of_subset_left (t : Set α) {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) :
    t.ite s₁ s₂ = s₁ ∪ (s₂ \ t) := by
  ext x
  by_cases hx : x ∈ t <;> simp [*, Set.ite, or_iff_right_of_imp (@h x)]

theorem ite_eq_of_subset_right (t : Set α) {s₁ s₂ : Set α} (h : s₂ ⊆ s₁) :
    t.ite s₁ s₂ = (s₁ ∩ t) ∪ s₂ := by
  ext x
  by_cases hx : x ∈ t <;> simp [*, Set.ite, or_iff_left_of_imp (@h x)]

end Set
