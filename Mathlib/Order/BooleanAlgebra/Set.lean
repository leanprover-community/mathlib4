/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Insert
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Boolean algebra of sets

This file proves that `Set α` is a boolean algebra, and proves results about set difference and
complement.

## Notation

* `sᶜ` for the complement of `s`

## Tags

set, sets, subset, subsets, complement
-/

assert_not_exists RelIso

open Function

namespace Set
variable {α β : Type*} {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

instance instBooleanAlgebra : BooleanAlgebra (Set α) where
  __ : DistribLattice (Set α) := inferInstance
  __ : BooleanAlgebra (α → Prop) := inferInstance
  compl := (·ᶜ)
  sdiff := (· \ ·)

/-- See also `Set.sdiff_inter_right_comm`. -/
lemma inter_diff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) := inf_sdiff_assoc ..

/-- See also `Set.inter_diff_assoc`. -/
lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..

lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..

theorem diff_union_diff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

/-- A version of `diff_union_diff_cancel` with more general hypotheses. -/
theorem diff_union_diff_cancel' (hi : s ∩ u ⊆ t) (hu : t ⊆ s ∪ u) : (s \ t) ∪ (t \ u) = s \ u :=
  sdiff_sup_sdiff_cancel' hi hu

theorem diff_diff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u := sdiff_sdiff_eq_sdiff_sup h

theorem inter_diff_distrib_left (s t u : Set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
  inf_sdiff_distrib_left _ _ _

theorem inter_diff_distrib_right (s t u : Set α) : (s \ t) ∩ u = (s ∩ u) \ (t ∩ u) :=
  inf_sdiff_distrib_right _ _ _

theorem diff_inter_distrib_right (s t r : Set α) : (t ∩ r) \ s = (t \ s) ∩ (r \ s) :=
  inf_sdiff

/-! ### Lemmas about complement -/

theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h

theorem compl_setOf {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl

theorem notMem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h

@[deprecated (since := "2025-05-23")] alias not_mem_of_mem_compl := notMem_of_mem_compl

theorem notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not

@[deprecated (since := "2025-05-23")] alias not_mem_compl_iff := notMem_compl_iff

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
  rw [compl_union]
  aesop

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

theorem notMem_diff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx

@[deprecated (since := "2025-05-23")] alias not_mem_diff_of_mem := notMem_diff_of_mem

theorem mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left

theorem notMem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right

@[deprecated (since := "2025-05-23")] alias not_mem_of_mem_diff := notMem_of_mem_diff

theorem diff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [diff_eq, inter_comm]

theorem diff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff

theorem diff_subset {s t : Set α} : s \ t ⊆ s := show s \ t ≤ s from sdiff_le

theorem diff_subset_compl (s t : Set α) : s \ t ⊆ tᶜ :=
  diff_eq_compl_inter ▸ inter_subset_left

theorem union_diff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂

theorem union_diff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h

theorem union_diff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left <| disjoint_iff_inf_le.2 h

theorem union_diff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right <| disjoint_iff_inf_le.2 h

@[simp]
theorem union_diff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self

@[simp]
theorem union_diff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem union_diff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff

@[simp]
theorem inter_diff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right

@[simp]
theorem inter_union_diff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t

@[simp]
theorem diff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s := by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_diff _ _

theorem subset_inter_union_compl_left (s t : Set α) : t ⊆ s ∩ t ∪ sᶜ := by
  simp [inter_union_distrib_right]

theorem subset_inter_union_compl_right (s t : Set α) : s ⊆ s ∩ t ∪ tᶜ := by
  simp [inter_union_distrib_right]

theorem union_inter_compl_left_subset (s t : Set α) : (s ∪ t) ∩ sᶜ ⊆ t := by
  simp [union_inter_distrib_right]

theorem union_inter_compl_right_subset (s t : Set α) : (s ∪ t) ∩ tᶜ ⊆ s := by
  simp [union_inter_distrib_right]

@[gcongr]
theorem diff_subset_diff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂ from sdiff_le_sdiff

theorem diff_subset_diff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›

theorem diff_subset_diff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›

theorem diff_subset_diff_iff_subset {r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht

theorem compl_eq_univ_diff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm

@[simp]
theorem empty_diff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff

theorem diff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[simp]
theorem diff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot

@[simp]
theorem diff_univ (s : Set α) : s \ univ = ∅ :=
  diff_eq_empty.2 (subset_univ s)

theorem diff_diff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left

-- the following statement contains parentheses to help the reader
theorem diff_diff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  sdiff_sdiff_comm

theorem diff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff

theorem subset_diff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  show s ≤ s \ t ∪ t from le_sdiff_sup

theorem diff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset diff_subset h) (subset_diff_union _ _)

theorem diff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm

theorem diff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

theorem diff_inter_diff : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm

theorem diff_compl : s \ tᶜ = s ∩ t :=
  sdiff_compl

theorem compl_diff : (t \ s)ᶜ = s ∪ tᶜ :=
  Eq.trans compl_sdiff himp_eq

theorem diff_diff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'

theorem inter_diff_right_comm : (s ∩ t) \ u = s \ u ∩ t := by
  rw [diff_eq, diff_eq, inter_right_comm]

theorem diff_inter_right_comm : (s \ u) ∩ t = (s ∩ t) \ u := by
  rw [diff_eq, diff_eq, inter_right_comm]

@[simp]
theorem union_diff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _

@[simp]
theorem diff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _

@[simp]
theorem diff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left

@[simp]
theorem diff_inter_self_eq_diff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[simp]
theorem diff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

theorem diff_self {s : Set α} : s \ s = ∅ :=
  sdiff_self

theorem diff_diff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self

theorem diff_diff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

theorem union_eq_diff_union_diff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

@[simp] lemma sdiff_sep_self (s : Set α) (p : α → Prop) : s \ {a ∈ s | p a} = {a ∈ s | ¬ p a} :=
  diff_self_inter

lemma disjoint_sdiff_left : Disjoint (t \ s) s := disjoint_sdiff_self_left

lemma disjoint_sdiff_right : Disjoint s (t \ s) := disjoint_sdiff_self_right

-- TODO: prove this in terms of a boolean algebra lemma
lemma disjoint_sdiff_inter : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right inter_subset_right disjoint_sdiff_left

lemma subset_diff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u := le_iff_subset.symm.trans le_sdiff

lemma disjoint_of_subset_iff_left_eq_empty (h : s ⊆ t) : Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

@[simp]
lemma diff_ssubset_left_iff : s \ t ⊂ s ↔ (s ∩ t).Nonempty :=
  sdiff_lt_left.trans <| by rw [not_disjoint_iff_nonempty_inter, inter_comm]

lemma _root_.HasSubset.Subset.diff_ssubset_of_nonempty (hst : s ⊆ t) (hs : s.Nonempty) :
    t \ s ⊂ t := by
  simpa [inter_eq_self_of_subset_right hst]

lemma ssubset_iff_sdiff_singleton : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t \ {a} := by
  simp [ssubset_iff_insert, subset_diff, insert_subset_iff]; aesop

@[simp]
lemma diff_singleton_subset_iff : s \ {a} ⊆ t ↔ s ⊆ insert a t := by
  rw [← union_singleton, union_comm]
  apply diff_subset_iff

lemma subset_diff_singleton (h : s ⊆ t) (ha : a ∉ s) : s ⊆ t \ {a} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 ha

lemma subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← diff_singleton_subset_iff]

lemma diff_insert_of_notMem (h : a ∉ s) : s \ insert a t = s \ t := by
  grind

@[deprecated (since := "2025-05-23")] alias diff_insert_of_not_mem := diff_insert_of_notMem

@[simp]
lemma insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  grind

lemma insert_diff_of_notMem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  grind

@[deprecated (since := "2025-05-23")] alias insert_diff_of_not_mem := insert_diff_of_notMem

lemma insert_diff_self_of_notMem (h : a ∉ s) : insert a s \ {a} = s := by
  ext x; simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

@[deprecated (since := "2025-05-23")]
alias insert_diff_self_of_not_mem := insert_diff_self_of_notMem

@[simp] lemma insert_diff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by
  ext; simp +contextual [or_and_left, em, ha]

lemma insert_diff_subset : insert a s \ t ⊆ insert a (s \ t) := by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

lemma insert_erase_invOn :
    InvOn (insert a) (fun s ↦ s \ {a}) {s : Set α | a ∈ s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha ↦ insert_diff_self_of_mem ha, fun _s ↦ insert_diff_self_of_notMem⟩

@[simp]
lemma diff_singleton_eq_self (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [h]

lemma diff_singleton_ssubset : s \ {a} ⊂ s ↔ a ∈ s := by simp

@[deprecated (since := "2025-03-20")] alias diff_singleton_sSubset := diff_singleton_ssubset

@[simp]
lemma insert_diff_singleton : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

lemma insert_diff_singleton_comm (hab : a ≠ b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_diff_distrib,
    diff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

@[simp]
lemma insert_diff_insert : insert a (s \ insert a t) = insert a (s \ t) := by
  rw [← union_singleton (s := t), ← diff_diff, insert_diff_singleton]

lemma mem_diff_singleton : a ∈ s \ {b} ↔ a ∈ s ∧ a ≠ b := .rfl

lemma mem_diff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_diff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm

lemma subset_insert_iff : s ⊆ insert a t ↔ s ⊆ t ∨ (a ∈ s ∧ s \ {a} ⊆ t) := by
  grind

lemma pair_diff_left (hab : a ≠ b) : ({a, b} : Set α) \ {a} = {b} := by
  rw [insert_diff_of_mem _ (mem_singleton a), diff_singleton_eq_self (by simpa)]

lemma pair_diff_right (hab : a ≠ b) : ({a, b} : Set α) \ {b} = {a} := by
  rw [pair_comm, pair_diff_left hab.symm]

/-! ### If-then-else for sets -/

/-- `ite` for sets: `Set.ite t s s' ∩ t = s ∩ t`, `Set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]

@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, diff_compl, union_comm, diff_eq]

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]

@[simp]
theorem ite_diff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_diff _ _

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
  union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')

theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union inter_subset_left diff_subset

theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ inter_subset_left inter_subset_right

theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' := by
  ext x
  simp only [Set.ite, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
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
