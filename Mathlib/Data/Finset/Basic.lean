/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Directed
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Set.SymmDiff

/-!
# Basic lemmas on finite sets

This file contains lemmas on the interaction of various definitions on the `Finset` type.

For an explanation of `Finset` design decisions, please see `Mathlib/Data/Finset/Defs.lean`.

## Main declarations

### Main definitions

* `Finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Equivalences between finsets

* The `Mathlib/Logic/Equiv/Defs.lean` file describes a general type of equivalence, so look in there
  for any lemmas. There is some API for rewriting sums and products from `s` to `t` given that
  `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-02-07")]
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s := by
  cases s
  dsimp [SizeOf.sizeOf, SizeOf.sizeOf, Multiset.sizeOf]
  rw [Nat.add_comm]
  refine lt_trans ?_ (Nat.lt_succ_self _)
  exact Multiset.sizeOf_lt_sizeOf_of_mem hx

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-! #### union -/

@[simp]
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s ∪ t :=
  ext fun a => by simp

@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_union, or_imp, forall_and]

@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]

/-! #### inter -/

theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff.trans <| by simp [Finset.Nonempty]

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s ∩ t).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _

omit [DecidableEq α] in
theorem disjoint_of_subset_iff_left_eq_empty (h : s ⊆ t) :
    Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

lemma pairwiseDisjoint_iff {ι : Type*} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Lattice

instance isDirected_le : IsDirected (Finset α) (· ≤ ·) := by classical infer_instance
instance isDirected_subset : IsDirected (Finset α) (· ⊆ ·) := isDirected_le

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

@[simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl

protected lemma Nontrivial.erase_nonempty (hs : s.Nontrivial) : (s.erase a).Nonempty :=
  (hs.exists_ne a).imp <| by aesop

@[simp] lemma erase_nonempty (ha : a ∈ s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ ∈ _)]
  refine ⟨?_, fun hs ↦ hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by
  ext x
  simp

@[simp]
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a :=
  ext fun x => by
    simp +contextual only [mem_erase, mem_insert, and_congr_right_iff,
      false_or, iff_self, imp_true_iff]

theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s := by
  rw [erase_insert_eq_erase, erase_eq_of_notMem h]

theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  ext fun x => by
    have : x ≠ b ∧ x = a ↔ x = a := and_iff_right_of_imp fun hx => hx.symm ▸ h
    simp only [mem_erase, mem_insert, and_or_left, this]

theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    erase (cons a s ha) b = cons a (erase s b) fun h => ha <| erase_subset _ _ h := by
  simp only [cons_eq_insert, erase_insert_of_ne hb]

@[simp] theorem insert_erase (h : a ∈ s) : insert a (erase s a) = s :=
  ext fun x => by
    simp only [mem_insert, mem_erase, or_and_left, dec_em, true_and]
    apply or_iff_right_of_imp
    rintro rfl
    exact h

lemma erase_eq_iff_eq_insert (hs : a ∈ s) (ht : a ∉ t) : erase s a = t ↔ s = insert a t := by
  aesop

lemma insert_erase_invOn :
    Set.InvOn (insert a) (fun s ↦ erase s a) {s : Finset α | a ∈ s} {s : Finset α | a ∉ s} :=
  ⟨fun _s ↦ insert_erase, fun _s ↦ erase_insert⟩

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s :=
  calc
    s.erase a ⊂ insert a (s.erase a) := ssubset_insert <| notMem_erase _ _
    _ = _ := insert_erase h

theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  refine ⟨fun h => ?_, fun ⟨a, ha, h⟩ => ssubset_of_subset_of_ssubset h <| erase_ssubset ha⟩
  obtain ⟨a, ht, hs⟩ := not_subset.1 h.2
  exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩

theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2
    ⟨a, mem_insert_self _ _, erase_subset_erase _ <| subset_insert _ _⟩

theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by
  rw [cons_eq_insert, erase_insert_eq_erase, erase_eq_of_notMem h]

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t := by
  simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp]
  exact forall_congr' fun x => forall_swap

theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1 <| Subset.rfl

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2 <| Subset.rfl

theorem subset_insert_iff_of_notMem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_notMem h]

@[deprecated (since := "2025-05-23")]
alias subset_insert_iff_of_not_mem := subset_insert_iff_of_notMem

theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]

theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => erase s a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

end Erase

lemma Nontrivial.exists_cons_eq {s : Finset α} (hs : s.Nontrivial) :
    ∃ t a ha b hb hab, (cons b t hb).cons a (mem_cons.not.2 <| not_or_intro hab ha) = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;>
    simp [insert_erase this, insert_erase ha, *]

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

lemma erase_sdiff_erase (hab : a ≠ b) (hb : b ∈ s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

-- TODO: Do we want to delete this lemma and `Finset.disjUnion_singleton`,
-- or instead add `Finset.union_singleton`/`Finset.singleton_union`?
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ {a} = erase s a := by
  ext
  rw [mem_erase, mem_sdiff, mem_singleton, and_comm]

-- This lemma matches `Finset.insert_eq` in functionality.
theorem erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm

theorem disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]

lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]

lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]

theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjoint s t := by
  rw [← erase_insert ha, ← disjoint_erase_comm, disjoint_insert_right]
  exact ⟨notMem_erase _ _, hst⟩

theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disjoint s t := by
  rw [← erase_insert ha, disjoint_erase_comm, disjoint_insert_left]
  exact ⟨notMem_erase _ _, hst⟩

theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.erase a = (s ∩ t).erase a := by
  simp only [erase_eq, inter_sdiff_assoc]

@[simp]
theorem erase_inter (a : α) (s t : Finset α) : s.erase a ∩ t = (s ∩ t).erase a := by
  simpa only [inter_comm t] using inter_erase a t s

theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by
  simp_rw [erase_eq, sdiff_right_comm]

theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a := by
  rw [erase_inter, inter_erase]

theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a := by
  simp_rw [erase_eq, union_sdiff_distrib]

theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by simp_rw [insert_eq, union_inter_distrib_left]

theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a := by
  simp_rw [erase_eq, sdiff_sdiff, sup_sdiff_eq_sup le_rfl, sup_comm]

theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.erase a ∪ t = s ∪ t := by
  rw [← insert_erase (mem_union_right s ha), erase_union_distrib, ← union_insert, insert_erase ha]

theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.erase a = s ∪ t := by
  rw [← insert_erase (mem_union_left t ha), erase_union_distrib, ← insert_union, insert_erase ha]

theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a := by
  simp_rw [erase_eq, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]

theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  simp_rw [← sdiff_singleton_eq_erase, insert_eq, sdiff_sdiff_left', sdiff_union_distrib,
    inter_comm]

theorem sdiff_insert_insert_of_mem_of_notMem {s t : Finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  rw [sdiff_insert, insert_erase (mem_sdiff.mpr ⟨hxs, hxt⟩)]

@[deprecated (since := "2025-05-23")]
alias sdiff_insert_insert_of_mem_of_not_mem := sdiff_insert_insert_of_mem_of_notMem

theorem sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) := by
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h), insert_eq,
    union_comm]

theorem sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} := by
  rw [sdiff_erase ha, Finset.sdiff_self, insert_empty_eq]

theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]

--TODO@Yaël: Kill lemmas duplicate with `BooleanAlgebra`
theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2

theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm

theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right inter_subset_right sdiff_disjoint

end Sdiff

/-! ### attach -/

@[simp]
theorem attach_empty : attach (∅ : Finset α) = ∅ :=
  rfl

@[simp]
theorem attach_nonempty_iff {s : Finset α} : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]
theorem attach_eq_empty_iff {s : Finset α} : s.attach = ∅ ↔ s = ∅ := by
  simp [eq_empty_iff_forall_notMem]

/-! ### filter -/

section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅ := by
  classical
    ext x
    simp only [mem_singleton, forall_eq, mem_filter]
    split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']

theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    filter p (cons a s ha) = cons a (filter p s) ((mem_of_mem_filter _).mt ha) :=
  eq_of_veq <| Multiset.filter_cons_of_pos s.val hp

theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    filter p (cons a s ha) = filter p s :=
  eq_of_veq <| Multiset.filter_cons_of_neg s.val hp

theorem disjoint_filter {s : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filter p) (s.filter q) ↔ ∀ x ∈ s, p x → ¬q x := by
  constructor <;> simp +contextual [disjoint_left]

theorem disjoint_filter_filter' (s t : Finset α)
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) :
    Disjoint (s.filter p) (t.filter q) := by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a

theorem disjoint_filter_filter_neg (s t : Finset α) (p : α → Prop)
    [DecidablePred p] [∀ x, Decidable (¬p x)] :
    Disjoint (s.filter p) (t.filter fun a => ¬p a) :=
  disjoint_filter_filter' s t disjoint_compl_right

theorem filter_disjUnion (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    filter p (disjUnion s t h) = (filter p s).disjUnion (filter p t) (disjoint_filter_filter h) :=
  eq_of_veq <| Multiset.filter_add _ _ _

@[deprecated (since := "2025-06-11")]
alias filter_disj_union := filter_disjUnion

theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    filter p (cons a s ha) =
      if p a then cons a (filter p s) ((mem_of_mem_filter _).mt ha) else filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ _ _ ha h]
  · rw [filter_cons_of_neg _ _ _ ha h]

section
variable [DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
  ext fun _ => by simp only [mem_filter, mem_union, or_and_right]

theorem filter_union_right (s : Finset α) : s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x :=
  ext fun x => by simp [mem_filter, mem_union, ← and_or_left]

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filter fun i => i ∈ t) = s ∩ t :=
  ext fun i => by simp [mem_filter, mem_inter]

theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  ext
  simp [mem_filter, mem_inter, and_assoc]

theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) := by
  ext
  simp only [mem_inter, mem_filter, and_right_comm]

theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) := by
  rw [inter_comm, filter_inter, inter_comm]

theorem filter_insert (a : α) (s : Finset α) :
    filter p (insert a s) = if p a then insert a (filter p s) else filter p s := by
  ext x
  split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']

theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a := by
  ext x
  simp only [and_assoc, mem_filter, iff_self, mem_erase]

theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_union, and_or_left]

theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_inter, and_comm, and_left_comm, and_self_iff, and_assoc]

theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p :=
  ext fun a => by
    simp only [Bool.decide_coe, Bool.not_eq_true', mem_filter, and_comm, mem_sdiff, not_and_or,
      Bool.not_eq_true, and_or_left, and_not_self, or_false]

lemma filter_and_not (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    s.filter (fun a ↦ p a ∧ ¬ q a) = s.filter p \ s.filter q := by
  rw [filter_and, filter_not, ← inter_sdiff_assoc, inter_eq_left.2 (filter_subset _ _)]

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext fun _ => by simp [mem_sdiff, mem_filter]

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · simp [filter_union_right, em]
    · intro x
      simp
    · intro x
      simp only [not_not, coe_filter, Set.mem_setOf_eq, Set.mem_diff, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

-- This is not a good simp lemma, as it would prevent `Finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter (Eq b)`.
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) :
    s.filter (Eq b) = ite (b ∈ s) {b} ∅ := by
  split_ifs with h
  · ext
    simp only [mem_filter, mem_singleton, decide_eq_true_eq]
    refine ⟨fun h => h.2.symm, ?_⟩
    rintro rfl
    exact ⟨h, rfl⟩
  · ext
    simp only [mem_filter, not_and, iff_false, notMem_empty, decide_eq_true_eq]
    rintro m rfl
    exact h m

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@eq_comm _ b]) (filter_eq s b)

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b ≠ a) = s.erase b := by
  ext
  simp only [mem_filter, mem_erase, Ne, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  tauto

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]) (filter_ne s b)

theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filter p ∪ s.filter q = s :=
  (filter_or _ _ _).symm.trans <| filter_true_of_mem fun x _ => h.top_le x trivial

theorem filter_union_filter_neg_eq [∀ x, Decidable (¬p x)] (s : Finset α) :
    (s.filter p ∪ s.filter fun a => ¬p a) = s :=
  filter_union_filter_of_codisjoint _ _ _ <| @codisjoint_hnot_right _ _ p

end

end Filter

/-! ### range -/


section Range

open Nat

variable {n m l : ℕ}

@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by
  convert filter_eq (range n) m using 2
  · ext
    rw [eq_comm]
  · simp

end Range

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

@[simp]
theorem toFinset_add (s t : Multiset α) : toFinset (s + t) = toFinset s ∪ toFinset t :=
  Finset.ext <| by simp

@[simp]
theorem toFinset_inter (s t : Multiset α) : toFinset (s ∩ t) = toFinset s ∩ toFinset t :=
  Finset.ext <| by simp

@[simp]
theorem toFinset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext; simp

@[simp]
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]
theorem toFinset_nonempty : s.toFinset.Nonempty ↔ s ≠ 0 := by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty

@[simp]
theorem toFinset_filter (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    Multiset.toFinset (s.filter p) = s.toFinset.filter p := by
  ext; simp

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α} {f : α → β}
  {s : Finset α} {t : Set β} {t' : Finset β}

@[simp]
theorem toFinset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset := by
  ext
  simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty_iff

@[simp]
theorem toFinset_filter (s : List α) (p : α → Bool) :
    (s.filter p).toFinset = s.toFinset.filter (p ·) := by
  ext; simp [List.mem_filter]

end List

namespace Finset

section ToList

@[simp]
theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  Multiset.toList_eq_nil.trans val_eq_zero

theorem empty_toList {s : Finset α} : s.toList.isEmpty ↔ s = ∅ := by simp

@[simp]
theorem toList_empty : (∅ : Finset α).toList = [] :=
  toList_eq_nil.mpr rfl

theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=
  mt toList_eq_nil.mp hs.ne_empty

theorem Nonempty.not_empty_toList {s : Finset α} (hs : s.Nonempty) : ¬s.toList.isEmpty :=
  mt empty_toList.mp hs.ne_empty

end ToList

/-! ### choose -/


section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

end Finset

namespace Equiv
variable [DecidableEq α] {s t : Finset α}

open Finset

/-- The disjoint union of finsets is a sum -/
def Finset.union (s t : Finset α) (h : Disjoint s t) :
    s ⊕ t ≃ (s ∪ t : Finset α) :=
  Equiv.setCongr (coe_union _ _) |>.trans (Equiv.Set.union (disjoint_coe.mpr h)) |>.symm

@[simp]
theorem Finset.union_symm_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem Finset.union_symm_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

/-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
  type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

/-- A finset is equivalent to its coercion as a set. -/
def _root_.Finset.equivToSet (s : Finset α) : s ≃ s.toSet where
  toFun a := ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

end Equiv

namespace Multiset

variable [DecidableEq α]

@[simp]
lemma toFinset_replicate (n : ℕ) (a : α) :
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by
  ext x
  simp only [mem_toFinset, Finset.mem_singleton, mem_replicate]
  split_ifs with hn <;> simp [hn]

end Multiset
