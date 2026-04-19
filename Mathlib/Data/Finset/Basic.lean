/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.SymmDiff

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

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-! #### union -/

@[simp]
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s ∪ t := by grind

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
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Lattice

instance isDirected_le : IsDirectedOrder (Finset α) := by classical infer_instance
instance isDirected_subset : IsDirected (Finset α) (· ⊆ ·) := isDirected_le

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

@[simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl

protected lemma Nontrivial.erase_nonempty (hs : s.Nontrivial) : (s.erase a).Nonempty :=
  (hs.exists_ne a).imp <| by simp_all

@[simp] lemma erase_nonempty (ha : a ∈ s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ ∈ _)]
  refine ⟨?_, fun hs ↦ hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by
  ext x; simp

@[simp]
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a := by
  ext x
  simp only [mem_erase, mem_insert]
  constructor
  · rintro ⟨hne, rfl | hx⟩
    · exact absurd rfl hne
    · exact ⟨hne, hx⟩
  · rintro ⟨hne, hx⟩
    exact ⟨hne, Or.inr hx⟩

theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).erase a = s := by
  ext x
  simp only [mem_erase, mem_insert]
  constructor
  · rintro ⟨hne, rfl | hx⟩
    · exact absurd rfl hne
    · exact hx
  · intro hx
    exact ⟨fun heq => h (heq ▸ hx), Or.inr hx⟩

theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    (insert a s).erase b = insert a (s.erase b) := by grind

theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    (s.cons a ha).erase b = (s.erase b).cons a fun h => ha <| erase_subset _ _ h := by grind

@[simp] theorem insert_erase (h : a ∈ s) : insert a (s.erase a) = s := by
  ext x
  simp only [mem_insert, mem_erase]
  constructor
  · rintro (rfl | ⟨_, hx⟩)
    · exact h
    · exact hx
  · intro hx
    by_cases ha : x = a
    · exact Or.inl ha
    · exact Or.inr ⟨ha, hx⟩

lemma erase_eq_iff_eq_insert (hs : a ∈ s) (ht : a ∉ t) : s.erase a = t ↔ s = insert a t := by
  aesop

lemma insert_erase_invOn :
    Set.InvOn (insert a) (fun s ↦ s.erase a) {s : Finset α | a ∈ s} {s : Finset α | a ∉ s} :=
  ⟨fun _s ↦ insert_erase, fun _s ↦ erase_insert⟩

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s := by grind

theorem erase_union_eq (a : α) (s : Finset α) (h : a ∈ s) : (erase s a) ∪ {a} = s := by grind

theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  grind

theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, by grw [← subset_insert]⟩

theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by grind

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ s.erase a ⊆ t := by
  constructor
  · intro h x hx
    have hne : x ≠ a := (mem_erase.mp hx).1
    have hs : x ∈ s := (mem_erase.mp hx).2
    exact (mem_insert.mp (h hs)).resolve_left hne
  · intro h x hx
    by_cases ha : x = a
    · exact ha ▸ mem_insert_self a t
    · exact mem_insert_of_mem (h (mem_erase.mpr ⟨ha, hx⟩))

theorem erase_insert_subset (a : α) (s : Finset α) : (insert a s).erase a ⊆ s :=
  subset_insert_iff.1 Subset.rfl

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (s.erase a) :=
  subset_insert_iff.2 Subset.rfl

theorem subset_insert_iff_of_notMem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_notMem h]

theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]

theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => s.erase a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

end Erase

lemma Nontrivial.exists_cons_eq {s : Finset α} (hs : s.Nontrivial) :
    ∃ t a ha b hb hab, (cons b t hb).cons a (mem_cons.not.2 <| not_or_intro hab ha) = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;> simp [insert_erase ha, *]

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

lemma erase_sdiff_erase (hab : a ≠ b) (hb : b ∈ s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

-- TODO: Do we want to delete this lemma and `Finset.disjUnion_singleton`,
-- or instead add `Finset.union_singleton`/`Finset.singleton_union`?
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ {a} = s.erase a := by grind

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

theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.erase a = (s ∩ t).erase a := by grind

@[simp]
theorem erase_inter (a : α) (s t : Finset α) : s.erase a ∩ t = (s ∩ t).erase a := by grind

theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by grind

theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a := by grind

theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a := by
  grind

theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by grind

theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a := by
  grind

theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.erase a ∪ t = s ∪ t := by
  grind

theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.erase a = s ∪ t := by
  grind

theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a := by
  grind

theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  grind

theorem sdiff_insert_insert_of_mem_of_notMem {s t : Finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  grind

theorem sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) := by
  grind

theorem sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} := by
  grind

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
theorem attach_empty : (∅ : Finset α).attach = ∅ :=
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

theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅ := by grind

theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    (s.cons a ha).filter p = (s.filter p).cons a ((mem_of_mem_filter _).mt ha) :=
  eq_of_veq <| s.val.filter_cons_of_pos hp

theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    (s.cons a ha).filter p = s.filter p :=
  eq_of_veq <| s.val.filter_cons_of_neg hp

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

theorem disjoint_filter_filter_not (s t : Finset α) (p : α → Prop)
    [DecidablePred p] [∀ x, Decidable (¬p x)] :
    Disjoint (s.filter p) (t.filter fun a => ¬p a) :=
  s.disjoint_filter_filter' t disjoint_compl_right

@[deprecated (since := "2025-12-12")] alias disjoint_filter_filter_neg := disjoint_filter_filter_not

theorem filter_disjUnion (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    (s.disjUnion t h).filter p = (s.filter p).disjUnion (t.filter p) (disjoint_filter_filter h) :=
  eq_of_veq <| Multiset.filter_add _ _ _

theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).filter p =
      if p a then (s.filter p).cons a ((mem_of_mem_filter _).mt ha) else s.filter p := by grind

@[simp]
theorem disjoint_disjUnion_left {s t u : Finset α} (h : Disjoint s t) :
    Disjoint (s.disjUnion t h) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_disjUnion, or_imp, forall_and]

@[simp]
theorem disjoint_disjUnion_right {s t u : Finset α} (h : Disjoint t u) :
    Disjoint s (t.disjUnion u h) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_disjUnion, or_imp, forall_and]

section
variable [DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p := by
  grind

theorem filter_union_right (s : Finset α) :
    s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x := by grind

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filter fun i => i ∈ t) = s ∩ t := by
  ext; simp

theorem filter_notMem_eq_sdiff {s t : Finset α} [∀ i, Decidable (i ∉ t)] :
    (s.filter fun i => i ∉ t) = s \ t := by grind

theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  grind

theorem filter_inter (s t : Finset α) : s.filter p ∩ t = (s ∩ t).filter p := by grind

theorem inter_filter (s t : Finset α) : s ∩ t.filter p = (s ∩ t).filter p := by grind

theorem filter_insert (a : α) (s : Finset α) :
    (insert a s).filter p = if p a then insert a (s.filter p) else s.filter p := by grind

theorem filter_erase (a : α) (s : Finset α) : (s.erase a).filter p = (s.filter p).erase a := by
  grind

theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q := by
  grind

theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q := by
  grind

theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p := by
  grind

lemma filter_and_not (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    s.filter (fun a ↦ p a ∧ ¬ q a) = s.filter p \ s.filter q := by grind

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁.filter (· ∉ s₂) := by grind

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · grind
    · grind
    · intro x
      simp only [coe_filter, Set.mem_setOf_eq, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

-- This is not a good simp lemma, as it would prevent `Finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter (Eq b)`.
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) :
    s.filter (Eq b) = ite (b ∈ s) {b} ∅ := by grind

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ := by grind

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b ≠ a) = s.erase b := by grind

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]).trans (s.filter_ne b)

theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filter p ∪ s.filter q = s :=
  (filter_or _ _ _).symm.trans <| filter_true_of_mem fun x _ => h.top_le x trivial

theorem filter_union_filter_not_eq [∀ x, Decidable (¬p x)] (s : Finset α) :
    (s.filter p ∪ s.filter fun a => ¬p a) = s :=
  filter_union_filter_of_codisjoint _ _ _ <| @codisjoint_hnot_right _ _ p

@[deprecated (since := "2025-12-12")] alias filter_union_filter_neg_eq := filter_union_filter_not_eq

end

end Filter

/-! ### range -/


section Range

open Nat

variable {n m l : ℕ}

@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by grind

@[simp]
theorem range_inter_range (m n : ℕ) : range m ∩ range n = range (min m n) := by ext; simp

@[simp]
theorem range_union_range (m n : ℕ) : range m ∪ range n = range (max m n) := by ext; simp

end Range

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

@[simp]
theorem toFinset_add (s t : Multiset α) : (s + t).toFinset = s.toFinset ∪ t.toFinset :=
  Finset.ext <| by simp

@[simp]
theorem toFinset_inter (s t : Multiset α) : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset :=
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
    (s.filter p).toFinset = s.toFinset.filter p := by
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
  l.val.chooseX p hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  l.chooseX p hp

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : l.choose p hp ∈ l ∧ p (l.choose p hp) :=
  (l.chooseX p hp).property

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : l.choose p hp ∈ l :=
  (choose_spec _ _ _).1

grind_pattern choose_mem => l.choose p hp

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (l.choose p hp) :=
  (choose_spec _ _ _).2

grind_pattern choose_property => l.choose p hp

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
theorem Finset.union_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem Finset.union_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
theorem Finset.union_symm_left (h : Disjoint s t) {i : α} (hi : i ∈ s)
    (hi' : i ∈ s ∪ t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
theorem Finset.union_symm_right (h : Disjoint s t) {i : α} (hi : i ∈ t)
    (hi' : i ∈ s ∪ t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/-- The disjoint union of finsets is a sum -/
def Finset.disjUnionEquiv (s t : Finset α) (h : Disjoint s t) :
    s ⊕ t ≃ s.disjUnion t h :=
  Equiv.setCongr (coe_disjUnion h) |>.trans (Equiv.Set.union (disjoint_coe.mpr h)) |>.symm

@[simp]
theorem Finset.disjUnionEquiv_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.disjUnionEquiv s t h (Sum.inl x) = ⟨x, Finset.mem_disjUnion.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem Finset.disjUnionEquiv_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.disjUnionEquiv s t h (Sum.inr y) = ⟨y, Finset.mem_disjUnion.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
theorem Finset.disjUnionEquiv_symm_left (h : Disjoint s t) {i : α} (hi : i ∈ s)
    (hi' : i ∈ s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
theorem Finset.disjUnionEquiv_symm_right (h : Disjoint s t) {i : α} (hi : i ∈ t)
    (hi' : i ∈ s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
  type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

set_option backward.isDefEq.respectTransparency false in
lemma piFinsetUnion_left {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
    piFinsetUnion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_left h hi hi']
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma piFinsetUnion_right {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ t) (hi' : i ∈ s ∪ t) :
    Equiv.piFinsetUnion α h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_right h hi hi']
  rfl

/-- A finset is equivalent to its coercion as a set. -/
def _root_.Finset.equivToSet (s : Finset α) : s ≃ (s : Set α) where
  toFun a := ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

end Equiv

namespace Multiset

variable [DecidableEq α]

@[simp]
lemma toFinset_replicate (n : ℕ) (a : α) :
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by
  ext x
  simp only [mem_toFinset, mem_replicate]
  split_ifs with hn <;> simp [hn]

end Multiset

namespace Finset

variable {α : Type*}

theorem mem_union_of_disjoint [DecidableEq α]
    {s t : Finset α} (h : Disjoint s t) {x : α} :
    x ∈ s ∪ t ↔ Xor' (x ∈ s) (x ∈ t) := by
  rw [Finset.mem_union, Xor']
  have := disjoint_left.1 h
  tauto

@[simp]
theorem univ_finset_of_isEmpty [h : IsEmpty α] : (Set.univ : Set (Finset α)) = {∅} :=
  subset_antisymm (fun S hS ↦ by simp [Finset.eq_empty_of_isEmpty S]) (by simp)

theorem isEmpty_of_forall_eq_empty (H : ∀ s : Finset α, s = ∅) : IsEmpty α :=
  isEmpty_iff.mpr fun a ↦ by specialize H {a}; aesop

@[simp]
theorem univ_finset_eq_singleton_empty_iff : @Set.univ (Finset α) = {∅} ↔ IsEmpty α :=
  ⟨fun h ↦ isEmpty_of_forall_eq_empty fun s ↦ Set.mem_singleton_iff.mp
    (Set.ext_iff.mp h s |>.mp (Set.mem_univ s)), fun _ ↦ by simp⟩

end Finset
