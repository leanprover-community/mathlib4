/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Aesop
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Tactic.Simproc.ExistsAndEq

/-!
# Lemmas about insertion, singleton, and pairs

This file provides extra lemmas about `insert`, `singleton`, and `pair`.

## Tags

insert, singleton

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists HeytingAlgebra

/-! ### Set coercion to a type -/

open Function

namespace Set

variable {α β : Type*} {s t : Set α} {a b : α}

/-!
### Lemmas about `insert`

`insert a s` is the set `{a} ∪ s`.
-/

theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl

@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun _ => Or.inr

-- This is a fairly aggressive pattern; it might be safer to use
-- `s ⊆ insert x s` or `_ ⊆ insert x s` instead.
-- Currently Cslib relies on this.
-- See `MathlibTest/grind/set.lean` for a test case illustrating the reasoning
-- that Cslib is relying on.
grind_pattern subset_insert => insert x s

theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl

theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr

theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id

theorem mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s :=
  Or.resolve_left

theorem eq_of_mem_insert_of_notMem : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right

@[simp, grind =, push]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s := by grind

theorem ne_insert_of_notMem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t := by grind

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s := by grind

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s := by grind

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by grind

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t := by grind

@[gcongr]
theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := by grind

@[simp] theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by grind

theorem subset_insert_iff_of_notMem (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by grind

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := by grind

theorem _root_.HasSubset.Subset.ssubset_of_mem_notMem (hst : s ⊆ t) (hat : a ∈ t) (has : a ∉ s) :
    s ⊂ t := by grind

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s := by grind

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) := by
  grind

theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s := by grind

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) := by grind

@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) := by grind

@[simp]
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

theorem insert_inter_distrib (a : α) (s t : Set α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by grind

theorem insert_union_distrib (a : α) (s t : Set α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by grind

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
    (x) (h : x ∈ s) : P x := by grind

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
    (x) (h : x ∈ insert a s) : P x := by grind

theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by grind

theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x := by grind

/-- Inserting an element to a set is equivalent to the option type. -/
def subtypeInsertEquivOption
    [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

/-! ### Lemmas about singletons -/

instance : LawfulSingleton α (Set α) :=
  ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩

theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_empty_eq a).symm

@[simp, grind =, push]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl

theorem notMem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b :=
  Iff.rfl

@[simp]
theorem setOf_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl

@[simp]
theorem setOf_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm

-- TODO: again, annotation needed
-- Not `@[simp]` since `mem_singleton_iff` proves it.
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h

@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  Set.ext_iff.trans eq_iff_eq_cancel_left

theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
  singleton_eq_singleton_iff.mp

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H

theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
  (singleton_nonempty _).ne_empty

@[simp]
theorem empty_ne_singleton (a : α) : ∅ ≠ ({a} : Set α) :=
  (singleton_ne_empty a).symm

theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, grind =]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq

@[gcongr]
theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp

theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl

@[simp]
theorem singleton_union : {a} ∪ s = insert a s :=
  rfl

@[simp]
theorem union_singleton : s ∪ {a} = insert a s :=
  union_comm _ _

@[simp]
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by
  rw [inter_comm, singleton_inter_nonempty]

@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm, singleton_inter_eq_empty]

@[simp] alias ⟨_, singleton_inter_of_notMem⟩ := singleton_inter_eq_empty
@[simp] alias ⟨_, inter_singleton_of_notMem⟩ := inter_singleton_eq_empty

@[simp] lemma singleton_inter_of_mem (ha : a ∈ s) : {a} ∩ s = {a} := by simpa
@[simp] lemma inter_singleton_of_mem (ha : a ∈ s) : s ∩ {a} = {a} := by simpa

theorem notMem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm

instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.ext h⟩

theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff

theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <|
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

theorem setOf_mem_list_eq_replicate {l : List α} {a : α} :
    { x | x ∈ l } = {a} ↔ ∃ n > 0, l = List.replicate n a := by
  simpa +contextual [Set.ext_iff, iff_iff_implies_and_implies, forall_and, List.eq_replicate_iff,
    List.length_pos_iff_exists_mem] using ⟨fun _ _ ↦ ⟨_, ‹_›⟩, fun x hx h ↦ h _ hx ▸ hx⟩

theorem setOf_mem_list_eq_singleton_of_nodup {l : List α} (H : l.Nodup) {a : α} :
    { x | x ∈ l } = {a} ↔ l = [a] := by
  constructor
  · rw [setOf_mem_list_eq_replicate]
    rintro ⟨n, hn, rfl⟩
    simp only [List.nodup_replicate] at H
    simp [show n = 1 by lia]
  · rintro rfl
    simp

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl

@[simp]
theorem subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by grind

theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false,
    and_iff_left_iff_imp]
  exact fun h => h ▸ empty_ne_singleton _

theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

theorem eq_of_nonempty_of_subsingleton {α} [Subsingleton α] (s t : Set α) [Nonempty s]
    [Nonempty t] : s = t :=
  Nonempty.of_subtype.eq_univ.trans Nonempty.of_subtype.eq_univ.symm

theorem eq_of_nonempty_of_subsingleton' {α} [Subsingleton α] {s : Set α} (t : Set α)
    (hs : s.Nonempty) [Nonempty t] : s = t :=
  have := hs.to_subtype; eq_of_nonempty_of_subsingleton s t

theorem Nonempty.eq_zero [Subsingleton α] [Zero α] {s : Set α} (h : s.Nonempty) :
    s = {0} := eq_of_nonempty_of_subsingleton' {0} h

theorem Nonempty.eq_one [Subsingleton α] [One α] {s : Set α} (h : s.Nonempty) :
    s = {1} := eq_of_nonempty_of_subsingleton' {1} h

/-! ### Disjointness -/

@[simp default + 1]
lemma disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by simp [Set.disjoint_iff, subset_def]

@[simp]
lemma disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

lemma disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a ≠ b := by
  simp

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_insert_left, disjoint_comm]

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩

@[simp]
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by grind

theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by grind

theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by grind

theorem inter_insert_of_notMem (h : a ∉ s) : s ∩ insert a t = s ∩ t := by grind

theorem insert_inter_of_notMem (h : a ∉ t) : insert a s ∩ t = s ∩ t := by grind

/-! ### Lemmas about pairs -/

theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by grind

theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
  pair_subset_iff.2 ⟨ha,hb⟩

theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by grind

theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  mp := by grind
  mpr := by grind

theorem Nonempty.subset_pair_iff_eq (hs : s.Nonempty) :
    s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  rw [Set.subset_pair_iff_eq, or_iff_right]; exact hs.ne_empty

theorem range_ite_const {p : α → Prop} [DecidablePred p] {x y : β}
    (hp : ∃ a, p a) (hn : ∃ a, ¬ p a) :
    Set.range (fun a ↦ if p a then x else y) = {x, y} := by
  grind

/-! ### Powerset -/

/-- The powerset of a singleton contains only `∅` and the singleton itself. -/
theorem powerset_singleton (x : α) : 𝒫 {x} = {∅, {x}} := by grind

section
variable {α β : Type*} {a : α} {b : β}

lemma preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·) := by
  grind

lemma preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b) := by
  grind

end

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

/-! ### Decidability instances for sets -/

variable (s t : Set α) (a b : α)

instance decidableSingleton [Decidable (a = b)] : Decidable (a ∈ ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

end Set

open Set

@[simp] theorem Prop.compl_singleton (p : Prop) : ({p}ᶜ : Set Prop) = {¬p} :=
  ext fun q ↦ by simpa [@Iff.comm q] using not_iff
