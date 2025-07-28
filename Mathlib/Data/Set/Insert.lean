/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Disjoint

/-!
# Lemmas about insertion, singleton, and pairs

This file provides extra lemmas about `insert`, `singleton`, and `pair`.

## Tags

insert, singleton

-/

assert_not_exists HeytingAlgebra

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t : Set α} {a b : α}

/-!
### Lemmas about `insert`

`insert a s` is the set `{a} ∪ s`.
-/

theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl

@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun _ => Or.inr

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

@[deprecated (since := "2025-05-23")]
alias eq_of_not_mem_of_mem_insert := eq_of_mem_insert_of_notMem

@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext fun _ => or_iff_right_of_imp fun e => e.symm ▸ h

theorem ne_insert_of_notMem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt fun e => e.symm ▸ mem_insert _ _

@[deprecated (since := "2025-05-23")] alias ne_insert_of_not_mem := ne_insert_of_notMem

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert _ _, insert_eq_of_mem⟩

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, mem_insert_iff, or_imp, forall_and, forall_eq]

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha, hs⟩

@[gcongr]
theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun _ => Or.imp_right (@h _)

@[simp] theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  refine ⟨fun h x hx => ?_, insert_subset_insert⟩
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  exacts [(ha hx).elim, hxt]

theorem subset_insert_iff_of_notMem (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t :=
  forall₂_congr fun _ hb => or_iff_right <| ne_of_mem_of_not_mem hb ha

@[deprecated (since := "2025-05-23")]
alias subset_insert_iff_of_not_mem := subset_insert_iff_of_notMem

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := by
  simp only [insert_subset_iff, ssubset_def, not_subset]
  aesop

theorem _root_.HasSubset.Subset.ssubset_of_mem_notMem (hst : s ⊆ t) (hat : a ∈ t) (has : a ∉ s) :
    s ⊂ t := hst.ssubset_of_not_subset fun a ↦ has (a hat)

@[deprecated (since := "2025-05-23")]
alias _root_.HasSubset.Subset.ssubset_of_mem_not_mem :=
  _root_.HasSubset.Subset.ssubset_of_mem_notMem

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, Subset.rfl⟩

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun _ => or_left_comm

theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s :=
  insert_eq_of_mem <| mem_insert _ _

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
  ext fun _ => or_assoc

@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
  ext fun _ => or_left_comm

@[simp]
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

theorem insert_inter_distrib (a : α) (s t : Set α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
  ext fun _ => or_and_left

theorem insert_union_distrib (a : α) (s t : Set α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  ext fun _ => or_or_distrib_left

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
    (x) (h : x ∈ s) : P x :=
  H _ (Or.inr h)

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
    (x) (h : x ∈ insert a s) : P x :=
  h.elim (fun e => e.symm ▸ ha) (H _)

theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by
  simp [mem_insert_iff, or_and_right, exists_or]

theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
  forall₂_or_left.trans <| and_congr_left' forall_eq

/-- Inserting an element to a set is equivalent to the option type. -/
def subtypeInsertEquivOption
    [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, (mem_insert_iff.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, mem_insert_of_mem _ z.2⟩
  left_inv y := by
    by_cases h : ↑y = x
    · simp only [Subtype.ext_iff, h, Option.elim, dif_pos]
    · simp only [h, Option.elim, dif_neg, not_false_iff, Subtype.coe_eta]
  right_inv := by
    rintro (_ | y)
    · simp only [Option.elim, dif_pos]
    · have : ↑y ≠ x := by
        rintro ⟨⟩
        exact h y.2
      simp only [this, Option.elim, Subtype.eta, dif_neg, not_false_iff, Subtype.coe_mk]

/-! ### Lemmas about singletons -/

instance : LawfulSingleton α (Set α) :=
  ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩

theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_empty_eq a).symm

@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl

theorem notMem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b :=
  Iff.rfl

@[deprecated (since := "2025-05-23")] alias not_mem_singleton_iff := notMem_singleton_iff

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

theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq

theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp

@[gcongr] protected alias ⟨_, GCongr.singleton_subset_singleton⟩ := singleton_subset_singleton

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

theorem notMem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm

@[deprecated (since := "2025-05-24")] alias nmem_singleton_empty := notMem_singleton_empty

instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.eq h⟩

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
    simp [show n = 1 by omega]
  · rintro rfl
    simp

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl

@[simp]
theorem subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
  · simp [eq_singleton_iff_nonempty_unique_mem, hs, hs.ne_empty]

theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false,
    and_iff_left_iff_imp]
  exact fun h => h ▸ (singleton_ne_empty _).symm

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
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by
  ext
  rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, and_not_self_iff,
    or_false, and_iff_left_iff_imp]
  rintro rfl
  exact h

theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]

theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]

theorem inter_insert_of_notMem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
  ext fun _ => and_congr_right fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

@[deprecated (since := "2025-05-23")] alias inter_insert_of_not_mem := inter_insert_of_notMem

theorem insert_inter_of_notMem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
  ext fun _ => and_congr_left fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

@[deprecated (since := "2025-05-23")] alias insert_inter_of_not_mem := insert_inter_of_notMem

/-! ### Lemmas about pairs -/

theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  rw [insert_subset_iff, singleton_subset_iff]

theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
  pair_subset_iff.2 ⟨ha,hb⟩

theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by
  simp [subset_def]

theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  mp := by simp [subset_def, Set.ext_iff]; grind
  mpr := by simp +contextual [or_imp]

theorem Nonempty.subset_pair_iff_eq (hs : s.Nonempty) :
    s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  rw [Set.subset_pair_iff_eq, or_iff_right]; exact hs.ne_empty

/-! ### Powerset -/

/-- The powerset of a singleton contains only `∅` and the singleton itself. -/
theorem powerset_singleton (x : α) : 𝒫({x} : Set α) = {∅, {x}} := by
  ext y
  rw [mem_powerset_iff, subset_singleton_iff_eq, mem_insert_iff, mem_singleton_iff]

section
variable {α β : Type*} {a : α} {b : β}

lemma preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·) := by
  aesop

lemma preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b) := by
  aesop

end

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

/-! ### Decidability instances for sets -/

variable {α : Type u} (s t : Set α) (a b : α)

instance decidableSingleton [Decidable (a = b)] : Decidable (a ∈ ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

end Set

open Set

@[simp] theorem Prop.compl_singleton (p : Prop) : ({p}ᶜ : Set Prop) = {¬p} :=
  ext fun q ↦ by simpa [@Iff.comm q] using not_iff
