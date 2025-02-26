/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.One.Defs

/-!
# Lemmas about insertion, singleton, and pairs

This file provides extra lemmas about `insert`, `singleton`, and `pair`.

## Tags

insert, singleton

-/

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t : Set α} {a b : α}

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
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

theorem eq_of_not_mem_of_mem_insert : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right

@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext fun _ => or_iff_right_of_imp fun e => e.symm ▸ h

theorem ne_insert_of_not_mem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt fun e => e.symm ▸ mem_insert _ _

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert _ _, insert_eq_of_mem⟩

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, mem_insert_iff, or_imp, forall_and, forall_eq]

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha, hs⟩

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun _ => Or.imp_right (@h _)

@[simp] theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  refine ⟨fun h x hx => ?_, insert_subset_insert⟩
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  exacts [(ha hx).elim, hxt]

theorem subset_insert_iff_of_not_mem (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t :=
  forall₂_congr fun _ hb => or_iff_right <| ne_of_mem_of_not_mem hb ha

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := by
  simp only [insert_subset_iff, exists_and_right, ssubset_def, not_subset]
  aesop

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

/- Porting note: ∃ x ∈ insert a s, P x is parsed as ∃ x, x ∈ insert a s ∧ P x,
 where in Lean3 it was parsed as `∃ x, ∃ (h : x ∈ insert a s), P x` -/
theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by
  simp [mem_insert_iff, or_and_right, exists_and_left, exists_or]

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
    · simp only [Subtype.ext_iff, h, Option.elim, dif_pos, Subtype.coe_mk]
    · simp only [h, Option.elim, dif_neg, not_false_iff, Subtype.coe_eta, Subtype.coe_mk]
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
  (insert_emptyc_eq a).symm

@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl

theorem not_mem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b :=
  Iff.rfl

@[simp]
theorem setOf_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl

@[simp]
theorem setOf_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm

-- TODO: again, annotation needed
--Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): removed `simp` attribute
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

theorem nmem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm

instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.eq h⟩

theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff

theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <|
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

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

@[simp default+1]
lemma disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by simp [Set.disjoint_iff, subset_def]

@[simp]
lemma disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

lemma disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a ≠ b := by
  simp

lemma ssubset_iff_sdiff_singleton : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t \ {a} := by
  simp [ssubset_iff_insert, subset_diff, insert_subset_iff]; aesop

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_insert_left, disjoint_comm]

/-! ### Lemmas about complement -/

@[simp] lemma nonempty_compl_of_nontrivial [Nontrivial α] (x : α) : Set.Nonempty {x}ᶜ := by
  obtain ⟨y, hy⟩ := exists_ne x
  exact ⟨y, by simp [hy]⟩

theorem mem_compl_singleton_iff {a x : α} : x ∈ ({a} : Set α)ᶜ ↔ x ≠ a :=
  Iff.rfl

theorem compl_singleton_eq (a : α) : ({a} : Set α)ᶜ = { x | x ≠ a } :=
  rfl

@[simp]
theorem compl_ne_eq_singleton (a : α) : ({ x | x ≠ a } : Set α)ᶜ = {a} :=
  compl_compl _

@[simp]
theorem subset_compl_singleton_iff {a : α} {s : Set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
  subset_compl_comm.trans singleton_subset_iff

/-! ### Lemmas about set difference -/

@[simp]
theorem diff_singleton_subset_iff {x : α} {s t : Set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t := by
  rw [← union_singleton, union_comm]
  apply diff_subset_iff

theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 hx

theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← diff_singleton_subset_iff]

theorem diff_insert_of_not_mem {x : α} (h : x ∉ s) : s \ insert x t = s \ t := by
  refine Subset.antisymm (diff_subset_diff (refl _) (subset_insert ..)) fun y hy ↦ ?_
  simp only [mem_diff, mem_insert_iff, not_or] at hy ⊢
  exact ⟨hy.1, fun hxy ↦ h <| hxy ▸ hy.1, hy.2⟩

@[simp]
theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  ext
  constructor <;> simp +contextual [or_imp, h]

theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  classical
    ext x
    by_cases h' : x ∈ t
    · simp [h, h', ne_of_mem_of_not_mem h' h]
    · simp [h, h']

lemma insert_diff_subset : insert a s \ t ⊆ insert a (s \ t) := by
  rintro b ⟨rfl | hbs, hbt⟩ <;> simp [*]

theorem insert_diff_self_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : insert a s \ {a} = s := by
  ext x
  simp [and_iff_left_of_imp (ne_of_mem_of_not_mem · h)]

lemma insert_diff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by
  ext; simp +contextual [or_and_left, em, ha]

lemma insert_erase_invOn :
    InvOn (insert a) (fun s ↦ s \ {a}) {s : Set α | a ∈ s} {s : Set α | a ∉ s} :=
  ⟨fun _s ha ↦ insert_diff_self_of_mem ha, fun _s ↦ insert_diff_self_of_not_mem⟩

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h ▸ mem_insert a s) ha,
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

theorem inter_insert_of_not_mem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
  ext fun _ => and_congr_right fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

theorem insert_inter_of_not_mem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
  ext fun _ => and_congr_left fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [h]

@[simp]
theorem diff_singleton_sSubset {s : Set α} {a : α} : s \ {a} ⊂ s ↔ a ∈ s :=
  sdiff_le.lt_iff_ne.trans <| sdiff_eq_left.not.trans <| by simp

@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

theorem insert_diff_singleton_comm (hab : a ≠ b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_diff_distrib,
    diff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]

theorem mem_diff_singleton {x y : α} {s : Set α} : x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y :=
  Iff.rfl

theorem mem_diff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_diff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm

theorem subset_insert_iff {s t : Set α} {x : α} :
    s ⊆ insert x t ↔ s ⊆ t ∨ (x ∈ s ∧ s \ {x} ⊆ t) := by
  rw [← diff_singleton_subset_iff]
  by_cases hx : x ∈ s
  · rw [and_iff_right hx, or_iff_right_of_imp diff_subset.trans]
  rw [diff_singleton_eq_self hx, or_iff_left_of_imp And.right]

/-! ### Lemmas about pairs -/

theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

theorem pair_diff_left (hne : a ≠ b) : ({a, b} : Set α) \ {a} = {b} := by
  rw [insert_diff_of_mem _ (mem_singleton a), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right (hne : a ≠ b) : ({a, b} : Set α) \ {b} = {a} := by
  rw [pair_comm, pair_diff_left hne.symm]

theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  rw [insert_subset_iff, singleton_subset_iff]

theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
  pair_subset_iff.2 ⟨ha,hb⟩

theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by
  simp [subset_def]

theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} := by
  refine ⟨?_, by rintro (rfl | rfl | rfl | rfl) <;> simp [pair_subset_iff]⟩
  rw [subset_insert_iff, subset_singleton_iff_eq, subset_singleton_iff_eq,
    ← subset_empty_iff (s := s \ {x}), diff_subset_iff, union_empty, subset_singleton_iff_eq]
  have h : x ∈ s → {y} = s \ {x} → s = {x,y} := fun h₁ h₂ ↦ by simp [h₁, h₂]
  tauto

theorem Nonempty.subset_pair_iff_eq (hs : s.Nonempty) :
    s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  rw [Set.subset_pair_iff_eq, or_iff_right]; exact hs.ne_empty

/-! ### Powerset -/

/-- The powerset of a singleton contains only `∅` and the singleton itself. -/
theorem powerset_singleton (x : α) : 𝒫({x} : Set α) = {∅, {x}} := by
  ext y
  rw [mem_powerset_iff, subset_singleton_iff_eq, mem_insert_iff, mem_singleton_iff]

end Set

open Set

open Function

namespace Set

section
variable {α β : Type*} {a : α} {b : β}

lemma preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·) := by
  aesop

lemma preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b) := by
  aesop

end

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

end Set

/-! ### Decidability instances for sets -/

namespace Set

variable {α : Type u} (s t : Set α) (a b : α)

-- Porting note: Lean 3 unfolded `{a}` before finding instances but Lean 4 needs additional help
instance decidableSingleton [Decidable (a = b)] : Decidable (a ∈ ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

end Set

@[simp] theorem Prop.compl_singleton (p : Prop) : ({p}ᶜ : Set Prop) = {¬p} :=
  ext fun q ↦ by simpa [@Iff.comm q] using not_iff
