/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Insert

/-!
# Disjoint finite sets

## Main declarations

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.disjUnion`: the union of the finite sets `s` and `t`, given a proof `Disjoint s t`

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

/-! ### disjoint -/


section Disjoint

variable {f : α → β} {s t u : Finset α} {a b : α}

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => notMem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_left_finset := Disjoint.notMem_of_mem_left_finset

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by
  rw [_root_.disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_right_finset := Disjoint.notMem_of_mem_right_finset

theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp]
theorem disjoint_val : Disjoint s.1 t.1 ↔ Disjoint s t :=
  Multiset.disjoint_left.trans disjoint_left.symm

theorem _root_.Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb

theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  disjoint_left.not.trans <| not_forall.trans <| exists_congr fun _ => by
    rw [Classical.not_imp, not_not]

theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)

theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right

@[simp]
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

-- Not `simp` since `disjoint_singleton_{left,right}` prove it.
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]

theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]

@[simp, norm_cast]
theorem pairwiseDisjoint_coe {ι : Type*} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι → Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe

variable [DecidableEq α]

instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidable_of_iff _ disjoint_left.symm

end Disjoint

/-! ### disjoint union -/


/-- `disjUnion s t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
@[simps]
def disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp, grind =, push]
theorem mem_disjUnion {α s t h a} : a ∈ @disjUnion α s t h ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append

@[simp, norm_cast]
theorem coe_disjUnion {s t : Finset α} (h : Disjoint s t) :
    (disjUnion s t h : Set α) = (s : Set α) ∪ t :=
  Set.ext <| by simp

theorem disjUnion_comm (s t : Finset α) (h : Disjoint s t) :
    disjUnion s t h = disjUnion t s h.symm :=
  eq_of_veq <| Multiset.add_comm _ _

@[simp]
theorem disjUnion_inj_left {s₁ s₂ t : Finset α} (h₁ : Disjoint s₁ t) (h₂ : Disjoint s₂ t) :
    s₁.disjUnion t h₁ = s₂.disjUnion t h₂ ↔ s₁ = s₂ := by
  simp [← val_inj, Multiset.add_left_inj]

@[simp]
theorem disjUnion_inj_right {s t₁ t₂ : Finset α} (h₁ : Disjoint s t₁) (h₂ : Disjoint s t₂) :
    s.disjUnion t₁ h₁ = s.disjUnion t₂ h₂ ↔ t₁ = t₂ := by
  simp [← val_inj, Multiset.add_right_inj]

@[simp]
theorem empty_disjUnion (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left) :
    disjUnion ∅ t h = t :=
  eq_of_veq <| Multiset.zero_add _

@[simp]
theorem disjUnion_empty (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right) :
    disjUnion s ∅ h = s :=
  eq_of_veq <| Multiset.add_zero _

theorem singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) :
    disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h) :=
  eq_of_veq <| Multiset.singleton_add _ _

theorem disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) :
    disjUnion s {a} h = cons a s (disjoint_singleton_right.mp h) := by
  rw [disjUnion_comm, singleton_disjUnion]

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t u v : Finset α} {a b : α} {f : α → β}

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, _root_.disjoint_comm]

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
theorem disjoint_toFinset {m1 m2 : Multiset α} :
    _root_.Disjoint m1.toFinset m2.toFinset ↔ Disjoint m1 m2 := by
  simp [disjoint_left, Finset.disjoint_left]

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
theorem disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset.trans (Multiset.coe_disjoint _ _)

end List
