/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbmap.default
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rbmap.Basic
import Mathlib.Data.Rbtree.Main

universe u v

namespace Rbmap

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

-- Auxiliary instances
private def rbmap_lt_is_swo {α : Type u} {β : Type v} {lt : α → α → Prop} [IsStrictWeakOrder α lt] :
    IsStrictWeakOrder (α × β) (RbmapLt lt) where
  irrefl _ := irrefl_of lt _
  trans _ _ _ h₁ h₂ := trans_of lt h₁ h₂
  incomp_trans _ _ _ h₁ h₂ := incomp_trans_of lt h₁ h₂

private def rbmapLtDec {α : Type u} {β : Type v} {lt : α → α → Prop} [h : DecidableRel lt] :
    DecidableRel (@RbmapLt α β lt) := fun a b => h a.1 b.1

attribute [local instance] rbmap_lt_is_swo rbmap_lt_dec

-- Helper lemmas for reusing rbtree results.
private theorem to_rbtree_mem {k : α} {m : Rbmap α β lt} : k ∈ m → ∃ v : β, Rbtree.Mem (k, v) m :=
  by
  cases' m with n p <;> cases n <;> intro h
  · exact False.elim h
  all_goals exists n_val.2; exact h

private theorem eqv_entries_of_eqv_keys {k₁ k₂ : α} (v₁ v₂ : β) :
    k₁ ≈[lt]k₂ → (k₁, v₁) ≈[RbmapLt lt](k₂, v₂) :=
  id

private theorem eqv_keys_of_eqv_entries {k₁ k₂ : α} {v₁ v₂ : β} :
    (k₁, v₁) ≈[RbmapLt lt](k₂, v₂) → k₁ ≈[lt]k₂ :=
  id

private theorem eqv_entries [IsIrrefl α lt] (k : α) (v₁ v₂ : β) : (k, v₁) ≈[RbmapLt lt](k, v₂) :=
  And.intro (irrefl_of lt k) (irrefl_of lt k)

private theorem to_rbmap_mem [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    Rbtree.Mem (k, v) m → k ∈ m := by
  cases' m with n p <;> cases n <;> intro h
  · exact False.elim h
  · simp [Membership.Mem, Rbmap.Mem]
    exact
      @Rbtree.mem_of_mem_of_eqv _ _ _ ⟨Rbnode.red_node n_lchild n_val n_rchild, p⟩ _ _ h
        (eqv_entries _ _ _)
  · simp [Membership.Mem, Rbmap.Mem]
    exact
      @Rbtree.mem_of_mem_of_eqv _ _ _ ⟨Rbnode.black_node n_lchild n_val n_rchild, p⟩ _ _ h
        (eqv_entries _ _ _)

private theorem to_rbtree_mem' [IsStrictWeakOrder α lt] {k : α} {m : Rbmap α β lt} (v : β) :
    k ∈ m → Rbtree.Mem (k, v) m := by
  intro h
  cases' to_rbtree_mem h with v' hm
  apply Rbtree.mem_of_mem_of_eqv hm
  apply eqv_entries

theorem eq_some_of_toValue_eq_some {e : Option (α × β)} {v : β} :
    toValue e = some v → ∃ k, e = some (k, v) := by
  cases' e with val <;> simp [to_value, false_imp_iff]
  · cases val; simp
#align rbmap.eq_some_of_to_value_eq_some Rbmap.eq_some_of_toValue_eq_some

theorem eq_none_of_toValue_eq_none {e : Option (α × β)} : toValue e = none → e = none := by
  cases e <;> simp [to_value, false_imp_iff]
#align rbmap.eq_none_of_to_value_eq_none Rbmap.eq_none_of_toValue_eq_none

-- Lemmas
theorem not_mem_mkRbmap : ∀ k : α, k ∉ mkRbmap α β lt := by
  simp [Membership.Mem, mkRbmap, mkRbtree, Rbmap.Mem]
#align rbmap.not_mem_mk_rbmap Rbmap.not_mem_mkRbmap

theorem not_mem_of_empty {m : Rbmap α β lt} (k : α) : m.Empty = true → k ∉ m := by
  cases' m with n p <;> cases n <;>
    simp [Membership.Mem, mkRbmap, mkRbtree, Rbmap.Mem, Rbmap.empty, Rbtree.empty, false_imp_iff]
#align rbmap.not_mem_of_empty Rbmap.not_mem_of_empty

theorem mem_of_mem_of_eqv [IsStrictWeakOrder α lt] {m : Rbmap α β lt} {k₁ k₂ : α} :
    k₁ ∈ m → k₁ ≈[lt]k₂ → k₂ ∈ m := by
  intro h₁ h₂
  have h₁ := to_rbtree_mem h₁; cases' h₁ with v h₁
  exact to_rbmap_mem (Rbtree.mem_of_mem_of_eqv h₁ (eqv_entries_of_eqv_keys v v h₂))
#align rbmap.mem_of_mem_of_eqv Rbmap.mem_of_mem_of_eqv

section Decidable

variable [DecidableRel lt]

theorem not_mem_of_findEntry_none [IsStrictWeakOrder α lt] {k : α} {m : Rbmap α β lt} :
    m.findEntry k = none → k ∉ m := by
  cases' m with t p; cases t <;> simp [find_entry]
  · intros; simp [Membership.Mem, Rbmap.Mem]
  all_goals intro h; exact Rbtree.not_mem_of_find_none h
#align rbmap.not_mem_of_find_entry_none Rbmap.not_mem_of_findEntry_none

theorem not_mem_of_find_none [IsStrictWeakOrder α lt] {k : α} {m : Rbmap α β lt} :
    m.find k = none → k ∉ m := by
  simp [find]; intro h
  have := eq_none_of_to_value_eq_none h
  exact not_mem_of_find_entry_none this
#align rbmap.not_mem_of_find_none Rbmap.not_mem_of_find_none

theorem mem_of_findEntry_some [IsStrictWeakOrder α lt] {k₁ : α} {e : α × β} {m : Rbmap α β lt} :
    m.findEntry k₁ = some e → k₁ ∈ m := by
  cases' m with t p; cases t <;> simp [find_entry, false_imp_iff]
  all_goals intro h; exact Rbtree.mem_of_find_some h
#align rbmap.mem_of_find_entry_some Rbmap.mem_of_findEntry_some

theorem mem_of_find_some [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.find k = some v → k ∈ m := by
  simp [find]; intro h
  have := eq_some_of_to_value_eq_some h
  cases' this with _ he
  exact mem_of_find_entry_some he
#align rbmap.mem_of_find_some Rbmap.mem_of_find_some

theorem findEntry_eq_findEntry_of_eqv [IsStrictWeakOrder α lt] {m : Rbmap α β lt} {k₁ k₂ : α} :
    k₁ ≈[lt]k₂ → m.findEntry k₁ = m.findEntry k₂ := by
  intro h; cases' m with t p; cases t <;> simp [find_entry]
  all_goals apply Rbtree.find_eq_find_of_eqv; apply eqv_entries_of_eqv_keys; assumption
#align rbmap.find_entry_eq_find_entry_of_eqv Rbmap.findEntry_eq_findEntry_of_eqv

theorem find_eq_find_of_eqv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) :
    k₁ ≈[lt]k₂ → m.find k₁ = m.find k₂ := by intro h; simp [find]; apply congr_arg;
  apply find_entry_eq_find_entry_of_eqv; assumption
#align rbmap.find_eq_find_of_eqv Rbmap.find_eq_find_of_eqv

theorem findEntry_correct [IsStrictWeakOrder α lt] (k : α) (m : Rbmap α β lt) :
    k ∈ m ↔ ∃ e, m.findEntry k = some e ∧ k ≈[lt]e.1 := by
  apply Iff.intro <;> cases' m with t p
  · intro h
    have h := to_rbtree_mem h; cases' h with v h₁
    have hex := Iff.mp (Rbtree.find_correct _ _) h₁; cases' hex with e h₂
    exists e; cases t <;> simp [find_entry] at h₂ ⊢
    · simp [Rbtree.find, Rbnode.find] at h₂ ; cases h₂
    · cases' h₂ with h₂₁ h₂₂; constructor
      · have :=
          Rbtree.find_eq_find_of_eqv ⟨Rbnode.red_node t_lchild t_val t_rchild, p⟩
            (eqv_entries k v t_val.2)
        rw [← this]; exact h₂₁
      · cases e; apply eqv_keys_of_eqv_entries h₂₂
    · cases' h₂ with h₂₁ h₂₂; constructor
      · have :=
          Rbtree.find_eq_find_of_eqv ⟨Rbnode.black_node t_lchild t_val t_rchild, p⟩
            (eqv_entries k v t_val.2)
        rw [← this]; exact h₂₁
      · cases e; apply eqv_keys_of_eqv_entries h₂₂
  · intro h; cases' h with e h
    cases' h with h₁ h₂; cases t <;> simp [find_entry] at h₁ 
    · contradiction
    all_goals exact to_rbmap_mem (Rbtree.mem_of_find_some h₁)
#align rbmap.find_entry_correct Rbmap.findEntry_correct

theorem eqv_of_findEntry_some [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
    m.findEntry k₁ = some (k₂, v) → k₁ ≈[lt]k₂ := by
  cases' m with t p; cases t <;> simp [find_entry, false_imp_iff]
  all_goals intro h; exact eqv_keys_of_eqv_entries (Rbtree.eqv_of_find_some h)
#align rbmap.eqv_of_find_entry_some Rbmap.eqv_of_findEntry_some

theorem eq_of_findEntry_some [IsStrictTotalOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
    m.findEntry k₁ = some (k₂, v) → k₁ = k₂ := fun h =>
  suffices k₁ ≈[lt]k₂ from eq_of_eqv_lt this
  eqv_of_findEntry_some h
#align rbmap.eq_of_find_entry_some Rbmap.eq_of_findEntry_some

theorem find_correct [IsStrictWeakOrder α lt] (k : α) (m : Rbmap α β lt) :
    k ∈ m ↔ ∃ v, m.find k = some v := by
  apply Iff.intro
  · intro h
    have := Iff.mp (find_entry_correct k m) h
    cases' this with e h; cases' h with h₁ h₂
    exists e.2; simp [find, h₁, to_value]
  · intro h
    cases' h with v h
    simp [find] at h 
    have h := eq_some_of_to_value_eq_some h
    cases' h with k' h
    have heqv := eqv_of_find_entry_some h
    exact Iff.mpr (find_entry_correct k m) ⟨(k', v), ⟨h, heqv⟩⟩
#align rbmap.find_correct Rbmap.find_correct

theorem constains_correct [IsStrictWeakOrder α lt] (k : α) (m : Rbmap α β lt) :
    k ∈ m ↔ m.contains k = true := by
  apply Iff.intro
  · intro h
    have h := Iff.mp (find_entry_correct k m) h
    cases' h with e h; cases' h with h₁ h₂
    simp [contains, h₁, Option.isSome]
  · simp [contains]
    intro h
    generalize he : find_entry m k = e
    cases e
    · simp [he, Option.isSome] at h ; contradiction
    · exact mem_of_find_entry_some he
#align rbmap.constains_correct Rbmap.constains_correct

theorem mem_insert_of_incomp [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ → k₁ ∈ m.insert k₂ v := fun h =>
  to_rbmap_mem (Rbtree.mem_insert_of_incomp m (eqv_entries_of_eqv_keys v v h))
#align rbmap.mem_insert_of_incomp Rbmap.mem_insert_of_incomp

theorem mem_insert [IsStrictWeakOrder α lt] (k : α) (m : Rbmap α β lt) (v : β) : k ∈ m.insert k v :=
  to_rbmap_mem (Rbtree.mem_insert (k, v) m)
#align rbmap.mem_insert Rbmap.mem_insert

theorem mem_insert_of_equiv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    k₁ ≈[lt]k₂ → k₁ ∈ m.insert k₂ v :=
  mem_insert_of_incomp m v
#align rbmap.mem_insert_of_equiv Rbmap.mem_insert_of_equiv

theorem mem_insert_of_mem [IsStrictWeakOrder α lt] {k₁ : α} {m : Rbmap α β lt} (k₂ : α) (v : β) :
    k₁ ∈ m → k₁ ∈ m.insert k₂ v := fun h =>
  to_rbmap_mem (Rbtree.mem_insert_of_mem (k₂, v) (to_rbtree_mem' v h))
#align rbmap.mem_insert_of_mem Rbmap.mem_insert_of_mem

theorem equiv_or_mem_of_mem_insert [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
    k₁ ∈ m.insert k₂ v → k₁ ≈[lt]k₂ ∨ k₁ ∈ m := fun h =>
  Or.elim (Rbtree.equiv_or_mem_of_mem_insert (to_rbtree_mem' v h))
    (fun h => Or.inl (eqv_keys_of_eqv_entries h)) fun h => Or.inr (to_rbmap_mem h)
#align rbmap.equiv_or_mem_of_mem_insert Rbmap.equiv_or_mem_of_mem_insert

theorem incomp_or_mem_of_mem_ins [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
    k₁ ∈ m.insert k₂ v → ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ ∨ k₁ ∈ m :=
  equiv_or_mem_of_mem_insert
#align rbmap.incomp_or_mem_of_mem_ins Rbmap.incomp_or_mem_of_mem_ins

theorem eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
    k₁ ∈ m.insert k₂ v → k₁ = k₂ ∨ k₁ ∈ m := fun h =>
  suffices k₁ ≈[lt]k₂ ∨ k₁ ∈ m by simp [eqv_lt_iff_eq] at this  <;> assumption
  incomp_or_mem_of_mem_ins h
#align rbmap.eq_or_mem_of_mem_ins Rbmap.eq_or_mem_of_mem_ins

theorem findEntry_insert_of_eqv [IsStrictWeakOrder α lt] (m : Rbmap α β lt) {k₁ k₂ : α} (v : β) :
    k₁ ≈[lt]k₂ → (m.insert k₁ v).findEntry k₂ = some (k₁, v) := by
  intro h
  generalize h₁ : m.insert k₁ v = m'
  cases' m' with t p; cases t
  · have := mem_insert k₁ m v; rw [h₁] at this ; apply absurd this; apply not_mem_mk_rbmap
  all_goals
    simp [find_entry]; rw [← h₁, insert]; apply Rbtree.find_insert_of_eqv
    apply eqv_entries_of_eqv_keys _ _ h
#align rbmap.find_entry_insert_of_eqv Rbmap.findEntry_insert_of_eqv

theorem findEntry_insert [IsStrictWeakOrder α lt] (m : Rbmap α β lt) (k : α) (v : β) :
    (m.insert k v).findEntry k = some (k, v) :=
  findEntry_insert_of_eqv m v (refl k)
#align rbmap.find_entry_insert Rbmap.findEntry_insert

theorem find_insert_of_eqv [IsStrictWeakOrder α lt] (m : Rbmap α β lt) {k₁ k₂ : α} (v : β) :
    k₁ ≈[lt]k₂ → (m.insert k₁ v).find k₂ = some v := by
  intro h
  have := find_entry_insert_of_eqv m v h
  simp [find, this, to_value]
#align rbmap.find_insert_of_eqv Rbmap.find_insert_of_eqv

theorem find_insert [IsStrictWeakOrder α lt] (m : Rbmap α β lt) (k : α) (v : β) :
    (m.insert k v).find k = some v :=
  find_insert_of_eqv m v (refl k)
#align rbmap.find_insert Rbmap.find_insert

theorem findEntry_insert_of_disj [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    lt k₁ k₂ ∨ lt k₂ k₁ → (m.insert k₁ v).findEntry k₂ = m.findEntry k₂ := by
  intro h
  have h' : ∀ {v₁ v₂ : β}, (RbmapLt lt) (k₁, v₁) (k₂, v₂) ∨ (RbmapLt lt) (k₂, v₂) (k₁, v₁) :=
    fun _ _ => h
  generalize h₁ : m = m₁
  generalize h₂ : insert m₁ k₁ v = m₂
  rw [← h₁] at h₂ ⊢; rw [← h₂]
  cases' m₁ with t₁ p₁ <;> cases t₁ <;> cases' m₂ with t₂ p₂ <;> cases t₂
  · rw [h₂, h₁]
  iterate 2 
    rw [h₂]
    conv =>
      lhs
      simp [find_entry]
    rw [← h₂, insert, Rbtree.find_insert_of_disj _ h', h₁]
    rfl
  any_goals
    simp [insert] at h₂ 
    exact absurd h₂ (Rbtree.insert_ne_mkRbtree m (k₁, v))
  any_goals
    rw [h₂, h₁]; simp [find_entry]; rw [← h₂, ← h₁, insert, Rbtree.find_insert_of_disj _ h']
    apply Rbtree.find_eq_find_of_eqv; apply eqv_entries
#align rbmap.find_entry_insert_of_disj Rbmap.findEntry_insert_of_disj

theorem findEntry_insert_of_not_eqv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt)
    (v : β) : ¬k₁ ≈[lt]k₂ → (m.insert k₁ v).findEntry k₂ = m.findEntry k₂ := by
  intro hn
  have he : lt k₁ k₂ ∨ lt k₂ k₁ := by
    simp [StrictWeakOrder.Equiv, Decidable.not_and_iff_or_not, Decidable.not_not_iff] at hn 
    assumption
  apply find_entry_insert_of_disj _ _ he
#align rbmap.find_entry_insert_of_not_eqv Rbmap.findEntry_insert_of_not_eqv

theorem findEntry_insert_of_ne [IsStrictTotalOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    k₁ ≠ k₂ → (m.insert k₁ v).findEntry k₂ = m.findEntry k₂ := by
  intro h
  have : ¬k₁ ≈[lt]k₂ := fun h' => h (eq_of_eqv_lt h')
  apply find_entry_insert_of_not_eqv _ _ this
#align rbmap.find_entry_insert_of_ne Rbmap.findEntry_insert_of_ne

theorem find_insert_of_disj [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    lt k₁ k₂ ∨ lt k₂ k₁ → (m.insert k₁ v).find k₂ = m.find k₂ := by intro h;
  have := find_entry_insert_of_disj m v h; simp [find, this]
#align rbmap.find_insert_of_disj Rbmap.find_insert_of_disj

theorem find_insert_of_not_eqv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    ¬k₁ ≈[lt]k₂ → (m.insert k₁ v).find k₂ = m.find k₂ := by intro h;
  have := find_entry_insert_of_not_eqv m v h; simp [find, this]
#align rbmap.find_insert_of_not_eqv Rbmap.find_insert_of_not_eqv

theorem find_insert_of_ne [IsStrictTotalOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
    k₁ ≠ k₂ → (m.insert k₁ v).find k₂ = m.find k₂ := by intro h;
  have := find_entry_insert_of_ne m v h; simp [find, this]
#align rbmap.find_insert_of_ne Rbmap.find_insert_of_ne

end Decidable

theorem mem_of_min_eq [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.min = some (k, v) → k ∈ m := fun h => to_rbmap_mem (Rbtree.mem_of_min_eq h)
#align rbmap.mem_of_min_eq Rbmap.mem_of_min_eq

theorem mem_of_max_eq [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.max = some (k, v) → k ∈ m := fun h => to_rbmap_mem (Rbtree.mem_of_max_eq h)
#align rbmap.mem_of_max_eq Rbmap.mem_of_max_eq

theorem eq_leaf_of_min_eq_none {m : Rbmap α β lt} : m.min = none → m = mkRbmap α β lt :=
  Rbtree.eq_leaf_of_min_eq_none
#align rbmap.eq_leaf_of_min_eq_none Rbmap.eq_leaf_of_min_eq_none

theorem eq_leaf_of_max_eq_none {m : Rbmap α β lt} : m.max = none → m = mkRbmap α β lt :=
  Rbtree.eq_leaf_of_max_eq_none
#align rbmap.eq_leaf_of_max_eq_none Rbmap.eq_leaf_of_max_eq_none

theorem min_is_minimal [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.min = some (k, v) → ∀ {k'}, k' ∈ m → k ≈[lt]k' ∨ lt k k' := fun h k' hm =>
  Or.elim (Rbtree.min_is_minimal h (to_rbtree_mem' v hm))
    (fun h => Or.inl (eqv_keys_of_eqv_entries h)) fun h => Or.inr h
#align rbmap.min_is_minimal Rbmap.min_is_minimal

theorem max_is_maximal [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.max = some (k, v) → ∀ {k'}, k' ∈ m → k ≈[lt]k' ∨ lt k' k := fun h k' hm =>
  Or.elim (Rbtree.max_is_maximal h (to_rbtree_mem' v hm))
    (fun h => Or.inl (eqv_keys_of_eqv_entries h)) fun h => Or.inr h
#align rbmap.max_is_maximal Rbmap.max_is_maximal

theorem min_is_minimal_of_total [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.min = some (k, v) → ∀ {k'}, k' ∈ m → k = k' ∨ lt k k' := fun h k' hm =>
  match min_is_minimal h hm with
  | Or.inl h => Or.inl (eq_of_eqv_lt h)
  | Or.inr h => Or.inr h
#align rbmap.min_is_minimal_of_total Rbmap.min_is_minimal_of_total

theorem max_is_maximal_of_total [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
    m.max = some (k, v) → ∀ {k'}, k' ∈ m → k = k' ∨ lt k' k := fun h k' hm =>
  match max_is_maximal h hm with
  | Or.inl h => Or.inl (eq_of_eqv_lt h)
  | Or.inr h => Or.inr h
#align rbmap.max_is_maximal_of_total Rbmap.max_is_maximal_of_total

end Rbmap

