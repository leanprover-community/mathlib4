/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.main
! leanprover-community/mathlib commit 4d4167104581a21259f7f448e1972a63a4546be7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rbtree.Find
import Mathlib.Data.Rbtree.Insert
import Mathlib.Data.Rbtree.MinMax
import Mathlib.Order.RelClasses

universe u

namespace Rbnode

variable {α : Type u} {lt : α → α → Prop}

theorem isSearchable_of_wellFormed {t : Rbnode α} [IsStrictWeakOrder α lt] :
    t.WellFormed lt → IsSearchable lt t none none := by
  intro h; induction h
  · constructor; simp [lift]
  · subst h_n'; apply is_searchable_insert; assumption
#align rbnode.is_searchable_of_well_formed Rbnode.isSearchable_of_wellFormed

open Color

theorem isRedBlack_of_wellFormed {t : Rbnode α} : t.WellFormed lt → ∃ c n, IsRedBlack t c n := by
  intro h; induction h
  · exists black; exists 0; constructor
  · cases' h_ih with c ih; cases' ih with n ih; subst h_n'; apply insert_is_red_black; assumption
#align rbnode.is_red_black_of_well_formed Rbnode.isRedBlack_of_wellFormed

end Rbnode

namespace Rbtree

variable {α : Type u} {lt : α → α → Prop}

theorem balanced (t : Rbtree α lt) : t.depth max ≤ 2 * t.depth min + 1 := by
  cases' t with n p; simp only [depth]
  have := Rbnode.isRedBlack_of_wellFormed p
  cases' this with _ this; cases' this with _ this
  apply Rbnode.balanced; assumption
#align rbtree.balanced Rbtree.balanced

theorem not_mem_mkRbtree : ∀ a : α, a ∉ mkRbtree α lt := by
  simp [Membership.Mem, Rbtree.Mem, Rbnode.Mem, mkRbtree]
#align rbtree.not_mem_mk_rbtree Rbtree.not_mem_mkRbtree

theorem not_mem_of_empty {t : Rbtree α lt} (a : α) : t.Empty = true → a ∉ t := by
  cases' t with n p <;> cases n <;>
    simp [Empty, Membership.Mem, Rbtree.Mem, Rbnode.Mem, false_imp_iff]
#align rbtree.not_mem_of_empty Rbtree.not_mem_of_empty

theorem mem_of_mem_of_eqv [IsStrictWeakOrder α lt] {t : Rbtree α lt} {a b : α} :
    a ∈ t → a ≈[lt]b → b ∈ t := by
  cases' t with n p <;> simp [Membership.Mem, Rbtree.Mem] <;> clear p <;> induction n <;>
        simp only [Rbnode.Mem, StrictWeakOrder.Equiv, false_imp_iff] <;>
      intro h₁ h₂ <;>
    cases_type* or.1
  iterate 2 
    · have : Rbnode.Mem lt b n_lchild := n_ih_lchild h₁ h₂; simp [this]
    · simp [incomp_trans_of lt h₂.swap h₁]
    · have : Rbnode.Mem lt b n_rchild := n_ih_rchild h₁ h₂; simp [this]
#align rbtree.mem_of_mem_of_eqv Rbtree.mem_of_mem_of_eqv

section Dec

variable [DecidableRel lt]

theorem insert_ne_mkRbtree (t : Rbtree α lt) (a : α) : t.insert a ≠ mkRbtree α lt := by
  cases' t with n p
  simpa [insert, mkRbtree] using Rbnode.insert_ne_leaf lt n a
#align rbtree.insert_ne_mk_rbtree Rbtree.insert_ne_mkRbtree

theorem find_correct [IsStrictWeakOrder α lt] (a : α) (t : Rbtree α lt) :
    a ∈ t ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b := by cases t; apply Rbnode.find_correct;
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.find_correct Rbtree.find_correct

theorem find_correct_of_total [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) :
    a ∈ t ↔ t.find a = some a :=
  Iff.intro
    (fun h =>
      match Iff.mp (find_correct a t) h with
      | ⟨b, HEq, heqv⟩ => by simp [HEq, (eq_of_eqv_lt heqv).symm])
    fun h => Iff.mpr (find_correct a t) ⟨a, ⟨h, refl a⟩⟩
#align rbtree.find_correct_of_total Rbtree.find_correct_of_total

theorem find_correct_exact [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) :
    MemExact a t ↔ t.find a = some a := by cases t; apply Rbnode.find_correct_exact;
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.find_correct_exact Rbtree.find_correct_exact

theorem find_insert_of_eqv [IsStrictWeakOrder α lt] (t : Rbtree α lt) {x y} :
    x ≈[lt]y → (t.insert x).find y = some x := by
  cases t; intro h; apply Rbnode.find_insert_of_eqv lt h; apply Rbnode.isSearchable_of_wellFormed
  assumption
#align rbtree.find_insert_of_eqv Rbtree.find_insert_of_eqv

theorem find_insert [IsStrictWeakOrder α lt] (t : Rbtree α lt) (x) : (t.insert x).find x = some x :=
  find_insert_of_eqv t (refl x)
#align rbtree.find_insert Rbtree.find_insert

theorem find_insert_of_disj [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
    lt x y ∨ lt y x → (t.insert x).find y = t.find y := by
  cases t; intro h; apply Rbnode.find_insert_of_disj lt h
  apply Rbnode.isSearchable_of_wellFormed
  assumption
#align rbtree.find_insert_of_disj Rbtree.find_insert_of_disj

theorem find_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
    ¬x ≈[lt]y → (t.insert x).find y = t.find y := by
  cases t; intro h; apply Rbnode.find_insert_of_not_eqv lt h
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.find_insert_of_not_eqv Rbtree.find_insert_of_not_eqv

theorem find_insert_of_ne [IsStrictTotalOrder α lt] {x y : α} (t : Rbtree α lt) :
    x ≠ y → (t.insert x).find y = t.find y := by
  cases t; intro h
  have : ¬x ≈[lt]y := fun h' => h (eq_of_eqv_lt h')
  apply Rbnode.find_insert_of_not_eqv lt this
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.find_insert_of_ne Rbtree.find_insert_of_ne

theorem not_mem_of_find_none [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
    t.find a = none → a ∉ t := fun h =>
  Iff.mpr (not_congr (find_correct a t)) <| by
    intro h
    cases' h with _ h; cases' h with h₁ h₂
    rw [h] at h₁ ; contradiction
#align rbtree.not_mem_of_find_none Rbtree.not_mem_of_find_none

theorem eqv_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
    t.find a = some b → a ≈[lt]b := by cases t; apply Rbnode.eqv_of_find_some;
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.eqv_of_find_some Rbtree.eqv_of_find_some

theorem eq_of_find_some [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} :
    t.find a = some b → a = b := fun h =>
  suffices a ≈[lt]b from eq_of_eqv_lt this
  eqv_of_find_some h
#align rbtree.eq_of_find_some Rbtree.eq_of_find_some

theorem mem_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
    t.find a = some b → a ∈ t := fun h => Iff.mpr (find_correct a t) ⟨b, ⟨h, eqv_of_find_some h⟩⟩
#align rbtree.mem_of_find_some Rbtree.mem_of_find_some

theorem find_eq_find_of_eqv [IsStrictWeakOrder α lt] {a b : α} (t : Rbtree α lt) :
    a ≈[lt]b → t.find a = t.find b := by
  cases t; apply Rbnode.find_eq_find_of_eqv
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.find_eq_find_of_eqv Rbtree.find_eq_find_of_eqv

theorem contains_correct [IsStrictWeakOrder α lt] (a : α) (t : Rbtree α lt) :
    a ∈ t ↔ t.contains a = true := by
  have h := find_correct a t
  simp [h, contains]; apply Iff.intro
  · intro h'; cases' h' with _ h'; cases h'; simp [*]; simp [Option.isSome]
  · intro h'
    cases' heq : find t a with v; simp [HEq, Option.isSome] at h' ; contradiction
    exists v; simp; apply eqv_of_find_some HEq
#align rbtree.contains_correct Rbtree.contains_correct

theorem mem_insert_of_incomp {a b : α} (t : Rbtree α lt) : ¬lt a b ∧ ¬lt b a → a ∈ t.insert b := by
  cases t; apply Rbnode.mem_insert_of_incomp
#align rbtree.mem_insert_of_incomp Rbtree.mem_insert_of_incomp

theorem mem_insert [IsIrrefl α lt] : ∀ (a : α) (t : Rbtree α lt), a ∈ t.insert a := by intros;
  apply mem_insert_of_incomp; constructor <;> apply irrefl_of lt
#align rbtree.mem_insert Rbtree.mem_insert

theorem mem_insert_of_equiv {a b : α} (t : Rbtree α lt) : a ≈[lt]b → a ∈ t.insert b := by cases t;
  apply Rbnode.mem_insert_of_incomp
#align rbtree.mem_insert_of_equiv Rbtree.mem_insert_of_equiv

theorem mem_insert_of_mem [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} (b : α) :
    a ∈ t → a ∈ t.insert b := by cases t; apply Rbnode.mem_insert_of_mem
#align rbtree.mem_insert_of_mem Rbtree.mem_insert_of_mem

theorem equiv_or_mem_of_mem_insert {a b : α} {t : Rbtree α lt} :
    a ∈ t.insert b → a ≈[lt]b ∨ a ∈ t := by cases t; apply Rbnode.equiv_or_mem_of_mem_insert
#align rbtree.equiv_or_mem_of_mem_insert Rbtree.equiv_or_mem_of_mem_insert

theorem incomp_or_mem_of_mem_ins {a b : α} {t : Rbtree α lt} :
    a ∈ t.insert b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t :=
  equiv_or_mem_of_mem_insert
#align rbtree.incomp_or_mem_of_mem_ins Rbtree.incomp_or_mem_of_mem_ins

theorem eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} :
    a ∈ t.insert b → a = b ∨ a ∈ t := fun h =>
  suffices a ≈[lt]b ∨ a ∈ t by simp [eqv_lt_iff_eq] at this  <;> assumption
  incomp_or_mem_of_mem_ins h
#align rbtree.eq_or_mem_of_mem_ins Rbtree.eq_or_mem_of_mem_ins

end Dec

theorem mem_of_min_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.min = some a → a ∈ t := by
  cases t; apply Rbnode.mem_of_min_eq
#align rbtree.mem_of_min_eq Rbtree.mem_of_min_eq

theorem mem_of_max_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.max = some a → a ∈ t := by
  cases t; apply Rbnode.mem_of_max_eq
#align rbtree.mem_of_max_eq Rbtree.mem_of_max_eq

theorem eq_leaf_of_min_eq_none {t : Rbtree α lt} : t.min = none → t = mkRbtree α lt := by cases t;
  intro h; congr; apply Rbnode.eq_leaf_of_min_eq_none h
#align rbtree.eq_leaf_of_min_eq_none Rbtree.eq_leaf_of_min_eq_none

theorem eq_leaf_of_max_eq_none {t : Rbtree α lt} : t.max = none → t = mkRbtree α lt := by cases t;
  intro h; congr; apply Rbnode.eq_leaf_of_max_eq_none h
#align rbtree.eq_leaf_of_max_eq_none Rbtree.eq_leaf_of_max_eq_none

theorem min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
    t.min = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt a b := by
  classical
  cases t
  apply Rbnode.min_is_minimal
  apply Rbnode.isSearchable_of_wellFormed
  assumption
#align rbtree.min_is_minimal Rbtree.min_is_minimal

theorem max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
    t.max = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt b a := by cases t; apply Rbnode.max_is_maximal;
  apply Rbnode.isSearchable_of_wellFormed; assumption
#align rbtree.max_is_maximal Rbtree.max_is_maximal

end Rbtree

