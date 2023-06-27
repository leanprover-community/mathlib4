/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.min_max
! leanprover-community/mathlib commit 8f6fd1b69096c6a587f745d354306c0d46396915
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rbtree.Basic

universe u

namespace Rbnode

variable {α : Type u} {lt : α → α → Prop}

theorem mem_of_min_eq (lt : α → α → Prop) [IsIrrefl α lt] {a : α} {t : Rbnode α} :
    t.min = some a → Mem lt a t := by
  induction t
  · intros; contradiction
  all_goals
    cases t_lchild <;> simp [Rbnode.min] <;> intro h
    · subst t_val; simp [mem, irrefl_of lt a]
    all_goals rw [mem]; simp [t_ih_lchild h]
#align rbnode.mem_of_min_eq Rbnode.mem_of_min_eq

theorem mem_of_max_eq (lt : α → α → Prop) [IsIrrefl α lt] {a : α} {t : Rbnode α} :
    t.max = some a → Mem lt a t := by
  induction t
  · intros; contradiction
  all_goals
    cases t_rchild <;> simp [Rbnode.max] <;> intro h
    · subst t_val; simp [mem, irrefl_of lt a]
    all_goals rw [mem]; simp [t_ih_rchild h]
#align rbnode.mem_of_max_eq Rbnode.mem_of_max_eq

variable [IsStrictWeakOrder α lt]

theorem eq_leaf_of_min_eq_none {t : Rbnode α} : t.min = none → t = leaf := by
  induction t
  · intros; rfl
  all_goals
    cases t_lchild <;> simp [Rbnode.min, false_imp_iff] <;> intro h
    all_goals have := t_ih_lchild h; contradiction
#align rbnode.eq_leaf_of_min_eq_none Rbnode.eq_leaf_of_min_eq_none

theorem eq_leaf_of_max_eq_none {t : Rbnode α} : t.max = none → t = leaf := by
  induction t
  · intros; rfl
  all_goals
    cases t_rchild <;> simp [Rbnode.max, false_imp_iff] <;> intro h
    all_goals have := t_ih_rchild h; contradiction
#align rbnode.eq_leaf_of_max_eq_none Rbnode.eq_leaf_of_max_eq_none

theorem min_is_minimal {a : α} {t : Rbnode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → t.min = some a → ∀ {b}, Mem lt b t → a ≈[lt]b ∨ lt a b :=
  by
  classical
  induction t
  · simp [StrictWeakOrder.Equiv]; intro _ _ hs hmin b; contradiction
  all_goals
    cases t_lchild <;> intro lo hi hs hmin b hmem
    · simp [Rbnode.min] at hmin ; subst t_val
      simp [mem] at hmem ; cases' hmem with heqv hmem
      · left; exact heqv.swap
      · have := lt_of_mem_right hs (by constructor) hmem
        right; assumption
    all_goals
      have hs' := hs
      cases hs; simp [Rbnode.min] at hmin 
      rw [mem] at hmem ; cases_type* or.1
      · exact t_ih_lchild hs_hs₁ hmin hmem
      · have hmm := mem_of_min_eq lt hmin
        have a_lt_val := lt_of_mem_left hs' (by constructor) hmm
        have a_lt_b := lt_of_lt_of_incomp a_lt_val hmem.swap
        right; assumption
      · have hmm := mem_of_min_eq lt hmin
        have a_lt_b := lt_of_mem_left_right hs' (by constructor) hmm hmem
        right; assumption
#align rbnode.min_is_minimal Rbnode.min_is_minimal

theorem max_is_maximal {a : α} {t : Rbnode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → t.max = some a → ∀ {b}, Mem lt b t → a ≈[lt]b ∨ lt b a :=
  by
  classical
  induction t
  · simp [StrictWeakOrder.Equiv]; intro _ _ hs hmax b; contradiction
  all_goals
    cases t_rchild <;> intro lo hi hs hmax b hmem
    · simp [Rbnode.max] at hmax ; subst t_val
      simp [mem] at hmem ; cases' hmem with hmem heqv
      · have := lt_of_mem_left hs (by constructor) hmem
        right; assumption
      · left; exact heqv.swap
    all_goals
      have hs' := hs
      cases hs; simp [Rbnode.max] at hmax 
      rw [mem] at hmem ; cases_type* or.1
      · have hmm := mem_of_max_eq lt hmax
        have a_lt_b := lt_of_mem_left_right hs' (by constructor) hmem hmm
        right; assumption
      · have hmm := mem_of_max_eq lt hmax
        have val_lt_a := lt_of_mem_right hs' (by constructor) hmm
        have a_lt_b := lt_of_incomp_of_lt hmem val_lt_a
        right; assumption
      · exact t_ih_rchild hs_hs₂ hmax hmem
#align rbnode.max_is_maximal Rbnode.max_is_maximal

end Rbnode

