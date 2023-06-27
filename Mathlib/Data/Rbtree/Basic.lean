/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.basic
! leanprover-community/mathlib commit 5cb17dd1617d2dc55eb17777c3dcded3306fadb5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rbtree.Init
import Mathlib.Logic.IsEmpty
import Mathlib.Tactic.Interactive

universe u

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def tactic.interactive.blast_disjs : tactic Unit :=
  sorry
#align tactic.interactive.blast_disjs tactic.interactive.blast_disjs

namespace Rbnode

variable {α : Type u}

open Color Nat

inductive IsNodeOf : Rbnode α → Rbnode α → α → Rbnode α → Prop
  | of_red (l v r) : is_node_of (red_node l v r) l v r
  | of_black (l v r) : is_node_of (black_node l v r) l v r
#align rbnode.is_node_of Rbnode.IsNodeOf

def Lift (lt : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => lt a b
  | _, _ => True
#align rbnode.lift Rbnode.Lift

inductive IsSearchable (lt : α → α → Prop) : Rbnode α → Option α → Option α → Prop
  | leaf_s {lo hi} (hlt : Lift lt lo hi) : is_searchable leaf lo hi
  |
  red_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
    is_searchable (red_node l v r) lo hi
  |
  black_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
    is_searchable (black_node l v r) lo hi
#align rbnode.is_searchable Rbnode.IsSearchable

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def is_searchable_tactic : tactic Unit :=
  sorry
#align rbnode.is_searchable_tactic rbnode.is_searchable_tactic

open Rbnode (Mem)

open IsSearchable

section IsSearchableLemmas

variable {lt : α → α → Prop}

theorem lo_lt_hi {t : Rbnode α} {lt} [IsTrans α lt] :
    ∀ {lo hi}, IsSearchable lt t lo hi → Lift lt lo hi := by
  induction t <;> intro lo hi hs
  case leaf => cases hs; assumption
  all_goals
    cases hs
    have h₁ := t_ih_lchild hs_hs₁
    have h₂ := t_ih_rchild hs_hs₂
    cases lo <;> cases hi <;> simp [lift] at *
    apply trans_of lt h₁ h₂
#align rbnode.lo_lt_hi Rbnode.lo_lt_hi

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_of_isSearchable_of_incomp [IsStrictWeakOrder α lt] {t} :
    ∀ {lo hi hi'} (hc : ¬lt hi' hi ∧ ¬lt hi hi') (hs : IsSearchable lt t lo (some hi)),
      IsSearchable lt t lo (some hi') := by
  classical
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp_all [lift]; apply lt_of_lt_of_incomp; assumption; exact ⟨hc.2, hc.1⟩
  all_goals apply t_ih_rchild hc hs_hs₂
#align rbnode.is_searchable_of_is_searchable_of_incomp Rbnode.isSearchable_of_isSearchable_of_incomp

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_of_incomp_of_isSearchable [IsStrictWeakOrder α lt] {t} :
    ∀ {lo lo' hi} (hc : ¬lt lo' lo ∧ ¬lt lo lo') (hs : IsSearchable lt t (some lo) hi),
      IsSearchable lt t (some lo') hi := by
  classical
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi <;> simp_all [lift]; apply lt_of_incomp_of_lt; assumption; assumption
  all_goals apply t_ih_lchild hc hs_hs₁
#align rbnode.is_searchable_of_incomp_of_is_searchable Rbnode.isSearchable_of_incomp_of_isSearchable

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_some_low_of_isSearchable_of_lt {t} [IsTrans α lt] :
    ∀ {lo hi lo'} (hlt : lt lo' lo) (hs : IsSearchable lt t (some lo) hi),
      IsSearchable lt t (some lo') hi := by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi <;> simp_all [lift]; apply trans_of lt hlt; assumption
  all_goals apply t_ih_lchild hlt hs_hs₁
#align rbnode.is_searchable_some_low_of_is_searchable_of_lt Rbnode.isSearchable_some_low_of_isSearchable_of_lt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_none_low_of_isSearchable_some_low {t} :
    ∀ {y hi} (hlt : IsSearchable lt t (some y) hi), IsSearchable lt t none hi := by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · simp [lift]
  all_goals apply t_ih_lchild hlt_hs₁
#align rbnode.is_searchable_none_low_of_is_searchable_some_low Rbnode.isSearchable_none_low_of_isSearchable_some_low

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_some_high_of_isSearchable_of_lt {t} [IsTrans α lt] :
    ∀ {lo hi hi'} (hlt : lt hi hi') (hs : IsSearchable lt t lo (some hi)),
      IsSearchable lt t lo (some hi') := by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp_all [lift]; apply trans_of lt; assumption; assumption
  all_goals apply t_ih_rchild hlt hs_hs₂
#align rbnode.is_searchable_some_high_of_is_searchable_of_lt Rbnode.isSearchable_some_high_of_isSearchable_of_lt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem isSearchable_none_high_of_isSearchable_some_high {t} :
    ∀ {lo y} (hlt : IsSearchable lt t lo (some y)), IsSearchable lt t lo none := by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp [lift]
  all_goals apply t_ih_rchild hlt_hs₂
#align rbnode.is_searchable_none_high_of_is_searchable_some_high Rbnode.isSearchable_none_high_of_isSearchable_some_high

theorem range [IsStrictWeakOrder α lt] {t : Rbnode α} {x} :
    ∀ {lo hi}, IsSearchable lt t lo hi → Mem lt x t → Lift lt lo (some x) ∧ Lift lt (some x) hi :=
  by
  classical
  induction t
  case leaf => simp [mem]
  all_goals
    -- red_node and black_node are identical
    intro lo hi h₁ h₂;
    cases h₁
    simp only [mem] at h₂ 
    have val_hi : lift lt (some t_val) hi := by apply lo_lt_hi; assumption
    have lo_val : lift lt lo (some t_val) := by apply lo_lt_hi; assumption
    cases_type* or.1
    · have h₃ : lift lt lo (some x) ∧ lift lt (some x) (some t_val) := by apply t_ih_lchild;
        assumption; assumption
      cases' h₃ with lo_x x_val
      constructor
      show lift lt lo (some x); · assumption
      show lift lt (some x) hi
      · cases' hi with hi <;> simp [lift] at *
        apply trans_of lt x_val val_hi
    · cases h₂
      cases' lo with lo <;> cases' hi with hi <;> simp [lift] at *
      · apply lt_of_incomp_of_lt _ val_hi; simp [*]
      · apply lt_of_lt_of_incomp lo_val; simp [*]
      constructor
      · apply lt_of_lt_of_incomp lo_val; simp [*]
      · apply lt_of_incomp_of_lt _ val_hi; simp [*]
    · have h₃ : lift lt (some t_val) (some x) ∧ lift lt (some x) hi := by apply t_ih_rchild;
        assumption; assumption
      cases' h₃ with val_x x_hi
      cases' lo with lo <;> cases' hi with hi <;> simp [lift] at *
      · assumption
      · apply trans_of lt lo_val val_x
      constructor
      · apply trans_of lt lo_val val_x
      · assumption
#align rbnode.range Rbnode.range

theorem lt_of_mem_left [IsStrictWeakOrder α lt] {y : α} {t l r : Rbnode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → IsNodeOf t l y r → ∀ {x}, Mem lt x l → lt x y := by
  intro _ _ hs hn x hm; cases hn <;> cases hs
  all_goals exact (range hs_hs₁ hm).2
#align rbnode.lt_of_mem_left Rbnode.lt_of_mem_left

theorem lt_of_mem_right [IsStrictWeakOrder α lt] {y : α} {t l r : Rbnode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → IsNodeOf t l y r → ∀ {z}, Mem lt z r → lt y z := by
  intro _ _ hs hn z hm; cases hn <;> cases hs
  all_goals exact (range hs_hs₂ hm).1
#align rbnode.lt_of_mem_right Rbnode.lt_of_mem_right

theorem lt_of_mem_left_right [IsStrictWeakOrder α lt] {y : α} {t l r : Rbnode α} :
    ∀ {lo hi},
      IsSearchable lt t lo hi → IsNodeOf t l y r → ∀ {x z}, Mem lt x l → Mem lt z r → lt x z := by
  intro _ _ hs hn x z hm₁ hm₂; cases hn <;> cases hs
  all_goals
    have h₁ := range hs_hs₁ hm₁
    have h₂ := range hs_hs₂ hm₂
    exact trans_of lt h₁.2 h₂.1
#align rbnode.lt_of_mem_left_right Rbnode.lt_of_mem_left_right

end IsSearchableLemmas

inductive IsRedBlack : Rbnode α → Color → Nat → Prop
  | leaf_rb : is_red_black leaf black 0
  |
  red_rb {v l r n} (rb_l : is_red_black l black n) (rb_r : is_red_black r black n) :
    is_red_black (red_node l v r) red n
  |
  black_rb {v l r n c₁ c₂} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) :
    is_red_black (black_node l v r) black (succ n)
#align rbnode.is_red_black Rbnode.IsRedBlack

open IsRedBlack

theorem depth_min : ∀ {c n} {t : Rbnode α}, IsRedBlack t c n → n ≤ depth min t := by
  intro c n' t h
  induction h
  case leaf_rb => exact le_refl _
  case red_rb =>
    simp [depth]
    have : min (depth min h_l) (depth min h_r) ≥ h_n := by apply le_min <;> assumption
    apply le_succ_of_le; assumption
  case black_rb =>
    simp [depth]
    apply succ_le_succ
    apply le_min <;> assumption
#align rbnode.depth_min Rbnode.depth_min

private def upper : Color → Nat → Nat
  | red, n => 2 * n + 1
  | black, n => 2 * n

private theorem upper_le : ∀ c n, upper c n ≤ 2 * n + 1
  | red, n => le_refl _
  | black, n => by apply le_succ

theorem depth_max' : ∀ {c n} {t : Rbnode α}, IsRedBlack t c n → depth max t ≤ upper c n := by
  intro c n' t h
  induction h
  case leaf_rb => simp [max, depth, upper, Nat.mul_zero]
  case
    red_rb =>
    suffices succ (max (depth max h_l) (depth max h_r)) ≤ 2 * h_n + 1 by simp_all [depth, upper]
    apply succ_le_succ
    apply max_le <;> assumption
  case
    black_rb =>
    have : depth max h_l ≤ 2 * h_n + 1 := le_trans h_ih_rb_l (upper_le _ _)
    have : depth max h_r ≤ 2 * h_n + 1 := le_trans h_ih_rb_r (upper_le _ _)
    suffices new : max (depth max h_l) (depth max h_r) + 1 ≤ 2 * h_n + 2 * 1
    · simp_all [depth, upper, succ_eq_add_one, Nat.left_distrib]
    apply succ_le_succ; apply max_le <;> assumption
#align rbnode.depth_max' Rbnode.depth_max'

theorem depth_max {c n} {t : Rbnode α} (h : IsRedBlack t c n) : depth max t ≤ 2 * n + 1 :=
  le_trans (depth_max' h) (upper_le _ _)
#align rbnode.depth_max Rbnode.depth_max

theorem balanced {c n} {t : Rbnode α} (h : IsRedBlack t c n) : depth max t ≤ 2 * depth min t + 1 :=
  by
  have : 2 * depth min t + 1 ≥ 2 * n + 1 := by apply succ_le_succ; apply Nat.mul_le_mul_left;
    apply depth_min h
  apply le_trans; apply depth_max h; apply this
#align rbnode.balanced Rbnode.balanced

end Rbnode

