/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.RBTree.Find

/-!
# Basic theorems on structural/well-foundeness after `insert`

Ported to preserve theorems, heavily covered by existing `Std` theorems
-/


universe u v

namespace RBNode

variable {α : Type u}

open Color

@[simp]
theorem balance1_eq₁ (l : RBNode α) (x r₁ y r₂ v t) :
    balance1 (red_node l x r₁) y r₂ v t = sorry

@[simp] theorem balance1_eq₂ (l₁ : RBNode α) (y l₂ x r v t) :
    getColor l₁ ≠ red → balance1 l₁ y (red_node l₂ x r) v t = sorry

@[simp] theorem balance1_eq₃ (l : RBNode α) (y r v t) :
    getColor l ≠ red → getColor r ≠ red → balance1 l y r v t =
      black_node (red_node l y r) v t := sorry

@[simp] theorem balance2_eq₁ (l : RBNode α) (x₁ r₁ y r₂ v t) :
    balance2 (red_node l x₁ r₁) y r₂ v t =
      red_node (black_node t v l) x₁ (black_node r₁ y r₂) := sorry

@[simp] theorem balance2_eq₂ (l₁ : RBNode α) (y l₂ x₂ r₂ v t) :
    getColor l₁ ≠ red → balance2 l₁ y (red_node l₂ x₂ r₂) v t =
      red_node (black_node t v l₁) y (black_node l₂ x₂ r₂) := sorry

@[simp] theorem balance2_eq₃ (l : RBNode α) (y r v t) :
    getColor l ≠ red → getColor r ≠ red → balance2 l y r v t =
      black_node t v (red_node l y r) := sorry

-- We can use the same induction principle for balance1 and balance2
theorem Balance.cases {p : RBNode α → α → RBNode α → Prop}
    (l y r) (red_left : ∀ l x r₁ y r₂, p (red_node l x r₁) y r₂)
    (red_right : ∀ l₁ y l₂ x r, getColor l₁ ≠ red → p l₁ y (red_node l₂ x r))
    (other : ∀ l y r, getColor l ≠ red → getColor r ≠ red → p l y r) : p l y r := sorry

theorem balance1_ne_leaf (l : RBNode α) (x r v t) : balance1 l x r v t ≠ leaf := sorry

theorem balance1_node_ne_leaf {s : RBNode α} (a : α) (t : RBNode α) :
    s ≠ leaf → balance1Node s a t ≠ leaf := sorry

theorem balance2_ne_leaf (l : RBNode α) (x r v t) : balance2 l x r v t ≠ leaf := sorry

theorem balance2_node_ne_leaf {s : RBNode α} (a : α) (t : RBNode α) :
    s ≠ leaf → balance2Node s a t ≠ leaf := sorry

variable (lt : α → α → Prop)

@[elab_as_elim]
theorem ins.induction [DecidableRel lt] {p : RBNode α → Prop} (t x) (is_leaf : p leaf)
    (is_red_lt : ∀ (a y b) (hc : CmpUsing lt x y = Ordering.lt) (ih : p a), p (red_node a y b))
    (is_red_eq : ∀ (a y b) (hc : CmpUsing lt x y = Ordering.eq), p (red_node a y b))
    (is_red_gt : ∀ (a y b) (hc : CmpUsing lt x y = Ordering.gt) (ih : p b), p (red_node a y b))
    (is_black_lt_red :
      ∀ (a y b)
        (hc : CmpUsing lt x y = Ordering.lt)
        (hr : getColor a = red) (ih : p a), p (black_node a y b))
    (is_black_lt_not_red :
      ∀ (a y b)
        (hc : CmpUsing lt x y = Ordering.lt)
        (hnr : getColor a ≠ red) (ih : p a), p (black_node a y b))
    (is_black_eq : ∀ (a y b) (hc : CmpUsing lt x y = Ordering.eq), p (black_node a y b))
    (is_black_gt_red :
      ∀ (a y b)
        (hc : CmpUsing lt x y = Ordering.gt)
        (hr : getColor b = red) (ih : p b), p (black_node a y b))
    (is_black_gt_not_red :
      ∀ (a y b)
        (hc : CmpUsing lt x y = Ordering.gt)
        (hnr : getColor b ≠ red) (ih : p b), p (black_node a y b)) :
    p t := sorry

theorem is_searchable_balance1 {l y r v t lo hi} :
    IsSearchable lt l lo (some y) →
      IsSearchable lt r (some y) (some v) →
        IsSearchable lt t (some v) hi → IsSearchable lt (balance1 l y r v t) lo hi := sorry

theorem is_searchable_balance1_node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      IsSearchable lt t lo (some y) →
        IsSearchable lt s (some y) hi →
          IsSearchable lt (balance1Node t y s) lo hi := sorry

theorem is_searchable_balance2 {l y r v t lo hi} :
    IsSearchable lt t lo (some v) →
      IsSearchable lt l (some v) (some y) →
        IsSearchable lt r (some y) hi → IsSearchable lt (balance2 l y r v t) lo hi := sorry

theorem is_searchable_balance2_node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      IsSearchable lt s lo (some y) →
        IsSearchable lt t (some y) hi →
          IsSearchable lt (balance2Node t y s) lo hi := sorry

theorem is_searchable_ins [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (h : IsSearchable lt t lo hi),
      Lift lt lo (some x) → Lift lt (some x) hi → IsSearchable lt (ins lt t x) lo hi := sorry

theorem is_searchable_mk_insert_result {c t} :
    IsSearchable lt t none none → IsSearchable lt (mkInsertResult c t) none none := sorry

end RBNode

namespace RBNode

section MembershipLemmas

parameter {α : Type u}(lt : α → α → Prop)

attribute [local simp] mem balance1_node balance2_node

-- mathport name: mem
local infixl:0 " ∈ " => Mem lt

theorem mem_balance1_node_of_mem_left {x s} (v) (t : RBNode α) :
    (x ∈ s) → (x ∈ balance1Node s v t) := sorry

theorem mem_balance2_node_of_mem_left {x s} (v) (t : RBNode α) :
    (x ∈ s) → (x ∈ balance2Node s v t) := sorry

theorem mem_balance1_node_of_mem_right {x t} (v) (s : RBNode α) :
    (x ∈ t) → (x ∈ balance1Node s v t) := sorry

theorem mem_balance2_node_of_mem_right {x t} (v) (s : RBNode α) :
    (x ∈ t) → (x ∈ balance2Node s v t) := sorry

theorem mem_balance1_node_of_incomp {x v} (s t) :
    ¬lt x v ∧ ¬lt v x → s ≠ leaf → (x ∈ balance1Node s v t) := sorry

theorem mem_balance2_node_of_incomp {x v} (s t) :
    ¬lt v x ∧ ¬lt x v → s ≠ leaf → (x ∈ balance2Node s v t) := sorry

theorem ins_ne_leaf [DecidableRel lt] (t : RBNode α) (x : α) : t.ins lt x ≠ leaf := sorry

theorem insert_ne_leaf [DecidableRel lt] (t : RBNode α) (x : α) : insert lt t x ≠ leaf := sorry

theorem mem_ins_of_incomp [DecidableRel lt] (t : RBNode α) {x y : α} : ∀ h :
    ¬lt x y ∧ ¬lt y x, x ∈ t.ins lt y := sorry

theorem mem_ins_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t : RBNode α} (z : α) :
    ∀ {x} (h : x ∈ t), x ∈ t.ins lt z := sorry


theorem mem_mk_insert_result {a t} (c) : Mem lt a t → Mem lt a (mkInsertResult c t) := sorry

theorem mem_of_mem_mk_insert_result {a t c} : Mem lt a (mkInsertResult c t) → Mem lt a t := sorry

theorem mem_insert_of_incomp [DecidableRel lt] (t : RBNode α) {x y : α} :
    ∀ h : ¬lt x y ∧ ¬lt y x, x ∈ t.insert lt y := sorry


theorem mem_insert_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t x} (z) :
    (x ∈ t) → (x ∈ t.insert lt z) := sorry

theorem of_mem_balance1_node {x s v t} :
    (x ∈ balance1Node s v t) → (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) := sorry

theorem of_mem_balance2_node {x s v t} : (x ∈ balance2Node s v t) →
    (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) := sorry

theorem equiv_or_mem_of_mem_ins [DecidableRel lt] {t : RBNode α} {x z} :
    ∀ h : x ∈ t.ins lt z, x ≈[lt]z ∨ (x ∈ t) := sorry

theorem equiv_or_mem_of_mem_insert [DecidableRel lt] {t : RBNode α} {x z} :
    ∀ h : x ∈ t.insert lt z, x ≈[lt]z ∨ (x ∈ t) := sorry

attribute [local simp] mem_exact

theorem mem_exact_balance1_node_of_mem_exact {x s} (v) (t : RBNode α) :
    MemExact x s → MemExact x (balance1Node s v t) := sorry

theorem mem_exact_balance2_node_of_mem_exact {x s} (v) (t : RBNode α) :
    MemExact x s → MemExact x (balance2Node s v t) := sorry


theorem find_balance1_node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z t s} :
    ∀ {lo hi},
      IsSearchable lt t lo (some z) →
        IsSearchable lt s (some z) hi →
          find lt t y = some x → y ≈[lt]x → find lt (balance1Node t z s) y = some x := sorry

theorem find_balance2_node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z s t} [IsTrans α lt] :
    ∀ {lo hi},
      IsSearchable lt s lo (some z) →
        IsSearchable lt t (some z) hi →
          find lt t y = some x → y ≈[lt]x → find lt (balance2Node t z s) y = some x := sorry

-- Auxiliary lemma
theorem ite_eq_of_not_lt
    [DecidableRel lt] [IsStrictOrder α lt] {a b} {β : Type v} (t s : β) (h : lt b a) :
      (if lt a b then t else s) = s := sorry

attribute [local simp] ite_eq_of_not_lt

theorem find_ins_of_eqv
    [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α} {t : RBNode α} (he : x ≈[lt]y) :
      ∀ {lo hi}
        (hs : IsSearchable lt t lo hi)
        (hlt₁ : Lift lt lo (some x))
        (hlt₂ :Lift lt (some x) hi), find lt (ins lt t x) y = some x := sorry

theorem find_mk_insert_result [DecidableRel lt] (c : Color) (t : RBNode α) (x : α) :
    find lt (mkInsertResult c t) x = find lt t x := sorry

theorem find_insert_of_eqv
    [DecidableRel lt]
    [IsStrictWeakOrder α lt]
    {x y : α}
    {t : RBNode α}
    (he : x ≈[lt]y) :
      IsSearchable lt t none none → find lt (insert lt t x) y = some x := sorry

theorem weak_trichotomous
    (x y)
    {p : Prop}
    (is_lt : ∀ h : lt x y, p)
    (is_eqv : ∀ h : ¬lt x y ∧ ¬lt y x, p)
    (is_gt : ∀ h : lt y x, p) : p := sorry

section FindInsOfNotEqv

section SimpAuxLemmas

theorem find_black_eq_find_red [DecidableRel lt] {l y r x} :
    find lt (black_node l y r) x = find lt (red_node l y r) x := sorry


theorem find_red_of_lt [DecidableRel lt] {l y r x} (h : lt x y) :
    find lt (red_node l y r) x = find lt l x := sorry

theorem find_red_of_gt [DecidableRel lt] [IsStrictOrder α lt] {l y r x} (h : lt y x) :
    find lt (red_node l y r) x = find lt r x := sorry

theorem find_red_of_incomp [DecidableRel lt] {l y r x} (h : ¬lt x y ∧ ¬lt y x) :
    find lt (red_node l y r) x = some y := sorry

end SimpAuxLemmas

-- attribute [local simp] find_black_eq_find_red find_red_of_lt
--find_red_of_lt find_red_of_gt find_red_of_incomp

variable [IsStrictWeakOrder α lt] [DecidableRel lt]

theorem find_balance1_lt {l r t v x y lo hi} (h : lt x y) (hl : IsSearchable lt l lo (some v))
    (hr : IsSearchable lt r (some v) (some y)) (ht : IsSearchable lt t (some y) hi) :
    find lt (balance1 l v r y t) x = find lt (red_node l v r) x := sorry

theorem find_balance1_node_lt {t s x y lo hi} (hlt : lt y x) (ht : IsSearchable lt t lo (some x))
    (hs : IsSearchable lt s (some x) hi)
    (hne : t ≠ leaf := sorry

theorem find_balance1_gt {l r t v x y lo hi} (h : lt y x) (hl : IsSearchable lt l lo (some v))
    (hr : IsSearchable lt r (some v) (some y)) (ht : IsSearchable lt t (some y) hi) :
    find lt (balance1 l v r y t) x = find lt t x := sorry

theorem find_balance1_node_gt {t s x y lo hi} (h : lt x y) (ht : IsSearchable lt t lo (some x))
    (hs : IsSearchable lt s (some x) hi)
    (hne : t ≠ leaf := sorry

theorem find_balance1_eqv
    {l r t v x y lo hi}
    (h : ¬lt x y ∧ ¬lt y x)
    (hl : IsSearchable lt l lo (some v))
    (hr : IsSearchable lt r (some v) (some y))
    (ht : IsSearchable lt t (some y) hi) :
      find lt (balance1 l v r y t) x = some y := sorry

theorem find_balance1_node_eqv
    {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (ht : IsSearchable lt t lo (some y))
    (hs : IsSearchable lt s (some y) hi)
    (hne : t ≠ leaf) :
      find lt (balance1Node t y s) x = some y := sorry


theorem find_balance2_node_lt {s t x y lo hi} (h : lt x y) (ht : IsSearchable lt t (some y) hi)
    (hs : IsSearchable lt s lo (some y))
    (hne : t ≠ leaf := sorry

theorem find_balance2_gt {l v r t x y lo hi} (h : lt y x) (hl : IsSearchable lt l (some y) (some v))
    (hr : IsSearchable lt r (some v) hi) (ht : IsSearchable lt t lo (some y)) :
    find lt (balance2 l v r y t) x = find lt (red_node l v r) x := sorry

theorem find_balance2_node_gt {s t x y lo hi} (h : lt y x) (ht : IsSearchable lt t (some y) hi)
    (hs : IsSearchable lt s lo (some y))
    (hne : t ≠ leaf := sorry

theorem find_balance2_eqv
    {l v r t x y lo hi}
    (h : ¬lt x y ∧ ¬lt y x)
    (hl : IsSearchable lt l (some y) (some v))
    (hr : IsSearchable lt r (some v) hi)
    (ht : IsSearchable lt t lo (some y)) :
      find lt (balance2 l v r y t) x = some y := sorry

theorem find_balance2_node_eqv
    {t s x y lo hi}
    (h : ¬lt x y ∧ ¬lt y x)
    (ht : IsSearchable lt t (some y) hi)
    (hs : IsSearchable lt s lo (some y))
    (hne : t ≠ leaf) : find lt (balance2Node t y s) x = some y := sorry

theorem find_ins_of_disj
    {x y : α}
    {t : RBNode α}
    (hn : lt x y ∨ lt y x) :
      ∀ {lo hi}
        (hs : IsSearchable lt t lo hi)
        (hlt₁ : Lift lt lo (some x))
        (hlt₂ : Lift lt (some x) hi), find lt (ins lt t x) y = find lt t y := sorry

end FindInsOfNotEqv

theorem find_insert_of_disj
    [DecidableRel lt]
    [IsStrictWeakOrder α lt]
    {x y : α}
    {t : RBNode α}
    (hd : lt x y ∨ lt y x) :
      IsSearchable lt t none none → find lt (insert lt t x) y = find lt t y := sorry

theorem find_insert_of_not_eqv
    [DecidableRel lt]
    [IsStrictWeakOrder α lt]
    {x y : α}
    {t : RBNode α}
    (hn : ¬x ≈[lt]y) :
      IsSearchable lt t none none → find lt (insert lt t x) y = find lt t y := sorry

end MembershipLemmas

section IsRedBlack

variable {α : Type u}

open Nat Color

inductive IsBadRedBlack : RBNode α → Nat → Prop := sorry

theorem balance1_rb {l r t : RBNode α} {y v : α} {c_l c_r c_t n} :
    IsRedBlack l c_l n → IsRedBlack r c_r n →
      IsRedBlack t c_t n →
        ∃ c, IsRedBlack (balance1 l y r v t) c (succ n) := sorry

theorem balance2_rb {l r t : RBNode α} {y v : α} {c_l c_r c_t n} :
    IsRedBlack l c_l n →
      IsRedBlack r c_r n →
        IsRedBlack t c_t n →
          ∃ c, IsRedBlack (balance2 l y r v t) c (succ n) := sorry

theorem balance1_node_rb {t s : RBNode α} {y : α} {c n} :
    IsBadRedBlack t n → IsRedBlack s c n → ∃ c, IsRedBlack (balance1Node t y s) c (succ n) := sorry

theorem balance2_node_rb {t s : RBNode α} {y : α} {c n} :
    IsBadRedBlack t n → IsRedBlack s c n → ∃ c, IsRedBlack (balance2Node t y s) c (succ n) := sorry

def InsRbResult : RBNode α → Color → Nat → Prop := sorry

variable {lt : α → α → Prop} [DecidableRel lt]

theorem of_get_color_eq_red
    {t : RBNode α} {c n} : getColor t = red → IsRedBlack t c n → c = red := sorry

theorem of_get_color_ne_red
    {t : RBNode α} {c n} : getColor t ≠ red → IsRedBlack t c n → c = black := sorry

variable (lt)

theorem ins_rb
    {t : RBNode α} (x) : ∀ {c n} (h : IsRedBlack t c n), InsRbResult (ins lt t x) c n := sorry

def InsertRbResult : RBNode α → Color → Nat → Prop := sorry

theorem insert_rb
    {t : RBNode α} (x) {c n} (h : IsRedBlack t c n) : InsertRbResult (insert lt t x) c n := sorry

theorem insert_is_red_black
    {t : RBNode α} {c n} (x) : IsRedBlack t c n → ∃ c n, IsRedBlack (insert lt t x) c n := sorry

end IsRedBlack

end RBNode
