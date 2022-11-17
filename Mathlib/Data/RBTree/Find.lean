/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.RBTee.Basic

/-!
# Basic thorems on ordering invariants

Ported with `sorry`s to preserve theorems
-/


universe u

namespace RBNode

variable {α : Type u}

@[elab_without_expected_type]
theorem find.induction {p : RBNode α → Prop} (lt) [DecidableRel lt] (t x) (h₁ : p leaf)
    (h₂ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.lt) (ih : p l), p (red_node l y r))
    (h₃ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.eq), p (red_node l y r))
    (h₄ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.gt) (ih : p r), p (red_node l y r))
    (h₅ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.lt) (ih : p l), p (black_node l y r))
    (h₆ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.eq), p (black_node l y r))
    (h₇ : ∀ (l y r) (h : CmpUsing lt x y = Ordering.gt) (ih : p r), p (black_node l y r)) : p t :=
    sorry

theorem find_correct {t : RBNode α} {lt x} [DecidableRel lt] [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (hs : IsSearchable lt t lo hi), Mem lt x t ↔ ∃ y, find lt t x = some y ∧ x ≈[lt]y :=
    sorry

theorem mem_of_mem_exact {lt} [IsIrrefl α lt] {x t} : MemExact x t → Mem lt x t := sorry

theorem find_correct_exact {t : RBNode α} {lt x} [DecidableRel lt] [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (hs : IsSearchable lt t lo hi), MemExact x t ↔ find lt t x = some x := sorry

theorem eqv_of_find_some {t : RBNode α} {lt x y} [DecidableRel lt] :
    ∀ {lo hi} (hs : IsSearchable lt t lo hi) (he : find lt t x = some y), x ≈[lt]y := sorry

theorem find_eq_find_of_eqv {lt a b} [DecidableRel lt] [IsStrictWeakOrder α lt] {t : RBNode α} :
    ∀ {lo hi} (hs : IsSearchable lt t lo hi) (heqv : a ≈[lt]b), find lt t a = find lt t b := sorry

end RBNode
