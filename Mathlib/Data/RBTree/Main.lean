/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.RBTree.Find
import Mathlib.Data.RBTree.Insert
import Mathlib.Data.RBTree.MinMax
import Mathlib.Order.RelClasses

/-!
# Basic theorems on API behavior given structural/well-foundeness

Ported to preserve theorems
-/


universe u

namespace RBNode

variable {α : Type u} {lt : α → α → Prop}

theorem is_searchable_of_well_formed {t : RBNode α} [IsStrictWeakOrder α lt] :
    t.WellFormed lt → IsSearchable lt t none none := sorry
open Color

theorem is_red_black_of_well_formed {t : RBNode α} : t.WellFormed lt → ∃ c n, IsRedBlack t c n :=
    sorry

end RBNode

namespace RBTree

variable {α : Type u} {lt : α → α → Prop}

theorem balanced (t : RBTree α lt) : t.depth max ≤ 2 * t.depth min + 1 := sorry

theorem not_mem_mk_rbtree : ∀ a : α, a ∉ mkRBTree α lt := sorry

theorem not_mem_of_empty {t : RBTree α lt} (a : α) : t.Empty = tt → a ∉ t := sorry

theorem mem_of_mem_of_eqv
    [IsStrictWeakOrder α lt]
    {t : RBTree α lt}
    {a b : α} : a ∈ t → a ≈[lt]b → b ∈ t := sorry

section Dec

variable [DecidableRel lt]

theorem insert_ne_mk_rbtree (t : RBTree α lt) (a : α) : t.insert a ≠ mkRBTree α lt := sorry

theorem find_correct
    [IsStrictWeakOrder α lt]
    (a : α)
    (t : RBTree α lt) : a ∈ t ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b := sorry

theorem find_correct_of_total
    [IsStrictTotalOrder α lt]
    (a : α)
    (t : RBTree α lt) : a ∈ t ↔ t.find a = some a := sorry

theorem find_correct_exact
    [IsStrictTotalOrder α lt]
    (a : α)
    (t : RBTree α lt) : MemExact a t ↔ t.find a = some a := sorry

theorem find_insert_of_eqv
    [IsStrictWeakOrder α lt]
    (t : RBTree α lt)
    {x y} : x ≈[lt]y → (t.insert x).find y = some x := sorry

theorem find_insert
    [IsStrictWeakOrder α lt]
    (t : RBTree α lt) (x) : (t.insert x).find x = some x := sorry

theorem find_insert_of_disj [IsStrictWeakOrder α lt] {x y : α} (t : RBTree α lt) :
    lt x y ∨ lt y x → (t.insert x).find y = t.find y := sorry

theorem find_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α} (t : RBTree α lt) :
    ¬x ≈[lt]y → (t.insert x).find y = t.find y := sorry

theorem find_insert_of_ne [IsStrictTotalOrder α lt] {x y : α} (t : RBTree α lt) :
    x ≠ y → (t.insert x).find y = t.find y := sorry

theorem not_mem_of_find_none
    [IsStrictWeakOrder α lt] {a : α} {t : RBTree α lt} : t.find a = none → a ∉ t := sorry

theorem eqv_of_find_some
    [IsStrictWeakOrder α lt] {a b : α} {t : RBTree α lt} : t.find a = some b → a ≈[lt]b := sorry

theorem eq_of_find_some
    [IsStrictTotalOrder α lt] {a b : α} {t : RBTree α lt} : t.find a = some b → a = b := sorry

theorem mem_of_find_some
    [IsStrictWeakOrder α lt] {a b : α} {t : RBTree α lt} : t.find a = some b → a ∈ t := sorry

theorem find_eq_find_of_eqv
    [IsStrictWeakOrder α lt] {a b : α} (t : RBTree α lt) : a ≈[lt]b → t.find a = t.find b := sorry

theorem contains_correct
    [IsStrictWeakOrder α lt] (a : α) (t : RBTree α lt) : a ∈ t ↔ t.contains a = tt := sorry

theorem mem_insert_of_incomp
    {a b : α} (t : RBTree α lt) : ¬lt a b ∧ ¬lt b a → a ∈ t.insert b := sorry

theorem mem_insert [IsIrrefl α lt] : ∀ (a : α) (t : RBTree α lt), a ∈ t.insert a := sorry

theorem mem_insert_of_equiv {a b : α} (t : RBTree α lt) : a ≈[lt]b → a ∈ t.insert b := sorry

theorem mem_insert_of_mem
    [IsStrictWeakOrder α lt] {a : α} {t : RBTree α lt} (b : α) : a ∈ t → a ∈ t.insert b := sorry

theorem equiv_or_mem_of_mem_insert
    {a b : α} {t : RBTree α lt} : a ∈ t.insert b → a ≈[lt]b ∨ a ∈ t := sorry

theorem incomp_or_mem_of_mem_ins
    {a b : α} {t : RBTree α lt} : a ∈ t.insert b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t := sorry

theorem eq_or_mem_of_mem_ins
    [IsStrictTotalOrder α lt] {a b : α} {t : RBTree α lt} : a ∈ t.insert b → a = b ∨ a ∈ t := sorry

end Dec

theorem mem_of_min_eq [IsIrrefl α lt] {a : α} {t : RBTree α lt} : t.min = some a → a ∈ t := sorry

theorem mem_of_max_eq [IsIrrefl α lt] {a : α} {t : RBTree α lt} : t.max = some a → a ∈ t := sorry

theorem eq_leaf_of_min_eq_none {t : RBTree α lt} : t.min = none → t = mkRBTree α lt := sorry

theorem eq_leaf_of_max_eq_none {t : RBTree α lt} : t.max = none → t = mkRBTree α lt := sorry

theorem min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : RBTree α lt} :
    t.min = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt a b := sorry

theorem max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : RBTree α lt} :
    t.max = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt b a := sorry

end RBTree
