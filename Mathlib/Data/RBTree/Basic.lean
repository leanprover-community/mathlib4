/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.RBTree.Init

/-!
# Basic thorems on search invariants

Ported with `sorry`s to preserve theorems
-/

universe u

namespace RRNode

variable {α : Type u}

inductive IsNodeOf : RBNode α → RBNode α → α → RBNode α → Prop := sorry

def Lift (lt : α → α → Prop) : Option α → Option α → Prop := sorry

inductive IsSearchable (lt : α → α → Prop) : RBNode α → Option α → Option α → Prop := sorry


open RBNode (Mem)

open IsSearchable

section IsSearchableLemmas

variable {lt : α → α → Prop}

theorem lo_lt_hi {t : RBNode α} {lt} [IsTrans α lt] :
    ∀ {lo hi}, IsSearchable lt t lo hi → Lift lt lo hi := sorry

theorem is_searchable_of_is_searchable_of_incomp [IsStrictWeakOrder α lt] {t} :
    ∀ {lo hi hi'} (hc : ¬lt hi' hi ∧ ¬lt hi hi') (hs : IsSearchable lt t lo (some hi)),
      IsSearchable lt t lo (some hi') := sorry

theorem is_searchable_of_incomp_of_is_searchable [IsStrictWeakOrder α lt] {t} :
    ∀ {lo lo' hi} (hc : ¬lt lo' lo ∧ ¬lt lo lo') (hs : IsSearchable lt t (some lo) hi),
      IsSearchable lt t (some lo') hi := sorry

theorem is_searchable_some_low_of_is_searchable_of_lt {t} [IsTrans α lt] :
    ∀ {lo hi lo'}
      (hlt : lt lo' lo)
      (hs : IsSearchable lt t (some lo) hi), IsSearchable lt t (some lo') hi := sorry

theorem is_searchable_none_low_of_is_searchable_some_low {t} :
    ∀ {y hi} (hlt : IsSearchable lt t (some y) hi), IsSearchable lt t none hi := sorry

theorem is_searchable_some_high_of_is_searchable_of_lt {t} [IsTrans α lt] :
    ∀ {lo hi hi'}
      (hlt : lt hi hi')
      (hs : IsSearchable lt t lo (some hi)), IsSearchable lt t lo (some hi') := sorry

theorem is_searchable_none_high_of_is_searchable_some_high {t} :
    ∀ {lo y} (hlt : IsSearchable lt t lo (some y)), IsSearchable lt t lo none := sorry

theorem range [IsStrictWeakOrder α lt] {t : RBNode α} {x} :
    ∀ {lo hi}, IsSearchable lt t lo hi →
      Mem lt x t → Lift lt lo (some x) ∧ Lift lt (some x) hi := sorry

theorem lt_of_mem_left [IsStrictWeakOrder α lt] {y : α} {t l r : RBNode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → IsNodeOf t l y r → ∀ {x}, Mem lt x l → lt x y := sorry

theorem lt_of_mem_right [IsStrictWeakOrder α lt] {y : α} {t l r : RBNode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → IsNodeOf t l y r → ∀ {z}, Mem lt z r → lt y z := sorry

theorem lt_of_mem_left_right [IsStrictWeakOrder α lt] {y : α} {t l r : RBNode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi →
      IsNodeOf t l y r → ∀ {x z}, Mem lt x l → Mem lt z r → lt x z := sorry

end IsSearchableLemmas

inductive IsRedBlack : RBNode α → Color → Nat → Prop := sorry

open IsRedBlack

theorem depth_min : ∀ {c n} {t : RBNode α}, IsRedBlack t c n → n ≤ depth min t := sorry

theorem depth_max' : ∀ {c n} {t : RBNode α}, IsRedBlack t c n → depth max t ≤ upper c n := sorry

theorem depth_max {c n} {t : RBNode α} (h : IsRedBlack t c n) : depth max t ≤ 2 * n + 1 := sorry

theorem balanced {c n} {t : RBNode α} (h : IsRedBlack t c n) :
    depth max t ≤ 2 * depth min t + 1 := sorry

end RBNode
