/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.RBTree.Basic

/-!
# Theorems on invariants of `min`/`max`

Ported with `sorry` to preserve theorems
-/

universe u

namespace RBNode

variable {α : Type u} {lt : α → α → Prop}

theorem mem_of_min_eq (lt : α → α → Prop)
  [IsIrrefl α lt] {a : α} {t : RBNode α} : t.min = some a → Mem lt a t := sorry


theorem mem_of_max_eq
  (lt : α → α → Prop) [IsIrrefl α lt] {a : α} {t : RBNode α} : t.max = some a → Mem lt a t := sorry

variable [IsStrictWeakOrder α lt]

theorem eq_leaf_of_min_eq_none {t : RBNode α} : t.min = none → t = leaf := sorry

theorem eq_leaf_of_max_eq_none {t : RBNode α} : t.max = none → t = leaf := sorry

theorem min_is_minimal {a : α} {t : RBNode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → t.min = some a → ∀ {b}, Mem lt b t → a ≈[lt]b ∨ lt a b :=
    sorry

theorem max_is_maximal {a : α} {t : RBNode α} :
    ∀ {lo hi}, IsSearchable lt t lo hi → t.max = some a → ∀ {b}, Mem lt b t → a ≈[lt]b ∨ lt b a :=
    sorry

end RBNode
