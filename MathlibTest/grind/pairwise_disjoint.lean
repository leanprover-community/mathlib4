import Mathlib

abbrev S1 : Fin 3 → Finset (Fin 4)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2, 3}

-- #adaptation_note 2025-10-27
-- This theorem was deprecated, but the replacement theorm has `Singleton` as an implicit argument,
-- and this seems to confuse `grind`.
theorem LawfulSingleton.insert_empty_eq' [EmptyCollection β] [Insert α β] [Singleton α β]
    [LawfulSingleton α β] (x : α) : (insert x ∅ : β) = singleton x :=
  insert_empty_eq _

attribute [grind _=_] LawfulSingleton.insert_empty_eq'

attribute [grind =] Finset.mem_singleton

attribute [grind =] Finset.disjoint_insert_left
attribute [grind =] Finset.disjoint_insert_right
attribute [grind ←] Finset.disjoint_empty_left
attribute [grind ←] Finset.disjoint_empty_right

attribute [grind] Pairwise

example : Pairwise (Function.onFun Disjoint fun x ↦ S1 x) := by
  grind
