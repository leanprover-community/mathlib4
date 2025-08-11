import Mathlib

abbrev S1 : Fin 3 → Finset (Fin 4)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2, 3}

attribute [grind _=_] LawfulSingleton.insert_emptyc_eq

attribute [grind =] Finset.mem_singleton

attribute [grind =] Finset.disjoint_insert_left
attribute [grind =] Finset.disjoint_insert_right
attribute [grind] Finset.disjoint_empty_left
attribute [grind] Finset.disjoint_empty_right

attribute [grind] Pairwise

#adaptation_note
/-- As of nightly-2025-08-11, this stopped working.
Reported in https://github.com/leanprover/lean4/pull/9830 -/
-- example : Pairwise (Function.onFun Disjoint fun x ↦ S1 x) := by
--   grind
