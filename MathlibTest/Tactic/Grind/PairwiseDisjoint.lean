import Mathlib

abbrev S1 : Fin 3 → Finset (Fin 4)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2, 3}

attribute [grind _=_] LawfulSingleton.insert_empty_eq

attribute [grind] Pairwise

example : Pairwise (Function.onFun Disjoint fun x ↦ S1 x) := by
  grind
