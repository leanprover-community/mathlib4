
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.DeriveFintype

open Equiv

#guard with_decl_name% ex₁ unsafe (reprStr (1 : Perm (Fin 4))) == "1"
#guard with_decl_name% ex₂ unsafe (reprStr (c[0, 1] : Perm (Fin 4))) == "c[0, 1]"
#guard with_decl_name% ex₃
  unsafe (reprStr (c[0, 1] * c[2, 3] : Perm (Fin 4))) == "c[0, 1] * c[2, 3]"
#guard with_decl_name% ex₄
  unsafe (reprPrec (c[0, 1] * c[2, 3] : Perm (Fin 4)) 70).pretty == "(c[0, 1] * c[2, 3])"
#guard with_decl_name% ex₅
  unsafe (reprPrec (c[0, 1] * c[1, 2] : Perm (Fin 4)) 70).pretty == "c[0, 1, 2]"

example : (c[0, 1] * c[1, 2] : Perm (Fin 4)).cycleType = {3} := by decide
