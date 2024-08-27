import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.DFinsupp.Notation -- to ensure it does not interfere
import Mathlib.Data.Nat.Factorization.Basic

example : (fun₀ | 1 => 3) 1 = 3 := by
  simp

example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 1 = 3 := by
  simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 2 = 3 := by
  simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 3 = 4 := by
  simp

/--
info:
-/
#guard_msgs in
#eval show Lean.MetaM Unit from
  guard <|
    reprStr (Finsupp.mk {1, 2} (fun | 1 | 2 => 3 | _ => 0) (fun x => by aesop))
      = "fun₀ | 1 => 3 | 2 => 3"

/-! ## (computable) number theory examples-/

/-- info: fun₀ | 2 => 2 | 7 => 1 -/
#guard_msgs in
#eval Nat.factorization 28

/-- info: fun₀ | 3 => 2 | 5 => 1 -/
#guard_msgs in
#eval (Nat.factorization 720).filter Odd
