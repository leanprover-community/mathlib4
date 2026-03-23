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

section repr

/-- info: fun₀ | 1 => 3 | 2 => 3 -/
#guard_msgs in
#eval (Finsupp.mk {1, 2} (fun | 1 | 2 => 3 | _ => 0) (fun x => by aesop))

/--
info: fun₀
  | ["there are five words here", "and five more words here"] => 5
  | ["there are seven words but only here"] => 7
  | ["just two"] => 2
-/
#guard_msgs in
#eval Finsupp.mk
  {["there are five words here", "and five more words here"],
   ["there are seven words but only here"],
   ["just two"]}
  (fun
    | ["there are five words here", "and five more words here"] => 5
    | ["there are seven words but only here"] => 7
    | ["just two"] => 2
    | _ => 0)
  (fun x => by aesop)

end repr

section PrettyPrinter

/--
info: fun₀
  | ["there are five words here", "and five more words here"] => 5
  | ["there are seven words but only here"] => 7
  | ["just two"] => 2 : List String →₀ ℕ
-/
#guard_msgs in
#check fun₀
    | ["there are five words here", "and five more words here"] => 5
    | ["there are seven words but only here"] => 7
    | ["just two"] => 2

end PrettyPrinter


/-! ## (computable) number theory examples -/

/-- info: fun₀ | 2 => 2 | 7 => 1 -/
#guard_msgs in
#eval Nat.factorization 28

/-- info: fun₀ | 3 => 2 | 5 => 1 -/
#guard_msgs in
#eval (Nat.factorization 720).filter Odd
