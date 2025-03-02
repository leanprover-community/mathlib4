import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.DFinsupp.Notation

example : (fun₀ | 1 => 3 : Π₀ i, Fin (i + 10)) 1 = 3 := by
  simp

example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 1 = 3 := by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 2 = 3 := by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 3 = 4 := by simp

section Repr

/-- info: fun₀ | 1 => 3 | 2 => 3 : Π₀ (i : ℕ), Fin (i + 10) -/
#guard_msgs in
#check (fun₀ | 1 => 3 | 2 => 3 : Π₀ i, Fin (i + 10))

/-- info: fun₀ | 2 => 7 -/
#guard_msgs in
#eval ((fun₀ | 1 => 3 | 2 => 3) + (fun₀ | 1 => -3 | 2 => 4) : Π₀ _, ℤ)

/--
info: fun₀
  | ["there are five words here", "and five more words here"] => 5
  | ["there are seven words but only here"] => 7
  | ["just two"] => 2
-/
#guard_msgs in
#eval (fun₀
    | ["there are five words here", "and five more words here"] => 5
    | ["there are seven words but only here"] => 7
    | ["just two"] => 2 : Π₀ _ : List String, ℕ)

end Repr

section PrettyPrinter

/--
info: fun₀
  | ["there are five words here", "and five more words here"] => 5
  | ["there are seven words but only here"] => 7
  | ["just two"] => 2 : Π₀ (i : List String), ℕ
-/
#guard_msgs in
#check (fun₀
    | ["there are five words here", "and five more words here"] => 5
    | ["there are seven words but only here"] => 7
    | ["just two"] => 2 : Π₀ _ : List String, ℕ)

end PrettyPrinter
