import Mathlib.Data.DFinsupp.Notation

example : (fun₀ | 1 => 3 : Π₀ i, Fin (i + 10)) 1 = 3 := by
  simp

example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 1 = 3 := by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 2 = 3 := by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4 : Π₀ i, Fin (i + 10)) 3 = 4 := by simp

/--
info:
-/
#guard_msgs in
#eval show Lean.MetaM Unit from
  guard <|
    reprStr (fun₀ | 1 => 3 | 2 => 3 : Π₀ i, Fin (i + 10))
      = "fun₀ | 1 => 3 | 2 => 3"

/--
info:
-/
#guard_msgs in
#eval show Lean.MetaM Unit from
  guard <|
    reprStr ((fun₀ | 1 => 3 | 2 => 3) + (fun₀ | 1 => -3 | 2 => 4) : Π₀ _, ℤ)
      = "fun₀ | 2 => 7"
