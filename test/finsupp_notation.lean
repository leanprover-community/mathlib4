import Mathlib.Data.Finsupp.Notation

example : (fun₀ | 1 => 3) 1 = 3 :=
by simp

example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 1 = 3 :=
by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 2 = 3 :=
by simp
example : (fun₀ | 1 | 2 | 3 => 3 | 3 => 4) 3 = 4 :=
by simp

/--
info:
-/
#guard_msgs in
#eval show Lean.MetaM Unit from
  guard <|
    reprStr (Finsupp.mk {1, 2} (fun | 1 | 2 => 3 | _ => 0) (fun x => by aesop))
      = "fun₀ | 1 => 3 | 2 => 3"
