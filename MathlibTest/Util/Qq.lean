import Mathlib.Util.Qq
import Mathlib.Data.Finset.Basic


open Qq Lean Elab Meta

section mkSetLiteralQ

/--
info: {1, 2, 3} : Finset ℕ
-/
#guard_msgs in
#check by_elab return mkSetLiteralQ q(Finset ℕ) [q(1), q(2), q(3)]

/--
info: {1, 2, 3} : Multiset ℕ
-/
#guard_msgs in
#check by_elab return mkSetLiteralQ q(Multiset ℕ) [q(1), q(2), q(3)]

/--
info: {1, 2, 3} : Set ℕ
-/
#guard_msgs in
#check by_elab return mkSetLiteralQ q(Set ℕ) [q(1), q(2), q(3)]

/--
info: {1, 2, 3} : List ℕ
-/
#guard_msgs in
#check by_elab return mkSetLiteralQ q(List ℕ) [q(1), q(2), q(3)]


/-- info: {0 • -1, 1 • -1, 2 • -1, 3 • -1} : Finset ℤ -/
#guard_msgs in
#check by_elab return mkSetLiteralQ q(Finset ℤ) (List.range 4 |>.map fun n : ℕ ↦ q($n • (-1 : ℤ)))

end mkSetLiteralQ
