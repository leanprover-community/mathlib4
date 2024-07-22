import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.Prime

section Csimp

/-!
We test that `@[csimp]` replaces `jacobiSym` (i.e. `J(· | ·)`) and `legendreSym` with
`jacobiSym.fastJacobiSym` at runtime.
-/

open scoped NumberTheorySymbols

/-- info: -1 -/
#guard_msgs in
#eval J(123 | 335)

/-- info: -1 -/
#guard_msgs in
#eval J(-2345 | 6789)

/-- info: 1 -/
#guard_msgs in
#eval J(-1 | 1655801)

/-- info: -1 -/
#guard_msgs in
#eval J(-102334155 | 165580141)

/-- info: -1 -/
#guard_msgs in
#eval J(58378362899022564339483801989973056405585914719065 |
  53974350278769849773003214636618718468638750007307)

instance prime_1000003 : Fact (Nat.Prime 1000003) := ⟨by norm_num1⟩
/-- info: -1 -/
#guard_msgs in
#eval @legendreSym 1000003 prime_1000003 7

-- Should replace `legendreSym` with `fastJacobiSym` without using `Fact p.Prime`
/--
warning: declaration uses 'sorry'
---
info: 1
-/
#guard_msgs in
#eval @legendreSym (2 ^ 11213 - 1) sorry 7

end Csimp
