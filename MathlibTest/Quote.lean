import Mathlib.Lean.Quote
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

open Lean Elab Term

/-! ### The syntax produced by `quote` -/

/--
info: 0
---
info: 5
---
info: -1
---
info: -7
---
info: 123456789012345678901234567890
---
info: -123456789012345678901234567891
-/
#guard_msgs in
run_meta
  for n in [(0 : Int), 5, -1, -7, 123456789012345678901234567890,
      -123456789012345678901234567891] do
    logInfo m!"{(quote n : Term)}"

/--
info: 0
---
info: 5
---
info: -7
---
info: 7 / 2
---
info: -7 / 2
---
info: -1 / 3
---
info: -123456789012345678901234567891 / 7
-/
#guard_msgs in
run_meta
  for q in [(0 : Rat), 5, -7, 7 / 2, -7 / 2, -1 / 3, -123456789012345678901234567891 / 7] do
    logInfo m!"{(quote q : Term)}"

/-! ### Quoted numbers elaborate back to the same value -/

/-- `quoteRat% q` evaluates the rational number `q`, quotes it,
and elaborates the result at the expected type. -/
elab "quoteRat% " t:term : term <= ty => do
  let q ← unsafe evalTerm Rat (mkConst ``Rat) t
  elabTerm (quote q : Term) ty

/-- `quoteInt% n` evaluates the integer `n`, quotes it,
and elaborates the result at the expected type. -/
elab "quoteInt% " t:term : term <= ty => do
  let n ← unsafe evalTerm Int (mkConst ``Int) t
  elabTerm (quote n : Term) ty

example : (quoteInt% 0 : ℤ) = 0 := rfl
example : (quoteInt% 5 : ℤ) = 5 := rfl
example : (quoteInt% -1 : ℤ) = -1 := rfl
example : (quoteInt% -7 : ℤ) = -7 := rfl
example : (quoteInt% -123456789012345678901234567891 : ℤ) =
    -123456789012345678901234567891 := rfl

-- `Int.negSucc n` is `-(n + 1)`, not `-n`.
example : (quoteInt% Int.negSucc 6 : ℤ) = -7 := rfl

example : (quoteRat% 0 : ℚ) = 0 := by norm_num
example : (quoteRat% 5 : ℚ) = 5 := by norm_num
example : (quoteRat% -7 : ℚ) = -7 := by norm_num
example : (quoteRat% 7 / 2 : ℚ) = 3.5 := by norm_num
example : (quoteRat% -7 / 2 : ℚ) = -3.5 := by norm_num
example : (quoteRat% -1 / 3 : ℚ) = -1 / 3 := by norm_num
example : (quoteRat% 6 / 4 : ℚ) = 3 / 2 := by norm_num

-- The quoted syntax has no type ascription, so it elaborates directly at other types
-- (no cast from `ℚ` is inserted, so these hold by `with_reducible rfl`).
example : (quoteInt% -7 : ℝ) = -7 := by with_reducible rfl
example : (quoteRat% -7 / 2 : ℝ) = -7 / 2 := by with_reducible rfl
example : (quoteRat% -1 / 3 : ℝ) = -1 / 3 := by with_reducible rfl
example : (quoteRat% -123456789012345678901234567891 / 7 : ℝ) =
    -123456789012345678901234567891 / 7 := by with_reducible rfl
example : (quoteRat% 6 / 4 : ℝ) = 3 / 2 := by with_reducible rfl

/-! ### Documented behaviour at other types -/

-- In `ℤ`, `/` is integer division, so a quoted non-integer rational does not keep its value.
example : (quoteRat% -7 / 2 : ℤ) = -4 := by decide

-- In `ℕ`, nonnegative integers elaborate, but negative ones do not (there is no `Neg ℕ`).
example : (quoteInt% 7 : ℕ) = 7 := rfl
example : True := by
  fail_if_success have := (quoteInt% -7 : ℕ)
  trivial

/-! ### Quoted numbers inside larger terms are bracketed correctly -/

/--
info: x * -7
---
info: (-7) ^ 2
---
info: x - -7
---
info: x * (-7 / 2)
---
info: (-7 / 2) ^ 2
---
info: x - -7 / 2
-/
#guard_msgs in
run_meta
  let x := mkIdent `x
  for q in [(quote (-7 : Int) : Term), quote (-7 / 2 : Rat)] do
    logInfo m!"{← `($x * $q)}"
    logInfo m!"{← `($q ^ 2)}"
    logInfo m!"{← `($x - $q)}"
