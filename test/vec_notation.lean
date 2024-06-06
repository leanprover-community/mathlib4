/-
Manually ported from
https://github.com/leanprover-community/mathlib/blob/fee91d74414e681a8b72cb7160e6b5ef0ec2cc0b/test/vec_notation.lean
-/
import Mathlib.Data.Fin.VecNotation

open Lean
open Lean.Meta
open Qq

set_option pp.unicode.fun false

/-! These tests are testing `PiFin.toExpr` and fail with
`local attribute [-instance] PiFin.toExpr` -/

run_cmd Elab.Command.liftTermElabM do
  let x : Fin 0 → ℕ := ![]
  guard (← isDefEq (toExpr x) q((![] : Fin 0 → ℕ)))

run_cmd Elab.Command.liftTermElabM do
  let x := ![1, 2, 3]
  guard (← isDefEq (toExpr x) q(![1, 2, 3]))

run_cmd Elab.Command.liftTermElabM do
  let x := ![![1, 2], ![3, 4]]
  guard (← isDefEq (toExpr x) q(![![1, 2], ![3, 4]]))

/-! These tests are testing `PiFin.repr` -/

#guard (toString (repr (![] : _ → ℕ)) = "![]")
#guard (toString (repr ![1, 2, 3]) = "![1, 2, 3]")
#guard (toString (repr ![![1, 2], ![3, 4]]) = "![![1, 2], ![3, 4]]")

/-! These tests are testing delaborators -/

/-- info: fun x => ![0, 1] x : Fin 2 → ℕ -/
#guard_msgs in #check fun x : Fin 2 => (![0, 1] : Fin 2 → ℕ) x
/-- info: fun x => ![] x : Fin 0 → ℕ -/
#guard_msgs in #check fun x : Fin 0 => (![] : Fin 0 → ℕ) x

example {a b c : α} : ![a, b, c] 0 = a := by simp
example {a b c : α} : ![a, b, c] 1 = b := by simp
example {a b c : α} : ![a, b, c] 2 = c := by simp

example {a b c d : α} : ![a, b, c, d] 0 = a := by simp
example {a b c d : α} : ![a, b, c, d] 1 = b := by simp
example {a b c d : α} : ![a, b, c, d] 2 = c := by simp
example {a b c d : α} : ![a, b, c, d] 3 = d := by simp
example {a b c d : α} : ![a, b, c, d] 42 = c := by simp
example {a b c d : α} : ![a, b, c, d] (-2) = c := by simp
example {a b c d : α} : ![a, b, c, d] (-0) = a := by simp

example {a b c d e : α} : ![a, b, c, d, e] 0 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 1 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 2 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 3 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 4 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 5 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 6 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 7 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 8 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 9 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 10 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123456789 = e := by simp

example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 5 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 7 = h := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 37 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 99 = d := by simp
