/-
Manually ported from
https://github.com/leanprover-community/mathlib/blob/fee91d74414e681a8b72cb7160e6b5ef0ec2cc0b/test/vec_notation.lean
-/
import Mathlib.Data.Fin.VecNotation

/-! These tests are testing `PiFin.toExpr` and fail with
`local attribute [-instance] PiFin.toExpr` -/

open Lean
open Lean.Meta
open Qq

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
