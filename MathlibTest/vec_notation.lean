/-
Manually ported from
https://github.com/leanprover-community/mathlib/blob/fee91d74414e681a8b72cb7160e6b5ef0ec2cc0b/test/vec_notation.lean
-/
import Mathlib.Data.Fin.VecNotation

open Lean
open Lean.Meta
open Qq

set_option linter.style.setOption false in
set_option pp.unicode.fun false

/-- info: ![1, 1 + 1, 1 + 1 + 1] : Fin (Nat.succ 2) → ℤ -/
#guard_msgs in
#check by_elab return PiFin.mkLiteralQ ![q(1 : ℤ), q(1 + 1), q(1 + 1 + 1)]

/-! These tests are testing `PiFin.toExpr` and fail with
`local attribute [-instance] PiFin.toExpr` -/

run_elab do
  let x : Fin 0 → ℕ := ![]
  guard (← isDefEq (toExpr x) q((![] : Fin 0 → ℕ)))

run_elab do
  let x := ![1, 2, 3]
  guard (← isDefEq (toExpr x) q(![1, 2, 3]))

run_elab do
  let x := ![![1, 2], ![3, 4]]
  guard (← isDefEq (toExpr x) q(![![1, 2], ![3, 4]]))

/-! These tests are testing `PiFin.repr` -/

#guard (toString (repr (![] : _ → ℕ)) = "![]")
#guard (toString (repr ![1, 2, 3]) = "![1, 2, 3]")
#guard (toString (repr ![![1, 2], ![3, 4]]) = "![![1, 2], ![3, 4]]")

/-! These tests are testing delaborators -/

set_option linter.style.commandStart false

/-- info: fun x => ![0, 1] x : Fin 2 → ℕ -/
#guard_msgs in #check fun x : Fin 2 => (![0, 1] : Fin 2 → ℕ) x
/-- info: fun x => ![] x : Fin 0 → ℕ -/
#guard_msgs in #check fun x : Fin 0 => (![] : Fin 0 → ℕ) x

section
variable {a b c d e f g h : α}


example : ![a] 0 = a := by dsimp only [Matrix.cons_val]
example : ![a] 1 = a := by dsimp only [Matrix.cons_val]
example : ![a] 2 = a := by dsimp only [Matrix.cons_val]
example : ![a] (-1) = a := by dsimp only [Matrix.cons_val]

example : ![a, b, c] 0 = a := by dsimp only [Matrix.cons_val]
example : ![a, b, c] 1 = b := by dsimp only [Matrix.cons_val]
example : ![a, b, c] 2 = c := by dsimp only [Matrix.cons_val]

example : ![a, b, c, d] 0 = a := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d] 1 = b := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d] 2 = c := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d] 3 = d := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d] 42 = c := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d] (-2) = c := by dsimp only [Matrix.cons_val]

example : ![a, b, c, d, e] 0 = a := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 1 = b := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 2 = c := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 3 = d := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 4 = e := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 5 = a := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 6 = b := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 7 = c := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 8 = d := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 9 = e := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 10 = a := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 123 = d := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e] 123456789 = e := by dsimp only [Matrix.cons_val]

example : ![a, b, c, d, e, f, g, h] 5 = f := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e, f, g, h] (5 : Fin (4 + 4)) = f := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e, f, g, h] 7 = h := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e, f, g, h] 37 = f := by dsimp only [Matrix.cons_val]
example : ![a, b, c, d, e, f, g, h] 99 = d := by dsimp only [Matrix.cons_val]

end

open Matrix

example {a b c : α} {f : Fin 3 → α} : vecCons a (vecCons b (vecCons c f)) 0 = a := by dsimp only [Matrix.cons_val]
example {a b c : α} {f : Fin 3 → α} : vecCons a (vecCons b (vecCons c f)) 2 = c := by dsimp only [Matrix.cons_val]
example {a b c : α} {f : Fin 3 → α} : vecCons a (vecCons b (vecCons c f)) (-1) = f 2 := by dsimp only [Matrix.cons_val]
example {a b c : α} {f : Fin 3 → α} : vecCons a (vecCons b (vecCons c f)) 8 = c := by dsimp only [Matrix.cons_val]

example {a b c : α} {n : ℕ} {f : Fin n → α} : vecCons a (vecCons b (vecCons c f)) 0 = a := by dsimp only [Matrix.cons_val]
example {a b c : α} {n : ℕ} {f : Fin n → α} : vecCons a (vecCons b (vecCons c f)) 2 = c := by dsimp only [Matrix.cons_val]

example {a b c : α} {n : ℕ} {f : Fin n.succ → α} :
    vecCons a (vecCons b (vecCons c f)) 3 = f 0 := by dsimp only [Matrix.cons_val]
example {a b c : α} {n : ℕ} {f : Fin n.succ → α} :
    vecCons a (vecCons b (vecCons c f)) 3 = f 0 := by dsimp only [Matrix.cons_val]
example {a b c : α} {n : ℕ} {f : Fin (n + 2) → α} :
    vecCons a (vecCons b (vecCons c f)) 4 = f 1 := by dsimp only [Matrix.cons_val]

-- these won't be true by `dsimp`, so need a separate simproc
-- example {a b c : α} {n : ℕ} {f : Fin n.succ → α} :
--     vecCons a (vecCons b (vecCons c f)) (-1) = f (-1) := by simp
-- example {a b c : α} {n : ℕ} {f : Fin (n + 2) → α} :
--     vecCons a (vecCons b (vecCons c f)) (-2) = f (-2) := by simp
