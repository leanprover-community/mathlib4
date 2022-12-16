import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Tactic.RunCmd
import Mathlib.Init.Data.Nat.Notation

open Lean Meta Elab Command

section replaceRec
/-! Test the implementation of `Expr.replaceRec` -/

/-- Reorder the last two arguments of every function in the expression.
  (The resulting term will generally not be a type-correct) -/
def reorderLastArguments : Expr → Expr :=
  Expr.replaceRec λ r e =>
    let n := e.getAppNumArgs
    if n ≥ 2 then
      mkAppN e.getAppFn <| e.getAppArgs.map r |>.swap! (n - 1) (n - 2)
    else
      none

def foo (f : ℕ → ℕ → ℕ) (n₁ n₂ n₃ n₄ : ℕ) : ℕ := f (f n₁ n₂) (f n₃ n₄)
def bar (f : ℕ → ℕ → ℕ) (n₁ n₂ n₃ n₄ : ℕ) : ℕ := f (f n₄ n₃) (f n₂ n₁)

run_cmd liftTermElabM <| do
  let d ← getConstInfo `foo
  let e := d.value!
  logInfo m!"before: {e}"
  let e := reorderLastArguments e
  logInfo m!"after: {e}"
  let t ← Meta.inferType e
  logInfo m!"new type: {t}"
  let d ← getConstInfo `bar
  logInfo m!"after: {d.value!}"
  guard $ e == d.value!

end replaceRec
