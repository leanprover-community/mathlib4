import Mathlib.Tactic.Core

open Lean Meta Elab

section replaceRec
/-! Test the implementation of `Expr.replaceRec` -/

/-- Reorder the last two arguments of every function in the expression.
  (The resulting term will generally not be a type-correct) -/
partial def reorderLastArguments : Expr → Expr :=
Expr.replaceRec λ e =>
  let n := e.getAppNumArgs
  if n ≥ 2 then
    some (e.getAppArgs, λ es => mkAppN e.getAppFn $ es.swap! (n - 1) (n - 2)) else
    none

def foo (f : ℕ → ℕ → ℕ) (n₁ n₂ n₃ n₄ : ℕ) : ℕ := f (f n₁ n₂) (f n₃ n₄)
def bar (f : ℕ → ℕ → ℕ) (n₁ n₂ n₃ n₄ : ℕ) : ℕ := f (f n₄ n₃) (f n₂ n₁)
#eval (do
  let d ← getConstInfo `foo
  let e := d.value!
  let s ← ppExpr { env := (← getEnv)} e
  IO.println $ "before: " ++ s
  let e := reorderLastArguments e
  let s ← ppExpr { env := (← getEnv)} e
  IO.println $ "after:  " ++ s
  let t ← Meta.inferType e
  let s ← ppExpr { env := (← getEnv)} t
  IO.println $ "new type: " ++ s
  let d ← getConstInfo `bar
  let s ← ppExpr { env := (← getEnv)} d.value!
  IO.println $ "after:  " ++ s
  guard $ e == d.value! : MetaM Unit)

end replaceRec
