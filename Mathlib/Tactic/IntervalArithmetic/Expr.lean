module

public import Mathlib.Tactic.IntervalArithmetic.Definitions

set_option linter.style.header false

public meta section

open Lean Meta Mathlib IntervalArithmetic

namespace Lean.Expr

/-- If `e` is an `Expr` of the form `x.toSet φ` return `some (x, φ)`. -/
def IntervaltoSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Interval.toSet 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

/-- If `e` is an `Expr` of the form `r ∈ s` return `some (r, s)`. -/
def memSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Membership.mem 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

/-- If `e` is an `Expr` of the form `r ∈ x.toSet φ` return `some (r, x, φ)`. -/
def memIntervaltoSet? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (r,s) ← memSet? e
  let (x, φ) ← IntervaltoSet? s
  return (r, x, φ)

/-- If `e` is an `Expr` of the form `r ∈ x.toSet φ`, and `r, x` are free variables, return
`(r.fvarId!, x.fvarId!, φ)`. -/
def intervalHyp? (e : Expr) : Option (FVarId × FVarId × Expr) := do
  let (r, x, φ) ← memIntervaltoSet? e
  return (← r.fvarId?, ← x.fvarId?, φ)

/-- If `e` is a function application, returns an array of the explicit arguments of `e`. -/
def _root_.Lean.Expr.getExplicitAppArgs (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  let param_info := (← getFunInfo e.getAppFn).paramInfo
  return Prod.fst <$> (args.zip param_info).filter (fun ⟨_, p⟩ ↦ p.isExplicit)

/-- Given `Expr`s `r, x, φ`, forms the `Expr`: `r ∈ x.toSet φ`. -/
def mkMemInterval (r x φ : Expr) : MetaM Expr := do
  return ← mkAppM ``Membership.mem #[(← mkAppM ``IntervalArithmetic.Interval.toSet #[φ, x]), r]
end Lean.Expr

namespace IntervalArithmetic

inductive Ineq
  | le
  | lt

/- `Option` version of `ineq?` -/
def ineq? (e : Expr) : Option (Ineq × Expr × Expr × Expr) :=
  match e.le? with
  | some p => some (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => some (Ineq.lt, p)
  | none => none
end IntervalArithmetic
