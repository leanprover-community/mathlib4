/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.FunProp.Core

/-!
## `funProp` simprocs
-/
public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

/-- Make simproc out of a theorem of the form `P → x = y` where `P` is `fun_prop` goal.

An example of such theorem is:
```
theorem HasFDerivAt.fderiv (h : HasFDerivAt f f' x) : fderiv 𝕜 f x = f' := ...
```

Warning: Currently it is assumed that the `fun_prop` goal is the last argument of the theorem!
-/
def mkFunPropSimproc (simprocName : Name) (thm : Name) : Simp.Simproc := fun e => do
  let thmExpr ← mkConstWithFreshMVarLevels thm
  let thmType ← inferType thmExpr
  let (xs,bi,statement) ← forallMetaTelescope thmType

  let .some (_,lhs,rhs) := statement.eq?
    | throwError m!"{simprocName} error: expected equality {statement}!"

  unless ← isDefEq lhs e do
    throwError m!"{simprocName} error: expected expression of the form {lhs}, got {e}!"

  -- synthesize all but last arguments
  unless ← Simp.synthesizeArgs (.decl thm) bi[:xs.size-1] xs[:xs.size-1] do
    return .continue

  -- extract fun_prop goal, for now we expect it is the last argument of the theorem
  let hf := xs[xs.size-1]!
  let hfType ← inferType hf >>= instantiateMVars

  trace[Meta.Tactic.fun_prop] m!"applying fun_prop simproc to {e} by solving {hfType}"

  unless ← isFunPropGoal hfType do
    throwError m!"{simprocName} error: expected `fun_prop` goal, got {hfType} instead!"

  let disch? := (← Simp.getMethods).discharge?
  let state : FunProp.State := { morTheorems := default, transitionTheorems := default }

  -- run fun_prop
  let (some r,_) ← funProp hfType { disch := disch? } state
    | return .continue

  unless ← isDefEq hf r.proof do
    throwError m!"{simprocName} error: failed to assign proof"

  let prf := (thmExpr.beta xs)

  return .visit { expr := rhs, proof? := prf }


/-- Simproc simplifying `deriv _ _` or `fderiv _ _ _` expressions.

More preciselly, this is a simp attribute that registers four separate simprocs for `deriv _`,
`deriv _ _`, `fderiv _ _`, `fderiv _ _ _` -/
register_simp_attr deriv_simproc

end Meta.FunProp

end Mathlib
