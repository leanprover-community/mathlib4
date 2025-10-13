/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw
-/

import Mathlib.Tactic.Positivity.Core
import Mathlib.Util.DischargerAsTactic

/-!
# Discharger for `field_simp` tactic

The `field_simp` tactic (implemented downstream from this file) clears denominators in algebraic
expressions. In order to do this, the denominators need to be certified as nonzero. This file
contains the discharger which carries out these checks.

Currently the discharger tries four strategies:
1. `assumption`
2. `positivity`
3. `norm_num`
4. `simp` with the same simp-context as the `field_simp` call which invoked it

TODO: Ideally the discharger would be just `positivity` (which, despite the name, has robust
handling of general `≠ 0` goals, not just `> 0` goals). We need the other strategies currently to
get (a cheap approximation of) `positivity` on fields without a partial order.

The refactor of `positivity` to avoid a partial order assumption would be large but not
fundamentally difficult.

### Main declarations

* `Mathlib.Tactic.FieldSimp.discharge`: the discharger, of type `Expr → SimpM (Option Expr)`

* `field_simp_discharge`: tactic syntax for the discharger (most useful for testing/debugging)

-/

namespace Mathlib.Tactic.FieldSimp

open Lean Elab.Tactic Parser.Tactic Lean.Meta
open Qq

/-- Constructs a trace message for the `discharge` function. -/
private def dischargerTraceMessage {ε : Type*} (prop : Expr) :
    Except ε (Option Expr) → SimpM MessageData
| .error _ | .ok none => return m!"{crossEmoji} discharge {prop}"
| .ok (some _) => return m!"{checkEmoji} discharge {prop}"

open private Simp.dischargeUsingAssumption? from Lean.Meta.Tactic.Simp.Rewrite

/-- Discharge strategy for the `field_simp` tactic. -/
partial def discharge (prop : Expr) : SimpM (Option Expr) :=
  withTraceNode `Tactic.field_simp (dischargerTraceMessage prop) do
    -- Discharge strategy 1: Use assumptions
    if let some r ← Simp.dischargeUsingAssumption? prop then
      return some r

    -- Discharge strategy 2: Normalize inequalities using NormNum
    let prop : Q(Prop) ← (do pure prop)
    let pf? ← match prop with
    | ~q(($e : $α) ≠ $b) =>
        try
          let res ← Mathlib.Meta.NormNum.derive prop
          match res with
          | .isTrue pf => pure (some pf)
          | _ => pure none
        catch _ =>
          pure none
    | _ => pure none
    if let some pf := pf? then return some pf

    -- Discharge strategy 3: Use positivity
    let pf? ←
      try some <$> Mathlib.Meta.Positivity.solve prop
      catch _ => pure none
    if let some pf := pf? then return some pf

    -- Discharge strategy 4: Use the simplifier
    Simp.withIncDischargeDepth do
      let ctx ← readThe Simp.Context
      let stats : Simp.Stats := { (← get) with }

      -- Porting note: mathlib3's analogous field_simp discharger `field_simp.ne_zero`
      -- does not explicitly call `simp` recursively like this. It's unclear to me
      -- whether this is because
      --   1) Lean 3 simp dischargers automatically call `simp` recursively. (Do they?),
      --   2) mathlib3 norm_num1 is able to handle any needed discharging, or
      --   3) some other reason?
      let ⟨simpResult, stats'⟩ ←
        simp prop ctx #[(← Simp.getSimprocs)]
          discharge stats
      set { (← get) with usedTheorems := stats'.usedTheorems, diag := stats'.diag }
      if simpResult.expr.isConstOf ``True then
        try
          return some (← mkOfEqTrue (← simpResult.getProof))
        catch _ =>
          return none
      else
        return none

@[inherit_doc discharge]
elab "field_simp_discharge" : tactic => wrapSimpDischarger Mathlib.Tactic.FieldSimp.discharge

end Mathlib.Tactic.FieldSimp
