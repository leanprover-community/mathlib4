import Std.Lean.Elab.Tactic
import Lean.Meta.Tactic
import Mathlib.Data.Rat.Order
import Mathlib.Lean.Meta.Basic
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Util.Qq

import Mathlib.Tactic.ByApprox.Lemmas
import Mathlib.Tactic.ByApprox.Core
import Mathlib.Tactic.ByApprox.Util
import Mathlib.Tactic.ByApprox.Basic
import Mathlib.Tactic.ByApprox.Exp

namespace Mathlib.Tactic.ByApprox

open Lean hiding Rat
open Std Lean.Parser Parser.Tactic Elab Command Elab.Tactic Meta Qq

open Mathlib.Tactic.ByApprox

private lemma lt_of_le_of_ge {ra rb : ℝ} {qa qb : ℚ}
    (ha : ra ≤ qa) (hb : rb ≥ qb) (h : qa < qb) :
    ra < rb := by
  refine lt_of_le_of_lt ha (lt_of_lt_of_le ?_ hb)
  rwa [Rat.cast_lt]

-- todo standardize api
partial def byApprox (g : MVarId) : MetaM Unit := do
  let target ← instantiateMVars (← g.getType)
  trace[ByApprox] "Got target {target}"
  let (lhs, rhs, strict, ne) ← match target.getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => pure (a, b, true, false)
  | (``LE.le, #[_, _, a, b]) => pure (a, b, false, false)
  | (``GT.gt, #[_, _, a, b]) => pure (b, a, true, false)
  | (``GE.ge, #[_, _, a, b]) => pure (b, a, false, false)
  | (``Ne, #[_, a, b]) => pure (a, b, true, true)
  | _ => throwError "Expecting inequality in by_approx {target}"

  -- todo go forever?
  for precision in [0 : 50] do
    let finished ← withTraceNode `ByApprox (fun _ => pure m!"trying precision {precision}") do
      let ⟨lhs_lower, _, lhs_upper, _⟩ ← approximate precision false lhs
      let ⟨rhs_lower, _, rhs_upper, _⟩ ← approximate precision false rhs
      trace[ByApprox] "Hoping {lhs_upper} < {rhs_lower}"
      if lhs_upper < rhs_lower then
        let ⟨_, _, _, lhs_upper_prf⟩ ← approximate precision true lhs
        let ⟨_, rhs_lower_prf, _, _⟩ ← approximate precision true rhs

        let prf ← mkAppNormNum ``lt_of_le_of_ge
          #[none, none, none, none, lhs_upper_prf.get!, rhs_lower_prf.get!, none]
        if ne then
          g.assign (← mkAppM `ne_of_lt #[prf])
        else if strict then
          g.assign prf
        else
          g.assign (← mkAppM ``le_of_lt #[prf])
        return true

      if lhs_lower > rhs_upper then
        if ne then
          let ⟨_, lhs_lower_prf, _, _⟩ ← approximate precision true lhs
          let ⟨_, _, _, rhs_upper_prf⟩ ← approximate precision true rhs

          let prf ← mkAppNormNum ``lt_of_le_of_ge
            #[none, none, none, none, rhs_upper_prf.get!, lhs_lower_prf.get!, none]

          g.assign (← mkAppM ``ne_of_gt #[prf])
          return true
        else
          throwError "by_approx: {target} seems false"
      return false
    if finished then return

  throwError "by_approx failed"


/- Prove an inequality in ℝ by finding rational approximations to both sides

-/
elab "by_approx" : tactic => liftMetaFinishingTactic byApprox
