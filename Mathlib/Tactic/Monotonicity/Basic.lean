/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Heather MacBeth, Thomas Murrills
-/
import Mathlib.Lean.Meta
import Mathlib.Data.Array.MinMax
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Relation.Rfl

/-! # Monotonicity tactic

The tactic `mono` applies monotonicity lemmas (collected through the library by being tagged
`@[mono]`, `@[mono left]`, or `@[mono right]`).
-/

open Lean Elab Meta Tactic Parser Qq Mathlib.Tactic SolveByElim BacktrackOptimize

namespace Mathlib.Tactic.Monotonicity

open Attr

/-- Match each registered `mono` extension against `t`, returning an array of matching extensions.
-/
def getMatchingMonos (t : Expr) (side := Side.both) : MetaM (Array MonoExt) := do
  profileitM Exception "mono" (← getOptions) do --!! what does profileit do?
    let monos := monoExt.getState (← getEnv)
    let arr ← monos.tree.getMatch t
    let arr := match side with
    | .both  => arr
    | .left  => arr.filter isLeft
    | .right => arr.filter isRight
    return arr

/-- Apply a mono extension to an already fully-telescoped (and in whnf) `t`. Returns any remaining
subgoals. -/
private def applyMono (t : Expr) (m : MonoExt) : MetaM (Expr × List MVarId) := do
  let (expr, goals) ← applyMatchReducing m.name t
  trace[Tactic.mono] "Applied {m.name} to {t}"
  let goals := goals.toList
  let cfg : SolveByElim.Config := { discharge := fun _ => pure none }
  let goals ← accumulateGoals goals fun g => do
    let (lemmas, ctx) ← mkAssumptionSet false false [] [] #[]
    let goals ← solveByElim cfg lemmas ctx [g]
    goals.filterM (fun g => return ! (← succeeds g.rfl))
  return (expr, goals)


namespace Mathlib.Tactic.Monotonicity

/--
`mono` applies monotonicity rules and local hypotheses repetitively.  For example,
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```
-/
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

elab_rules : tactic
| `(tactic| mono $[*]? $[$h:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $s,*]? ) => do
  let msg (s : String) := s ++ " syntax is not yet supported in 'mono'"
  if let some h := h then throwErrorAt h (msg "'left'/'right'/'both'")
  if let some w := w then throwErrorAt w (msg "'with'")
  if let some u := u then throwErrorAt u (msg "'using'")
  let cfg ← elabApplyRulesConfig <| mkNullNode #[]
  let cfg := { cfg with
    backtracking := false
    transparency := .reducible
    exfalso := false }
  liftMetaTactic fun g => do solveByElim.processSyntax cfg false false [] [] #[mkIdent `mono] [g]
