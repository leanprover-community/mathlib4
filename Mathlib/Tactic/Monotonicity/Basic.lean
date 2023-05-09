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

/-- `apply` all registered `mono` extensions of the given `side` to the type `t`. Find the one that
creates the fewest goals, and return the resulting inhabitant of `t` and a list of any goals in
that expression.

If a proof of `t` that creates no goals is found, that proof is immediately used.

If multiple mono extensions yield a minimal (nonzero) number of subgoals, then the behavior is
guided by `failIfAmbiguousMatch`. If `true`, we fail with an error message. If `false`, we choose
the first one that attains the minimum.
-/
private def applyMonos (t : Expr) (side : Side) (failIfAmbiguousMatch : Bool) :
    MetaM (Expr × List MVarId) := do
  let monos ← getMatchingMonos t side
  trace[Tactic.mono] "matched:\n{monos.map (·.name) |>.toList}"
  if monos.isEmpty then throwError "no monos apply"
  let mut results : Array (Meta.SavedState × Expr × List MVarId) := #[]
  let s ← saveState
  for m in monos do
    match ← optional (applyMono t m) with
    | some (e, []) => return (e, []) -- Finish immediately if we find one that proves `t`
    | some (e, l)  => do results := results.push (← saveState, e, l)
    | none         => pure ()
    s.restore
  trace[Tactic.mono] "got potential proof terms with the following subgoals:\n{results.map (·.2)}"
  let bestMatches := results.argmins (·.2.2.length)
  let some (s, e, l) := bestMatches[0]? | throwError "no monos apply"
  if bestMatches.size == 1 || ! failIfAmbiguousMatch then
    s.restore
    return (e, l)
  else
    let (bestMatchTypes : MessageData) ← do
      let a ← bestMatches.mapM fun (s,_,l) => do
        s.restore; l.mapM fun g => do addMessageContextFull (← g.getType)
      pure <| toMessageList (a.map toMessageData)
    throwError m!"Found multiple good matches which each produced the same number of subgoals. "
      ++ m!"Write `mono with ...` and include the types of one or more of the subgoals in one of "
      ++ m!"the following lists to encourage `mono` to use that list.\n{bestMatchTypes}"

/-- `apply` all `mono` extensions of a given `side` to the `goal` to produce a list of thunked
alternatives in `MetaM`. This form is used for `mono*`.  -/
private def applyMonosAlternatives (side : Side) (goal : MVarId) :
    MetaM (List (MetaM (List MVarId))) := withReducible do
  trace[Tactic.mono] "running applyMonosAlternatives on {goal}"
  let goal? ← dsimpGoal goal Monos.SimpContext false
  let goal ← match goal? with
  | (some goal, _) => pure goal
  | (none, _) => return []
  let (_, goal) ← goal.introsP!
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  let monos ← getMatchingMonos t side
  trace[Tactic.mono] "matched:\n{monos.map (·.name) |>.toList}"
  if monos.isEmpty then throwError "no monos apply"
  return monos.toList.map fun m => goal.withContext do
    let (e, gs) ← applyMono t m; goal.assign e; pure gs

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
