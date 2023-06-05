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

open Lean Elab Meta Tactic Parser Qq Mathlib.Tactic SolveByElim

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

/-- Apply the `mono` tactic to a goal. This finds all lemmas tagged with `mono` and applies each
one to generate subgoals.

* If `side` is `.left` or `.right`, we only use lemmas tagged `@[mono left]` or `@[mono right]`
respectively. By default, `side` is `.both`.

* If `recurse` is `true`, we apply the mono tactic repeatedly to the goal and choose the sequence
of applications which generates the least subgoals.

* If `simpUsing` is provided, we `simp` with the given `Simp.Context` before applying the lemmas.
If `recurse` is `true`, we `simp` all goals before each application of `mono`.

* If `failIfAmbiguousMatch` is `true`, we fail whenever multiple applications of `mono` lemmas
produce the same minimal number of subgoals. If `false`, the default for the `MetaM` tactic (but
not for the tactic syntax), we simply take the first. -/
def _root_.Lean.MVarId.mono (goal : MVarId) (side : Side := .both)
    (simpUsing : Option Simp.Context := none) (recurse : Bool := false)
    (failIfAmbiguousMatch : Bool := false) :
    MetaM (List MVarId) := goal.withContext <| withReducible do
  if ! recurse then
    let goal ← match ← dsimpGoal goal Monos.SimpContext false with
    | (some goal, _) => pure goal
    | (none, _) => return []
    let goal ←
      if let some ctx := simpUsing then
        match ← simpGoal goal ctx with
        | (some (_, goal), _) => pure goal
        | (none, _) => return []
      else
        pure goal
    let (_, goal) ← goal.introsP!
    let t ← whnfR <|← instantiateMVars <|← goal.getType
    trace[Tactic.mono] "Applying monos to {t}"
    let (expr, goals) ← goal.withContext <| applyMonos t side failIfAmbiguousMatch
    goal.assign expr
    return goals
  else
    -- Preserve "stopgap" behavior using solve_by_elim. This does not use the discrtree.
    let cfg : ApplyRulesConfig := {
      backtracking := false
      transparency := .reducible
      exfalso := false }
    let cfg :=
      if let some ctx := simpUsing then
        let simpProc (goals : List MVarId) : MetaM (Option (List MVarId)) := optional do
          let goals := (← goals.mapM
            (fun g ↦ do let (a,_) ← simpGoal g ctx; return a.map Prod.snd)).reduceOption
          return goals
        { cfg with proc := fun _ curr ↦ simpProc curr }
      else
        cfg.toConfig
    goal.withContext do
      let monos := monoExt.getState (← getEnv) |>.tree.elements
      let monos := match side with
      | .both  => monos
      | .left  => monos.filter isLeft
      | .right => monos.filter isRight
      let monoLemmas : List (TermElabM Expr) :=
        monos.toList.map (liftM <| mkConstWithFreshMVarLevels ·.name)
      let ⟨lemmas, ctx⟩ ← mkAssumptionSet false false [] [] #[]
      let goals ← repeat1' (maxIters := cfg.maxDepth)
        (applyFirstLemma cfg (monoLemmas ++ lemmas) ctx) [goal]
      if ! (← goal.isAssigned) then
        throwError "mono* could not make progress on the goal"
      else
        return goals

--TODO: add `config` syntax to adjust `maxDepth` in `mono*` and add custom `proc`
open Parser.Tactic in
/-- `mono` applies all lemmas tagged with `@[mono]` to the main goal and chooses the one which
produces the fewest remaining subgoals.

* `mono*` applies `mono` lemmas repeatedly, choosing the sequence of applications which produces
the fewest goals overall up to a given `maxDepth`. `mono*` fails if it cannot make any progress on
the goal.

* `mono left` and `mono right` only apply "left" and "right" mono lemmas to the goal. Lemmas tagged
with `@[mono left]` and `@[mono right]` are considered left and right, respectively; lemmas tagged
with just `@[mono]` are considered both `left` and `right`, and are always included. By default,
all lemmas are applied.

* `mono with P, Q ...` (where `P : Prop`, `Q : Prop`, ...) asserts `P`, `Q`, ... and leaves them as
side goals. If multiple different `mono` lemmas each produce the same minimal number of subgoals
when applied, then `mono` fails; if one of those goals has e.g. type `P`, then `mono with P` can be
used to encourage `mono` to choose the set of subgoals that includes `P`.

* `mono using l₁, l₂, ...` runs `simp [l₁, l₂, ...]` before applying `mono`. `mono* using ...` runs
`simp` before each iteration of `mono`.

All syntax options can be used in combination with each other, as long as they're used in the order
given above.
-/
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

elab_rules : tactic
| `(tactic| mono $[*%$r]? $[$s:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $l,*]? ) =>
  withMainContext do
    let goal ← getMainGoal
    let side ← parseSide s
    -- Handle 'with' by asserting all hypotheses provided
    let (assertedMVarIds, goal) ←
      if let some a := a then
        let as ← a.getElems.mapM (fun a => withRef a <| Tactic.elabTermEnsuringType a q(Prop))
        trace[Tactic.mono] "asserting {as}"
        let assertedMVars ← as.mapM (fun t => mkFreshExprMVar (some t) .syntheticOpaque)
        let hs : Array Hypothesis :=
          if as.size == 1 then
            #[⟨`mono_with, as[0]!, assertedMVars[0]!⟩]
          else
            as.zipWithIndex.zipWith assertedMVars fun (a,n) mvar =>
              ⟨`mono_with |>.appendIndexAfter (n+1), a, mvar⟩
        let (_, goal) ← goal.assertHypotheses hs
        pure (assertedMVars.map (·.mvarId!), goal)
      else
        pure (#[], goal)
    -- Change the context to that of the new goal
    goal.withContext do
      -- Handle 'using'
      let ctx? : Option Simp.Context ← l.mapM fun l => do
        pure (← Tactic.mkSimpContext (←`(tactic| simp only [$l,*])) false).ctx
      -- Run `mono`.
      let newGoals ← goal.mono side ctx? r.isSome true
      -- Cleanup:
      -- Replace all internal goal usernames with appropriate user-friendly ones.
      let _ ← liftMetaM <| newGoals.foldlM (init := 1) fun n g => do
        if (← g.getTag).isInternal' then
          g.setUserName <| (`mono).appendIndexAfter n
          pure (n+1)
        else
          pure n
      -- Name all `assertedMVarIds` `mono_with_<n>`, or just `mono_with` if there's only one.
      if assertedMVarIds.size == 1 then
        assertedMVarIds[0]!.setUserName `mono_with
      else
        let _ ← liftMetaM <| assertedMVarIds.foldlM (init := 1)
          fun n g => do g.setUserName <| (`mono_with).appendIndexAfter n; pure (n+1)
      -- Change all (possibly natural) goals to syntheticOpaque.
      for goal in newGoals do goal.setKind .syntheticOpaque
      replaceMainGoal (newGoals ++ assertedMVarIds.toList)
