/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
Ported by: Heather Macbeth
-/
import Mathlib.Lean.Meta
import Mathlib.Data.List.Defs
import Mathlib.Data.Array.MinMax
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Relation.Rfl

/-! # Monotonicity tactic

The tactic `mono` applies monotonicity rules (collected through the library by being tagged
`@[mono]`).
-/

open Lean Elab Meta Term Tactic Parser Qq Mathlib Tactic SolveByElim

namespace Mathlib.Tactic.Monotonicity

open Attr

/-- Match each registered `mono` extension against `t`, returning an array of matching extensions. -/
def getMatchingMonos (t : Expr) (side := Side.both) : MetaM (Array MonoExt) := do
  profileitM Exception "mono" (← getOptions) do --!! what does profileit do?
    let monos := monoExt.getState (← getEnv)
    let arr ← monos.tree.getMatch t
    -- For debugging, when needed:
    -- let showTypes : MetaM (Array Expr) := do
    --   return (← arr.map (·.name) |>.mapM getConstInfo).map (·.type)
    -- trace[Tactic.mono] "matched {← showTypes}"
    let arr := match side with
    | .both  => arr
    | .left  => arr.filter isLeft
    | .right => arr.filter isRight
    return arr -- return names?

/-- A maybe-faster `Array`-based version of `List.join`. -/
private def List.join : List (List α) → List α :=
  go #[]
where
  go (as : Array α) : List (List α) → List α
  | l::ls => go (as.appendList l) ls
  | [] => as.toList


/-- Apply a mono extension to an already fully-telescoped (and in whnf) `t`. Returns any remaining subgoals. -/
def applyMono (t : Expr) (m : MonoExt) : MetaM (Expr × List MVarId) := do
  let (expr, goals) ← applyMatchReducing m.name t
  trace[Tactic.mono] "Applied {m.name} to {t}"
  let goals := goals.toList
  let (lemmas, ctx) ← mkAssumptionSet false false [/-(←`(term|le_refl))-/] [] #[]
  let cfg : SolveByElim.Config := { failAtMaxDepth := false, discharge := fun _ => pure none }
  let goals ←
    try
    -- attempt to prove as many goals as possible
      solveByElim cfg lemmas ctx goals
    catch _ =>
      trace[Tactic.mono] "solveByElim failed"
      pure goals
  let goals := List.join <|← goals.mapM (fun g => try g.rfl catch _ => pure [g])
  return (expr, goals)

/-- Apply all registered `mono` extensions to the type `t`. Returns an inhabitant of `t` and  -/
def applyMonos (t : Expr) (side : Side := .both) : MetaM (Expr × List MVarId) := do
  let monos ← getMatchingMonos t side
  trace[Tactic.mono] "matched:\n{monos.map (·.name) |>.toList}"
  /- Porting note: we use the old mathlib method of using the application that produces the fewest subgoals. This is subject to change. -/
  if monos.isEmpty then throwError "no monos apply"
  let mut results : Array (Expr × List MVarId) := #[]
  for m in monos do --!! do we need a save stat?
    match ← try? <| applyMono t m with
    | some (e, []) => return (e, []) -- Finish immediately if we find one that proves `t`
    | some (e, l)  => results := results.push (e, l)
    | none         => pure ()
  if results.isEmpty then throwError "no monos apply"
  trace[Tactic.mono] "got potential proof terms with the following subgoals:\n{results}"
  let bestMatches := results.minimalBy' (·.2.length)
  if bestMatches.size == 1 then
    trace[Tactic.mono] "found {bestMatches[0]!}"
    return bestMatches[0]!
  else
    let (bestMatchTypes : Array (List Expr)) ← bestMatches.mapM (·.2.mapM (·.getType))
    throwError "Found multiple good matches which each produced the same number of subgoals. Write
      `mono with ...` and include one or more of the subgoals in one of the following lists to
      encourage `mono` to use that list.\n{bestMatchTypes}"

Temporary syntax change: Lean 3 `mono` applied a single monotonicity rule, then applied local
hypotheses and the `rfl` tactic as many times as it could.  This is hard to implement on top of
`solve_by_elim` because the counting system used in the `maxDepth` field of its configuration would
count these as separate steps, throwing off the count in the desired configuration
`maxDepth := 1`.  So instead we just implement a version of `mono` in which monotonicity rules,
local hypotheses and `rfl` are all applied repeatedly until nothing more is applicable.  The syntax
for this in Lean 3 was `mono*`. Both `mono` and `mono*` implement this behavior for now.
-/

open Lean Elab Tactic Parser Tactic
open Mathlib Tactic SolveByElim

/-- !! Apply the `mono` tactic to a goal. -/
def _root_.Lean.MVarId.mono (goal : MVarId) (side : Side := .both) : MetaM (List MVarId) := do
  let goal ← match ← dsimpGoal goal Monos.SimpContext with
  | (some goal, _) => pure goal
  | (none, _) => return []
  let (_, goal) ← goal.introsP!
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  trace[Tactic.mono] "Applying monos to {t}"
  let (expr, goals) ← applyMonos t side
  goal.assign expr
  return goals


/--
`mono` needs its documentation string written.
-/
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

--TODO: factor out `mono*` etc. into `MetaM`
elab_rules : tactic
| `(tactic| mono $[*%$r]? $[$s:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $l,*]? ) =>
  withMainContext do
    let goal ← getMainGoal
    let side ← parseSide s
    -- Handle 'with' by asserting all hypotheses provided
    let (assertedMVarIds, goal) ←
      if let some a := a then
        let as ← a.getElems.mapM (Tactic.elabTermEnsuringType · q(Prop))
        let assertedMVars ← as.mapM (fun t => mkFreshExprMVar (some t) .syntheticOpaque)
        let hs : Array Hypothesis := as.zipWith assertedMVars (⟨Name.anonymous,·,·⟩)
        let (_, goal) ← goal.assertHypotheses hs
        pure (assertedMVars.map (·.mvarId!), goal)
      else
        pure (#[], goal)
    -- Handle  '*'
    if r.isNone then
      -- Handle 'using' in the non-'*' case
      let goal ←
        if let some l := l then
          let { ctx .. } ← Tactic.mkSimpContext (←`(tactic| simp only [$l,*])) false
          match ← simpGoal goal ctx with
          | (some (_, goal), _) => pure goal
          | (none, _) => replaceMainGoal []; return ()
        else
          pure goal
      -- Apply mono once
      let newGoals ← goal.mono side
      for goal in newGoals do goal.setKind .syntheticOpaque
      replaceMainGoal (newGoals ++ assertedMVarIds.toList)
    else
      -- Handle 'using' in the '*' case
      if let some l := l then
        let { ctx .. } ← Tactic.mkSimpContext (←`(tactic| simp only [$l,*])) false
        let monoAfterSimp (goal : MVarId) : TacticM (List MVarId) := do
          let goal ← match ← simpGoal goal ctx with
          | (some (_, goal), _) => pure goal
          | (none, _) => return []
          goal.mono side
        let newGoals ← List.repeatM [goal] monoAfterSimp
        for goal in newGoals do goal.setKind .syntheticOpaque
        replaceMainGoal (newGoals ++ assertedMVarIds.toList)
      else
        let newGoals ← List.repeatM [goal] (·.mono side)
        for goal in newGoals do goal.setKind .syntheticOpaque
        replaceMainGoal (newGoals ++ assertedMVarIds.toList)

