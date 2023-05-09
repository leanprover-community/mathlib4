/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Thomas Murrills
-/
import Lean.Meta.Basic
import Lean.Meta.Tactic.Util
import Mathlib.Control.Basic
import Mathlib.Lean.Meta
import Mathlib.Data.Sum.Basic

/-!
# `backtrack`

A meta-tactic for running backtracking search, given a non-deterministic tactic
`alternatives : MVarId → MetaM (List (MetaM (List MVarId)))`.

Here the outermost list gives us alternative solutions to the input goal.
The innermost list is then the new subgoals generated in that solution.
The additional `MetaM` allows for deferring computation.

`backtrack alternatives goals` will recursively try to solve all goals in `goals`,
and the subgoals generated, backtracking as necessary.

In its default behaviour, it will either solve all goals, or fail.
A customisable `suspend` hook in `BacktrackConfig` allows suspend a goal (or subgoal),
so that it will be returned instead of processed further.
Other hooks `proc` and `discharge` (described in `BacktrackConfig`) allow running other
tactics before `alternatives`, or if all search branches from a given goal fail.

See also `nondeterministic`, an alternative implementation of the same idea,
but with simpler flow control, and no trace messages.

Currently only `solveByElim` is implemented in terms of `backtrack`.
-/

open Lean Meta

/-- Visualize an `Except` using a checkmark or a cross. -/
def Except.emoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

/-- Run a monadic function on every element of a list,
returning the list of elements on which the function fails, and the list of successful results. -/
def List.tryAllM [Monad m] [Alternative m] (L : List α) (f : α → m β) : m (List α × List β) := do
  let R ← L.mapM (fun a => (Sum.inr <$> f a) <|> (pure (Sum.inl a)))
  return (R.filterMap (fun s => match s with | .inl a => a | _ => none),
    R.filterMap (fun s => match s with | .inr b => b | _ => none))

namespace Lean.MVarId

/--
Given any tactic that takes a goal, and returns a sequence of alternative outcomes
(each outcome consisting of a list of new subgoals),
we can perform backtracking search by repeatedly applying the tactic.
-/
def firstContinuation (results : MVarId → MetaM (List (MetaM (List MVarId))))
    (cont : List MVarId → MetaM α) (g : MVarId) : MetaM α := do
  (← results g).firstM fun r => do cont (← r)

end Lean.MVarId

namespace Mathlib.Tactic

/--
Configuration structure to control the behaviour of `backtrack`:
* control the maximum depth and behaviour (fail or return subgoals) at the maximum depth,
* and hooks allowing
  * modifying intermediate goals before running the external tactic,
  * 'suspending' goals, returning them in the result, and
  * discharging subgoals if the external tactic fails.
-/
structure BacktrackConfig where
  /-- Maximum recursion depth. -/
  maxDepth : Nat := 6
  /-- An arbitrary procedure which can be used to modify the list of goals
  before each attempt to apply a lemma.
  Called as `proc goals curr`, where `goals` are the original goals for `backtracking`,
  and `curr` are the current goals.
  Returning `some l` will replace the current goals with `l` and recurse
  (consuming one step of maximum depth).
  Returning `none` will proceed to applying lemmas without changing goals.
  Failure will cause backtracking.
  (defaults to `none`) -/
  proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none
  /-- If `suspend g`, then we do not attempt to apply any further lemmas,
  but return `g` as a new subgoal. (defaults to `false`) -/
  suspend : MVarId → MetaM Bool := fun _ => pure false
  /-- `discharge g` is called on goals for which no lemmas apply.
  If `none` we return `g` as a new subgoal.
  If `some l`, we replace `g` by `l` in the list of active goals, and recurse.
  If failure, we backtrack. (defaults to failure) -/
  discharge : MVarId → MetaM (Option (List MVarId)) := fun _ => failure
  /-- If we solve any "independent" goals, don't fail. -/
  commitIndependentGoals : Bool := false

def ppMVarIds (gs : List MVarId) : MetaM (List Format) := do
  gs.mapM fun g => do ppExpr (← g.getType)

/--
Attempts to solve the `goals`, by recursively calling `alternatives g` on each subgoal that appears.
`alternatives` returns a list of list of goals (wrapped in `MetaM`).
The outermost list corresponds to alternative outcomes,
while the innermost list is the subgoals generated in that outcome.

`backtrack` performs a backtracking search, attempting to close all subgoals.

Further flow control options are available via the `Config` argument.
-/
partial def backtrack (cfg : BacktrackConfig := {}) (trace : Name := .anonymous)
    (alternatives : MVarId → MetaM (List (MetaM (List MVarId))))
    (goals : List MVarId) : MetaM (List MVarId) := do
  processIndependentGoals goals goals
where
  /--
  * `n : Nat` steps remaining.
  * `curr : List MVarId` the current list of unsolved goals.
  * `acc : List MVarId` a list of "suspended" goals, which will be returned as subgoals.
  -/
  -- `acc` is intentionally a `List` rather than an `Array` so we can share across branches.
  run (n : Nat) (curr acc : List MVarId) : MetaM (List MVarId) := do
    match n with
    | 0 => do
      -- We're out of fuel.
      throwError "backtrack exceeded the recursion limit"
    | n + 1 => do
    -- First, run `cfg.proc`, to see if it wants to modify the goals.
    let procResult? ← try
      cfg.proc goals curr
    catch e =>
      withTraceNode trace
        (return m!"{·.emoji} BacktrackConfig.proc failed: {e.toMessageData}") do
      throw e
    match procResult? with
    | some curr' => run n curr' acc
    | none =>
    match curr with
    -- If there are no active goals, return the accumulated goals.
    | [] => withTraceNode trace (return m!"{·.emoji} success!") do
        return acc.reverse
    | g :: gs =>
    -- Discard any goals which have already been assigned.
    if ← g.isAssigned then
      withTraceNode trace (return m!"{·.emoji} discarding already assigned goal {g}") do
        run (n+1) gs acc
    else
    withTraceNode trace
      -- Note: the `addMessageContextFull` ensures we show the goal using the mvar context before
      -- the `do` block below runs, potentially unifying mvars in the goal.
      (return m!"{·.emoji} working on: {← addMessageContextFull g}")
      do
        -- Check if we should suspend the search here:
        if (← cfg.suspend g) then
          withTraceNode trace
            (fun _ => return m!"⏸️ suspending search and returning as subgoal") do
          run (n+1) gs (g :: acc)
        else
          try
            -- We attempt to find an expression which can be applied,
            -- and for which all resulting sub-goals can be discharged using `run n`.
            g.firstContinuation alternatives (fun res => run n (res ++ gs) acc)
          catch _ =>
            -- No lemmas could be applied:
            match (← cfg.discharge g) with
            | none => (withTraceNode trace
                (fun _ => return m!"⏭️ deemed acceptable, returning as subgoal") do
              run (n+1) gs (g :: acc))
            | some l => (withTraceNode trace
                (fun _ => return m!"⏬ discharger generated new subgoals") do
              run n (l ++ gs) acc)
  -- A wrapper around `run`, which works on "independent" goals separately first,
  -- to reduce backtracking.
  processIndependentGoals (goals remaining : List MVarId) : MetaM (List MVarId) := do
    -- Partition the remaining goals into "independent" goals
    -- (which should be solvable without affecting the solvability of other goals)
    -- and all the others.
    let (igs, ogs) ← remaining.partitionM (MVarId.independent? goals)
    if igs.isEmpty then
      -- If there are no independent goals, we solve all the goals together via backtracking search.
      return (← run cfg.maxDepth remaining [])
    else
      withTraceNode trace
        (fun _ => return m!"independent goals {← ppMVarIds igs},"
          ++ m!" working on them before {← ppMVarIds ogs}") do
      -- Invoke `run` on each of the independent goals separately,
      -- gathering the subgoals on which `run` fails,
      -- and the new subgoals generated from goals on which it is successful.
      let (failed, newSubgoals') ← igs.tryAllM (fun g => run cfg.maxDepth [g] [])
      let newSubgoals := newSubgoals'.join
      withTraceNode trace
        (fun _ => return m!"failed: {← ppMVarIds failed}, new: {← ppMVarIds newSubgoals}") do
      -- Update the list of goals with respect to which we need to check independence.
      let goals' := (← goals.filterM (fun g => do pure !(← g.isAssigned))) ++ newSubgoals
      -- If `commitIndependentGoals` is `true`, we will return the new goals
      -- regardless of whether we can make further progress on the other goals.
      if cfg.commitIndependentGoals && !newSubgoals.isEmpty then
        return newSubgoals ++ failed ++ (← (processIndependentGoals goals' ogs <|> pure ogs))
      else if !failed.isEmpty then
        -- If `commitIndependentGoals` is `false`, and we failed on any of the independent goals,
        -- the overall failure is inevitable so we can stop here.
        failure
      else
        -- Finally, having solved this batch of independent goals,
        -- recurse (potentially now finding new independent goals).
        return newSubgoals ++ (← processIndependentGoals goals' ogs)
  -- termination_by run n curr acc => (n, curr)



namespace BacktrackOptimize

/-!
# Optimization via backtracking

These functions attempt to minimize a user-provided measure across different possible alternatives.
A specific aim is minimizing the number of subgoals generated by repeated applications of an
`apply`-like meta tactic.

-/

/-!
## Implementation notes

This is broken down into two functions: `getBestOfOneAlt` and `getBestOfAlts`.

`getBestOfAlts` folds over the different `alternatives` in the context of an optional `bestSize?`
and some `init : β`, representing the initial piece of `β` accumulated before we reached this
particular call. We can assume `! exceeds (size (init)) sizeBest`. At each stage of the fold, it
exposes some prior `newBestSize?` (which begins as `bestSize?`) and compares this to
`size (incorporate init newerBest)`. We need to stop if the value we're calculating ever exceeds
the best size.

Let's consider examining the first alternative. Using `≤` for `(not <| exceeds · ·)`, `|a|` for
`size a`, `+` for `incorporate`, and abusing notation liberally, we need to ensure that
(1) `∀ best ∈ best?, |init + newFromAlt₁| ≤ |best|`, where `newFromAlt₁` is the new piece of `β` we
get from the first alternative. When we enter the second alternative, we need to satisfy the next
version of this ((2.1) `∀ best ∈ Option β, |init + newFromAlt₂| ≤ |best|`), and also satisfy
(2.2) `∀ newFromAlt₁ ∈ newFromAlt₁?, |init + newFromAlt₂| ≤ |init + newFromAlt₁|`—that is, we also
can't be worse than any `newFromAlt₁` we might have found. However, we ensured that (1) was the
case in the first alternative, and (1) ∧ (2.2) ⇒ (2.1) as long as `exceeds` is transitive, so we
may as well just check (2.2).

In `getBestOfOneAlt`, we're building the prior `init` as we fold through the list. Suppose we
started `getBestOfOneAlt` with `init := init₀`, and we've accumulated `current : β` (starting from
`cfg.bot`) so far as we've folded through the list. Say we're examining a list element `a`. We
generate `← alternatives a` and pass down `init := init₀ + current` to `getBestOfAlts`. If we
return from `getBestOfAlts` with some `newFromAlt`, we update `current` to `current + newFromAlt`
and continue folding, then eventually return this (assuming we don't exceed the maximum size along
the way, in which case we fail).

We assume there's a function `∔` which lets `size` distribute over `+`, i.e. `|a + b| = |a| ∔ |b|`.
Then we need only receive `|init₀|` at the start of `getBestOfOneAlt`, and need only pass down
`|init₀ + current|` to `getBestOfAlts` at each list element. This might not always be the case for
all tasks we'd like to handle, but we'll leave handling that efficiently for future work; the
current implementation thus only passes down `currentSize := |init₀ + current|`, and demands a
function `add` which represents `∔`.

We use a tree `Later'` with a computed field, which lets us store the size in the constructor and
retrieve it in constant time. We then fold over the result with `incorporate` later. This lets us
avoid expensive `incorporate` operations inside alternatives which won't work out.
-/
end BacktrackOptimize

end Mathlib.Tactic
