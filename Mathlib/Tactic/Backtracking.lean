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

/-- The config data required for `minimizeListAlternatives` and related functions.

This data defines the notions necessary to minimize a resulting value `β` procedurally.
Specifically, we have a notion of `size : β → γ`, and notion of whether one magnitude of type `γ`
`exceeds` another, implying that the `β` with the excessive size can be discarded as non-minimal.
We also give a means to `incorporate` elements of `β` together when multiple
-/
structure BacktrackMinimizeListConfig (m : Type _ → Type _) [Monad m] [Alternative m]
    [MonadBacktrack σ m] (α β : Type _) (γ : Type v) where
  /-- The maximum recursion depth. -/
  maxDepth : Nat := 6
  /-- An arbitrary procedure which can be used to modify the list of `α`s
  before each attempt to apply alternatives.
  Called as `proc init curr`, where `init` is the initial list of `α`s,
  and `curr` are the current list of `α`s.
  Returning `some l` will replace the current `α`s with `l` just before alternatives are generated.
  Note that this does not consume a step of maximum depth.
  Returning `none` will proceed to generating alternatives.
  Failure will cause the whole list to fail and cause backtracking.
  (Defaults to returning `none`.) -/
  proc : List α → List α → m (Option (List α)) := fun _ _ => pure none
  /-- The minimal element of `β` to begin the search with. This should be a left identity for
  `incorporate`, i.e. `incorporate bot a = a`. -/
  bot : β
  /-- A function to calculate the size of a possible best element (`β`), where the notion of size
  is given by `γ` and `exceeds`. This function should be cheap. -/
  size : β → γ
  /-- An operation to add two sizes together. `size` should distribute over
  `incorporate : β → β → β` via `add : γ → γ → γ`; i.e., we should have
  `add (size a) (size b) = size (incorporate a b)`. -/
  add : γ → γ → γ
  /-- `exceeds (size newBestCandidate) (size oldBest)` should be `true` exactly when
  `newBestCandidate` is too big to be considered a minimum. This implies that the
  `newBestCandidate` is not actually viable, and will cause backtracking and/or movement to the
  next alternative.
  -/
  exceeds : γ → γ → Bool
  /-- `takeBestOfEq oldBest newBestCandidate` is used only when two candidates `newBestCandidate`,
  `oldBest` are "equal" in the sense that neither exceed the other; that is, both
  `exceeds (size newBestCandidate) (size oldBest)` and
  `exceeds (size oldBest) (size newBestCandidate)` are `false`. Note that if `exceeds` behaves like
  `≥`, `takeBestOfEq` will never be reached. In this case, `takeBestOfEq` should be set to `none`.
  However, if `exceeds` behaves like `>`, `takeBestOfEq` may be reached. It is always called with
  the older candidate in the first argument and the newer one in the second. By default, this is
  `none`, which, if encountered, simply takes the first `best`. -/
  takeBestOfEq? : Option (σ × β → σ × β → m β) := none
  /-- `incorporate current localBest` represents the "addition" of two necessary components of a
  minimal element. This is called to consolidate the `current` minimal elements obtained from the
  list currently being examined with the `localBest` generated from the next element in the list. -/
  incorporate : β → β → β
  /-- We call this function when either `alternatives a` fails, every alt in `← alternatives a`
  fails, or we're out of fuel. `fromAltsFailure a atZeroFuel` is used for
  the new `current` element at `a`; `atZeroFuel` is `true` exactly when we have reached `maxDepth`.
  Failure causes the whole list in which `a` was encountered to fail. -/
  fromAltsFailure : α → Bool → m β := fun _ _ => failure
  /-- The name of the traceclass to trace with. -/
  trace : Name := `Backtrack.Minimize

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

/-- A tree specialized for holding the values produced in `BacktrackOptimize` functions. This holds
a computed field—the size—at each node and leaf. The arguments `s` and `add` used to compute the
size will be given in practice by `cfg.size` and `cfg.add`. -/
inductive Later' (β γ σ : Type) (s : β → γ) (add : γ → γ → γ) where
| of : β → Later' β γ σ s add
| incorporateLater : Later' β γ σ s add → Later' β γ σ s add → Later' β γ σ s add
| takeBestOfEqLater : σ × Later' β γ σ s add → σ × Later' β γ σ s add → Later' β γ σ s add
  with
    /-- The size of a given node. -/
    @[computed_field] size : ∀ β γ σ s add, Later' β γ σ s add → γ
    | _, _, _, s, _, .of b => s b
    | _, _, _, _, add, .incorporateLater i₁ i₂ => add i₁.size i₂.size
    | _, _, _, s, _, .takeBestOfEqLater (_,b) _ => b.size -- trust that the sizes are equal

/-- A tree specialized for holding the values produced in `BacktrackOptimize` functions. This holds
a computed field—the size—at each node and leaf. This is an abbreviation for `Later'` which keeps
the types implicit. -/
@[inline] abbrev Later (σ) (s : β → γ) (add) := Later' _ _ σ s add

instance [ToMessageData β] : ToMessageData (Later (β := β) σ s add) where
  toMessageData := let rec f := fun
    | .of b => toMessageData b
    | .incorporateLater b b' => f b ++ " + " ++ f b'
    | .takeBestOfEqLater (_,b) (_,b') =>
      "takeBestOfEq (" ++ f b ++ ", " ++ f b' ++ ")"
    f

/-- The core of `minimizeListAlternatives`. Instead of returning the best, this returns the full
tree which represents the best, without having evaluated `incorporate` or `takeBestOfEq`, but
merely representing them as nodes on the tree. We can exploit this to e.g. efficiently get a list
of leaves of the things that together constitute the best list, without explicitly using
`β := List α`. -/
partial def minimizeListAlternativesCore [Monad m] [Alternative m] [MonadBacktrack σ m]
    -- instances to enable tracing
    [MonadExcept ε m] [MonadOptions m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadTrace m]
    [MonadRef m] [AddMessageContext m] [ToMessageData α] [ToMessageData β]
    -- arguments
    (init : List α) (alternatives : α → m (List (m (List α))))
    (cfg : BacktrackMinimizeListConfig m α β γ) : m (Option (Later σ cfg.size cfg.add)) :=
  getBestOfOneAlt none (cfg.size cfg.bot) cfg.maxDepth init
where
  /-- Abbreviated function for adding trace nodes to make the following code less verbose. -/
  withTrace {α} (msg : MessageData) : m α → m α := withTraceNode cfg.trace (fun _ => return msg)
  -- Each of the following functions reports back the best evolution it could find starting with
  -- its arguments (in contrast to reporting the best overall so far).
  -- `best?` is the local best, if one's been found yet.
  /-- This function takes the best out of a single alternative, which here takes the form of a
  list. That means that we need to `incorporate`(`Later`) the best for each set of alternatives
  generated by each element of the list. If generating alternatives fails, `fromAltsFailure` may
  return some `β`, depending on the `cfg`. If what we get from this alternative exceeds the best,
  then we fail. -/
  getBestOfOneAlt (bestSize? : Option γ) (initSize : γ) (fuel : Nat) (as : List α) :
      m (Option (Later σ cfg.size cfg.add)) := do
    let as := (← cfg.proc init as).getD as
    let newBest? ← optional <| as.foldlM (init := Later'.of cfg.bot) fun current a =>
      withTrace (m!"➡️ working on list element {a} with current {current}") do
      let newFromAlts?? ← optional (do
        guard (fuel != 0) -- If we're out of fuel, fail as though the alternatives had failed.
        withTrace (m!"⬇️ exploring alternatives generated by {a}") <|
          getBestOfAlts bestSize? (cfg.add initSize current.size) (fuel-1) (← alternatives a))
      let newFromAlts ← match newFromAlts?? with
      -- If either `alternatives` or every alt generated by `alternatives` failed, call
      -- `fromAltsFailure`.
      | none =>
        withTrace (if fuel == 0 then
            m! "❌➡️ fuel is empty"
          else
            m!"❌⬆➡️ generating more alternatives failed") <|
          Later'.of <$> cfg.fromAltsFailure a (fuel == 0)
      -- If nothing beat the best, this alt isn't viable, and we fail.
      | some none => withTrace (m!"❌⬆ no alternatives were minimal") failure
      | some (some newFromAlts) => withTrace (m!"got {newFromAlts}") <| pure newFromAlts
      -- may as well fail the whole list if `best` is better than `newCurrent`
      let newCurrent := Later'.incorporateLater current newFromAlts
      if bestSize?.any <| cfg.exceeds newCurrent.size then
        withTrace (m!"❌⬆️ {newFromAlts} is worse than the best, failing")
          failure
      else
        withTrace
          (m!"✅➡️ {newFromAlts} is not worse than the best, continuing")
          (pure newCurrent)
    -- Return any new contribution to the best.
    withTrace (if let some newBest := newBest? then
        m!"✅⬆️ finished this alternative with new best {newBest}"
          else
        m!"❌⬆️ did not find a new best from this alternative") <| pure newBest?
  /-- This function takes the best out of all of the possibilities given in `alts`. If nothing
  better than the best was found, we return `pure none`. If every alt failed, the whole function
  fails. -/
  getBestOfAlts (bestSize? : Option γ) (initSize : γ) (fuel : Nat) (alts : List (m (List α))) :
      m (Option (Later σ cfg.size cfg.add)) := do
    let initState ← saveState
    -- The bit `b` keeps track of whether we've seen a successful alt yet.
    let (b, _, bestOfAlts?) ←
      alts.foldlM (init := (false, bestSize?, none)) fun (b, bestSize?, bestOfAlts?) alt => do
        restoreState initState
        let some as ← optional alt | pure (b, bestSize?, bestOfAlts?)
        withTrace (m!"❓ working on alternative {as}") <|
        -- Since we've successfully generated an alt, set `b` to `true`.
        (true,·) <$> do
        -- Try to get the best evolution of `as`.
        let newBestOfAlts? ← getBestOfOneAlt bestSize? initSize fuel as <|> pure none
        let s' ← saveState
        -- If we exceeded the local best? while finding `newBestOfAlts?`, continue
        let some newBestOfAlts := newBestOfAlts?
          | restoreState initState; pure (bestSize?, bestOfAlts?)
        let newSize := cfg.add initSize newBestOfAlts.size
        -- if `newSize` is bigger than some `bestSize`, go on to the next alt.
        if bestSize?.any (cfg.exceeds newSize) then
          withTrace (m!"❓➡️ worse than the best") <|
            pure (bestSize?, bestOfAlts?)
        else if bestSize?.all (cfg.exceeds · newSize) then
          withTrace (m!"❓➡️ found a new best {newBestOfAlts}") <|
            pure (some newSize, some (s', newBestOfAlts))
        else
          match bestOfAlts? with
          | none => (withTrace (m!"❓➡️ found a new best, equal to an existing one") <|
              pure (some newSize, some (s', newBestOfAlts)))
          | some bestOfAltsWithState =>
            if cfg.takeBestOfEq?.isNone then
              withTrace (m!"❓➡️ takeBestOfEq not found, using {bestOfAltsWithState.2}") <|
                pure (bestSize?, bestOfAltsWithState)
            else
              (withTrace (m!"❓➡️ using takeBestOfEq") <|
                pure (some newSize,
                  some (s', Later'.takeBestOfEqLater (s', newBestOfAlts) bestOfAltsWithState)))
    -- Exit the loop. If no alts were successfully generated, meaning that every element of
    -- `(← alternatives a)` was `failure` (and therefore that `b` is `false`), fail.
    unless b do failure
    -- If nothing better than the best was obtained, return `none`.
    let some (s, bestOfAlts) := bestOfAlts? | restoreState initState; pure none
    restoreState s
    withTrace (m!"❓✅⬆️ found a new best among all alternatives {bestOfAlts}") <|
      pure bestOfAlts

end BacktrackOptimize

end Mathlib.Tactic
