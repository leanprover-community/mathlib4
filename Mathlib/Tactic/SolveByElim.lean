/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, David Renshaw
-/
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.Core
import Mathlib.Lean.LocalContext

/-!
A work-in-progress replacement for Lean3's `solve_by_elim` tactic.
We'll gradually bring it up to feature parity.
-/

open Lean Meta Elab Tactic

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def Lean.Meta.getLocalHyps : MetaM (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

initialize registerTraceClass `Meta.Tactic.solveByElim

namespace Mathlib.Tactic.SolveByElim

/-- Visualize an `Except` using a checkmark or a cross. -/
def exceptEmoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

/-- Elaborate the context and the list of lemmas -/
def elabContextLemmas (g : MVarId) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr)) :
    MetaM (List Expr) :=
  g.withContext (Elab.Term.TermElabM.run' do pure ((← lemmas.mapM id) ++ (← ctx)))

/-- Configuration structure to control the behaviour of `solve_by_elim`,
by modifying intermediate goals, returning goals as subgoals, and discharging subgoals. -/
structure Config where
  /-- Maximum recursion depth. -/
  maxDepth : Nat := 12
  /-- An arbitrary procedure which can be used to modify the list of goals
    before each attempt to apply a lemma.
    Called as `proc orig goals`, where `orig` are the original goals for `solve_by_elim`,
    and `goals` are the current goals.
    Returning `some l` will replace the active goals with `l` and recurse.
    Returning `none` will proceed to applying lemmas.
    Failure will cause backtracking.
    (defaults to none) -/
  proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none
  /-- If `suspend g`, then we do not attempt to apply any further lemmas,
     but return `g` as a new subgoal. (defaults to `false`) -/
  suspend : MVarId → MetaM Bool := fun _ => pure false
  /-- `discharge g` is called on goals for which no lemmas apply.
    If `none` we return `g` as a new subgoal.
    If `some l`, we replace `g` by `l` in the list of active goals, and recurse.
    If failure, we backtrack. (defaults to failure) -/
  discharge : MVarId → MetaM (Option (List MVarId)) := fun _ => failure

/--
Allow elaboration of `hConfig` arguments to tactics.
-/
declare_config_elab elabConfig Config

namespace Config

/-- Create or modify a `Config` which allows a class of goals to be returned as subgoals. -/
def accept (cfg : Config := {}) (test : MVarId → MetaM Bool) : Config :=
{ cfg with
  discharge := fun g => do
    if (← test g) then
      pure none
    else
      cfg.discharge g }

/-- Create or modify a `Config` which does no backtracking. -/
def noBackTracking (cfg : Config := {}) : Config := cfg.accept fun _ => pure true

/--
Create or modify a `Config` which runs a tactic on the main goal.
If that tactic fails, fall back to the `proc` behaviour of `cfg`.
-/
def mainGoalProc (cfg : Config := {}) (proc : MVarId → MetaM (List MVarId)) : Config :=
{ cfg with
  proc := fun orig goals => match goals with
  | [] => pure none
  | g :: gs => try
      return (← proc g) ++ gs
    catch _ => cfg.proc orig goals }

/-- Create or modify a `Config` which calls `intro` on each goal before applying lemmas. -/
def intros (cfg : Config := {}) : Config :=
  mainGoalProc cfg fun g => do pure [(← g.intro1P).2]

end Config

def solveByElimCore (cfg : Config) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr))
    (orig : List MVarId)
    (n : Nat := cfg.maxDepth) (goals : List MVarId := orig) (acc : List MVarId := []) :
    MetaM (List MVarId) := do
  match n with
  | 0 => throwError "solve_by_elim exceeded the recursion limit"
  | n + 1 => do
  match ← cfg.proc orig goals with
  | some goals' => solveByElimCore cfg lemmas ctx orig n goals' acc
  | none =>
  match goals with
  -- If there are no active goals, return the accumulated goals:
  | [] => return acc
  | g :: gs =>
  -- Discard any goals which have already been assigned.
  if ← g.isAssigned then
    solveByElimCore cfg lemmas ctx orig (n+1) gs acc
  else
  withTraceNode `Meta.Tactic.solveByElim
    -- Note: the `addMessageContextFull` is so that we show the goal using the mvar context before
    -- the `do` block below runs, potentially unifying mvars in the goal.
    (return m!"{exceptEmoji ·} working on: {← addMessageContextFull g}")
    do
      -- Check if we should suspend the search here:
      if (← cfg.suspend g) then
        withTraceNode `Meta.Tactic.solveByElim
          (fun _ => return m!"⏸️ suspending search and returning as subgoal") do
        solveByElimCore cfg lemmas ctx orig (n+1) gs (g :: acc)
      else
      let es ← elabContextLemmas g lemmas ctx
      try
        -- We attempt to find an expression which can be applied,
        -- and for which all resulting sub-goals can be discharged using `solveByElim n`.
        es.firstM fun e => withTraceNode `Meta.Tactic.solveByElim
            (return m!"{exceptEmoji ·} tried to apply: {e}") do
          let gs := (← g.apply e) ++ gs
          solveByElimCore cfg lemmas ctx orig n gs acc
      catch _ =>
        -- No lemmas could be applied:
        match (← cfg.discharge g) with
        | none => (withTraceNode `Meta.Tactic.solveByElim
            (fun _ => return m!"⏭️ deemed acceptable, returning as subgoal") do
          solveByElimCore cfg lemmas ctx orig (n+1) gs (g :: acc))
        | some l => (withTraceNode `Meta.Tactic.solveByElim
            (fun _ => return m!"⏬ discharger generated new subgoals") do
          solveByElimCore cfg lemmas ctx orig n (l ++ gs) acc)
termination_by solveByElimCore lemmas ctx orig n goals acc => (n, goals)

open Lean.Parser.Tactic

/--
`mkAssumptionSet` builds a collection of lemmas for use in
the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congrFun` and
  `congrArg`.
* The flag `noDflt` removes these.
* The argument `hs` is the list of arguments inside the square braces
  and can be used to add lemmas or expressions from the set. (TODO support removal.)

`mkAssumptionSet` returns not a `List expr`, but a `List (TermElabM Expr) × TermElabM (List Expr)`.
There are two separate problems that need to be solved.

### Relevant local hypotheses

`solve_by_elim*` (not implemented yet here) works with multiple goals,
and we need to use separate sets of local hypotheses for each goal.
The second component of the returned value provides these local hypotheses.
(Essentially using `local_context`, along with some filtering to remove hypotheses
that have been explicitly removed via `only` or `[-h]`.)

### Stuck metavariables

Lemmas with implicit arguments would be filled in with metavariables if we created the
`Expr` objects immediately, so instead we return thunks that generate the expressions
on demand. This is the first component, with type `List (TermElabM expr)`.

As an example, we have `def rfl : ∀ {α : Sort u} {a : α}, a = a`, which on elaboration will become
`@rfl ?m_1 ?m_2`.

Because `solve_by_elim` works by repeated application of lemmas against subgoals,
the first time such a lemma is successfully applied,
those metavariables will be unified, and thereafter have fixed values.
This would make it impossible to apply the lemma
a second time with different values of the metavariables.

See https://github.com/leanprover-community/mathlib/issues/2269
-/
-- Make sure that these `TermElabM`s are run inside a suitable `g.withContext`,
-- usually using `elabContextLemmas`.
def mkAssumptionSet (noDflt : Bool) (hs : List (TSyntax `term)) :
    MetaM (List (TermElabM Expr) × TermElabM (List Expr)) := do
  let hs := if noDflt then hs else [← `(rfl), ← `(trivial), ← `(congrFun), ← `(congrArg)] ++ hs
  let hs := hs.map (λ s => Elab.Term.elabTerm s.raw none)
  let locals : TermElabM (List Expr) := if noDflt then pure [] else do
    pure (← getLocalHyps).toList
  return (hs, locals)

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_depth` (currently hard-coded to 6) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ, attr₁, ... attrᵣ]` also applies the named lemmas, as well as
  all lemmas tagged with the specified attributes.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* (not implemented yet) `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions,
   removing the specified ones.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated sub-goals

TODO: there were further optional arguments in mathlib3:
<!--
- `discharger`: a subsidiary tactic to try at each step when no lemmas apply
  (e.g. `cc` may be helpful).
- `preApply`: a subsidiary tactic to run at each step before applying lemmas (e.g. `intros`).
- `accept`: a subsidiary tactic `List Expr → Tactic` that at each step,
  before any lemmas are applied, is passed the original proof terms
  as reported by `getGoals` when `solve_by_elim` started
  (but which may by now have been partially solved by previous `apply` steps).
  If the `accept` tactic fails,
  `solve_by_elim` will abort searching the current branch and backtrack.
  This may be used to filter results, either at every step of the search,
  or filtering complete results
  (by testing for the absence of metavariables, and then the filtering condition).
-->
-/
syntax (name := solveByElim) "solve_by_elim" "*"? (config)? (&" only")? (simpArgs)? : tactic

elab_rules : tactic |
    `(tactic| solve_by_elim $[*%$s]? $[$cfg]? $[only%$o]? $[[$[$t:term],*]]?) => do
  let es := (t.getD #[]).toList
  let ⟨lemmas, ctx⟩ ← mkAssumptionSet o.isSome es
  let goals ← if s.isSome then
    getGoals
  else
    pure [← getMainGoal]
  let cfg ← elabConfig (mkOptionalNode cfg)
  let [] ← solveByElimCore cfg lemmas ctx goals |
    throwError "solve_by_elim unexpectedly returned subgoals"
  pure ()

/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

[todo] not yet implemented:
If this fails, `apply_assumption` will call `symmetry` and try again.

[todo] not yet implemented:
If this also fails, `apply_assumption` will call `exfalso` and try again,
so that if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

[todo] not yet implemented:
Optional arguments:
- `lemmas`: a list of expressions to apply, instead of the local constants
- `tac`: a tactic to run on each subgoal after applying an assumption; if
  this tactic fails, the corresponding assumption will be rejected and
  the next one will be attempted.
-/
syntax (name := applyAssumption) "apply_assumption" : tactic

elab_rules : tactic | `(tactic| apply_assumption) => do
  let ctx := (← getLocalHyps).toList
  let lemmas := [← `(rfl), ← `(trivial), ← `(congrArg)].map (λ s => Elab.Term.elabTerm s.raw none)
  (← elabContextLemmas (← getMainGoal) lemmas (pure ctx)).firstM
    fun e => (liftMetaTactic (Lean.MVarId.apply · e))
