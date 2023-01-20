/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, David Renshaw
-/
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.Core
import Mathlib.Lean.LocalContext
import Mathlib.Tactic.Relation.Symm
import Mathlib.Control.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Tactic.TagAttr

/-!
A work-in-progress replacement for Lean3's `solve_by_elim` tactic.
We'll gradually bring it up to feature parity.
-/

open Lean Meta Elab Tactic

/-- Visualize an `Except` using a checkmark or a cross. -/
def exceptEmoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

namespace Lean.MVarId

/--
`applyFirst lemmas cont goal` will try to apply one of the `lemmas` to the goal `goal`,
and then call `cont` on the resulting `List MVarId` of subgoals.

It returns the result from `cont` for the first such lemma for which
both the `apply` and the call to `cont` succeed.

``applyFirst (trace := `name)`` will construct trace nodes for ``name` indicating which
calls to `apply` succeeded or failed.
-/
-- Because the operation of this function via a continuation is fairly specific to `solve_by_elim`,
-- we keep it here rather than moving it into `Mathlib/Lean/`.
def applyFirst (cfg : ApplyConfig := {}) (transparency : TransparencyMode := .default)
    (trace : Name := .anonymous) (lemmas : List Expr) (cont : List MVarId → MetaM α)
    (g : MVarId) : MetaM α :=
  lemmas.firstM fun e =>
    withTraceNode trace (return m!"{exceptEmoji ·} trying to apply: {e}") do
      let goals ← withTransparency transparency (g.apply e cfg)
      -- When we call `apply` interactively, `Lean.Elab.Tactic.evalApplyLikeTactic`
      -- deals with closing new typeclass goals by calling
      -- `Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing`.
      -- It seems we can't reuse that machinery down here in `MetaM`,
      -- so we just settle for trying to close each subgoal using `inferInstance`.
      cont (← goals.filterM fun g => try g.inferInstance; pure false catch _ => pure true)

end Lean.MVarId

initialize registerTraceClass `Meta.Tactic.solveByElim

namespace Mathlib.Tactic.SolveByElim

/--
Configuration structure to control the behaviour of `solve_by_elim`:
* control the maximum depth and behaviour (fail or return subgoals) at the maximum depth,
* whether to use `symm` on hypotheses and `exfalso` on the goal as needed,
* and hooks allowing
  * modifying intermediate goals,
  * returning goals as subgoals, and
  * discharging subgoals.
-/
structure Config extends ApplyConfig where
  /-- Maximum recursion depth. -/
  maxDepth : Nat := 6
  /-- If `failAtDepth`, then `solve_by_elim` will fail (and backtrack) upon reaching the max depth.
  Otherwise, upon reaching the max depth, all remaining goals will be returned.
  (defaults to `true`) -/
  failAtMaxDepth : Bool := true
  /-- Transparency mode for calls to `apply`. -/
  transparency : TransparencyMode := .default
  /-- Also use symmetric versions (via `@[symm]`) of local hypotheses. -/
  symm : Bool := true
  /-- Try proving the goal via `exfalso` if `solve_by_elim` otherwise fails.
  This is only used when operating on a single goal. -/
  exfalso : Bool := true
  /-- An arbitrary procedure which can be used to modify the list of goals
  before each attempt to apply a lemma.
  Called as `proc goals curr`, where `goals` are the original goals for `solve_by_elim`,
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

/-- The default `maxDepth` for `apply_rules` is higher. -/
structure ApplyRulesConfig extends Config where
  maxDepth := 50

/--
Allow elaboration of `Config` arguments to tactics.
-/
declare_config_elab elabConfig Config

/--
Allow elaboration of `ApplyRulesConfig` arguments to tactics.
-/
declare_config_elab elabApplyRulesConfig ApplyRulesConfig

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

/--
Create or modify a `Config` which rejects branches for which `test`,
applied to the instantiations of the original goals, fails or returns `false`.
-/
def testPartialSolutions (cfg : Config := {}) (test : List Expr → MetaM Bool) : Config :=
{ cfg with
  proc := fun orig goals => do
    let .true ← test (← orig.mapM fun m => m.withContext do instantiateMVars (.mvar m)) | failure
    cfg.proc orig goals }

/--
Create or modify a `Config` which rejects complete solutions for which `test`,
applied to the instantiations of the original goals, fails or returns `false`.
-/
def testSolutions (cfg : Config := {}) (test : List Expr → MetaM Bool) : Config :=
  cfg.testPartialSolutions fun sols => do
    if sols.any Expr.hasMVar then
      pure true
    else
      test sols

/--
Create or modify a `Config` which only accept solutions
for which every expression in `use` appears as a subexpression.
-/
def requireUsingAll (cfg : Config := {}) (use : List Expr) : Config :=
  cfg.testSolutions fun sols => do
    pure <| use.all fun e => sols.any fun s => e.occurs s

end Config

/--
Elaborate a list of lemmas and local context.
See `mkAssumptionSet` for an explanation of why this is needed.
-/
def elabContextLemmas (g : MVarId) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr)) :
    MetaM (List Expr) := do
  g.withContext (Elab.Term.TermElabM.run' do pure ((← lemmas.mapM id) ++ (← ctx)))

/--
Solve a collection of goals by repeatedly applying lemmas, backtracking as necessary.

Arguments:
* `cfg : Config` additional configuration options
  (options for `apply`, maximum depth, and custom flow control)
* `lemmas : List (TermElabM Expr)` lemmas to apply.
  These are thunks in `TermElabM` to avoid stuck metavariables.
* `ctx : TermElabM (List Expr)` monadic function returning the local hypotheses to use.
* `goals : List MVarId` the initial list of goals for `solveByElim`

Returns a list of suspended goals, if it succeeded on all other subgoals.
By default `cfg.suspend` is `false,` `cfg.discharge` fails, and `cfg.failAtMaxDepth` is `true`,
and so the returned list is always empty.
Custom wrappers (e.g. `apply_assumption` and `apply_rules`) may modify this behaviour.
-/
def solveByElim (cfg : Config) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr))
    (goals : List MVarId) : MetaM (List MVarId) := do
  -- We handle `cfg.symm` by saturating hypotheses of all goals using `symm`.
  -- Implementation note:
  -- (We used to apply `symm` all throughout the `solve_by_elim` stage.)
  -- I initially reproduced the mathlib3 approach, but it had bad performance so switched to this.
  let goals ← if cfg.symm then
    goals.mapM fun g => g.symmSaturate
  else
    pure goals

  -- Implementation note: as with `cfg.symm`, this is different from the mathlib3 approach,
  -- for (not as bad) performance reasons.
  match cfg.exfalso, goals with
    | true, [g] => try
        run cfg.maxDepth [g] []
      catch _ => do
        withTraceNode `Meta.Tactic.solveByElim
            (fun _ => return m!"⏮️ starting over using `exfalso`") do
          let g ← g.exfalso
          run cfg.maxDepth [g] []
    | _, _ =>
      run cfg.maxDepth goals []
  where
  /--
  * `n : Nat` steps remaining.
  * `curr : List MVarId` the current list of unsolved goals.
  * `acc : List MVarId` a list of "suspended" goals, which will be returned as subgoals.
  -/
  run (n : Nat) (curr acc : List MVarId) : MetaM (List MVarId) := do
  match n with
  | 0 => do
    -- We're out of fuel.
    if cfg.failAtMaxDepth then
      throwError "solve_by_elim exceeded the recursion limit"
    else
      -- Before returning the goals, we run `cfg.proc` one last time.
      let curr := acc.reverse ++ curr
      return (← cfg.proc goals curr).getD curr
  | n + 1 => do
  -- First, run `cfg.proc`, to see if it wants to modify the goals.
  match ← cfg.proc goals curr with
  | some curr' => run n curr' acc
  | none =>
  match curr with
  -- If there are no active goals, return the accumulated goals.
  | [] => return acc.reverse
  | g :: gs =>
  -- Discard any goals which have already been assigned.
  if ← g.isAssigned then
    run (n+1) gs acc
  else
  withTraceNode `Meta.Tactic.solveByElim
    -- Note: the `addMessageContextFull` ensures we show the goal using the mvar context before
    -- the `do` block below runs, potentially unifying mvars in the goal.
    (return m!"{exceptEmoji ·} working on: {← addMessageContextFull g}")
    do
      -- Check if we should suspend the search here:
      if (← cfg.suspend g) then
        withTraceNode `Meta.Tactic.solveByElim
          (fun _ => return m!"⏸️ suspending search and returning as subgoal") do
        run (n+1) gs (g :: acc)
      else
        let es ← elabContextLemmas g lemmas ctx
        try
          -- We attempt to find an expression which can be applied,
          -- and for which all resulting sub-goals can be discharged using `solveByElim n`.
          g.applyFirst cfg.toApplyConfig cfg.transparency `Meta.Tactic.solveByElim es fun res =>
            run n (res ++ gs) acc
        catch _ =>
          -- No lemmas could be applied:
          match (← cfg.discharge g) with
          | none => (withTraceNode `Meta.Tactic.solveByElim
              (fun _ => return m!"⏭️ deemed acceptable, returning as subgoal") do
            run (n+1) gs (g :: acc))
          | some l => (withTraceNode `Meta.Tactic.solveByElim
              (fun _ => return m!"⏬ discharger generated new subgoals") do
            run n (l ++ gs) acc)
  termination_by run n curr acc => (n, curr)

/--
A `MetaM` analogue of the `apply_rules` user tactic.

Since `apply_rules` does not backtrack, we don't need to worry about stuck metavariables
and can pass the lemmas as a `List Expr`.

By default it uses all local hypotheses, but you can disable this with `only := true`.
If you need to remove particular local hypotheses, call `solveByElim` directly.
-/
def _root_.Lean.MVarId.applyRules (cfg : Config) (lemmas : List Expr) (only : Bool := false)
    (g : MVarId) : MetaM (List MVarId) := do
  let lemmas := lemmas.map pure
  let ctx : TermElabM (List Expr) := if only then pure [] else do pure (← getLocalHyps).toList
  solveByElim { cfg.noBackTracking with failAtMaxDepth := false } lemmas ctx [g]

open Lean.Parser.Tactic
open Mathlib.Tactic.TagAttr

/--
`mkAssumptionSet` builds a collection of lemmas for use in
the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congrFun`
  and `congrArg`.
* The flag `noDefaults` removes these.
* The flag `star` includes all local hypotheses, but not `rfl`, `trivial`, `congrFun`,
  or `congrArg`. (It doesn't make sense to use `star` without `noDefaults`.)
* The argument `add` is the list of terms inside the square brackets that did not have `-`
  and can be used to add expressions or local hypotheses
* The argument `remove` is the list of terms inside the square brackets that had a `-`,
  and can be used to remove local hypotheses.
  (It doesn't make sense to remove expressions which are not local hypotheses,
  to remove local hypotheses unless `!noDefaults || star`,
  and it does not make sense to use `star` unless you remove at least one local hypothesis.)

`mkAssumptionSet` returns not a `List expr`, but a `List (TermElabM Expr) × TermElabM (List Expr)`.
There are two separate problems that need to be solved.

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

### Relevant local hypotheses

`solve_by_elim*` works with multiple goals,
and we need to use separate sets of local hypotheses for each goal.
The second component of the returned value provides these local hypotheses.
(Essentially using `local_context`, along with some filtering to remove hypotheses
that have been explicitly removed via `only` or `[-h]`.)

-/
-- These `TermElabM`s must be run inside a suitable `g.withContext`,
-- usually using `elabContextLemmas`.
def mkAssumptionSet (noDefaults star : Bool) (add remove : List Term) (use : Array Ident) :
    MetaM (List (TermElabM Expr) × TermElabM (List Expr)) := do
  if star && !noDefaults then
    throwError "It doesn't make sense to use `*` without `only`."

  let defaults : List (TermElabM Expr) :=
    [← `(rfl), ← `(trivial), ← `(congrFun), ← `(congrArg)].map elab'
  let taggedLemmas := (← use.mapM (tagged ·.raw.getId)).flatten.toList
    |>.map (liftM <| mkConstWithFreshMVarLevels ·)
  let lemmas := if noDefaults then
    add.map elab' ++ taggedLemmas
  else
    add.map elab' ++ taggedLemmas ++ defaults

  if !remove.isEmpty && noDefaults && !star then
    throwError "It doesn't make sense to remove local hypotheses when using `only` without `*`."
  let locals : TermElabM (List Expr) := if noDefaults && !star then do
    pure []
  else do
    pure <| (← getLocalHyps).toList.removeAll (← remove.mapM elab')

  return (lemmas, locals)
  where
  /-- Run `elabTerm`. -/
  elab' (t : Term) : TermElabM Expr := Elab.Term.elabTerm t.raw none

/-- Syntax for omitting a local hypothesis in `solve_by_elim`. -/
syntax erase := "-" term:max
/-- Syntax for including all local hypotheses in `solve_by_elim`. -/
syntax star := "*"
/-- Syntax for adding or removing a term, or `*`, in `solve_by_elim`. -/
syntax arg := star <|> erase <|> term
/-- Syntax for adding and removing terms in `solve_by_elim`. -/
syntax args := " [" SolveByElim.arg,* "] "
/-- Syntax for using all lemmas tagged with an attribute in `solve_by_elim`. -/
syntax using_ := " using " ident,*

open Syntax

/--
Parse the lemma argument of a call to `solve_by_elim`.
The first component should be true if `*` appears at least once.
The second component should contain each term `t`in the arguments.
The third component should contain `t` for each `-t` in the arguments.
-/
def parseArgs (s : Option (TSyntax ``args)) :
    Bool × List Term × List Term :=
  let args : Array (TSyntax ``arg) := match s with
  | some s => match s with
    | `(args| [$args,*]) => args.getElems
    | _ => #[]
  | none => #[]
  let args : Array (Option (Term ⊕ Term)) := args.map fun t => match t with
    | `(arg| $_:star) => none
    | `(arg| - $t:term) => some (Sum.inr t)
    | `(arg| $t:term) => some (Sum.inl t)
    | _ => panic! "Unreachable parse of solve_by_elim arguments."
  let args := args.toList
  (args.contains none,
    args.filterMap fun o => o.bind Sum.getLeft,
    args.filterMap fun o => o.bind Sum.getRight)

/-- Parse the `using ...` argument for `solve_by_elim`. -/
def parseUsing (s : Option (TSyntax ``using_)) : Array Ident :=
  match s with
  | some s => match s with
    | `(using_ | using $ids,*) => ids.getElems
    | _ => #[]
  | none => #[]

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `maxDepth` (defaults to 6) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs backtracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the given expressions.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* `solve_by_elim [-h₁, ... -hₙ]` removes the given local hypotheses.
* `solve_by_elim using [a₁, ...]` uses all lemmas which have been tagged
  with the attributes `aᵢ` (these attributes must be created using `register_tag_attr`).

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.
(Adding or removing local hypotheses may not be well-behaved when starting with multiple goals.)

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated subgoals
- `symm`: adds all hypotheses derived by `symm` (defaults to `true`).
- `exfalso`: allow calling `exfalso` and trying again if `solve_by_elim` fails
  (defaults to `true`).
- `transparency`: change the transparency mode when calling `apply`. Defaults to `.default`,
  but it is often useful to change to `.reducible`,
  so semireducible definitions will not be unfolded when trying to apply a lemma.

See also the doc-comment for `Mathlib.Tactic.SolveByElim.Config` for the options
`proc`, `suspend`, and `discharge` which allow further customization of `solve_by_elim`.
Both `apply_assumption` and `apply_rules` are implemented via these hooks.
-/
syntax (name := solveByElimSyntax)
  "solve_by_elim" "*"? (config)? (&" only")? (args)? (using_)? : tactic

/-- Wrapper for `solveByElim` that processes a list of `Term`s
that specify the lemmas to use. -/
def solveByElim.processSyntax (cfg : Config := {}) (only star : Bool) (add remove : List Term)
    (use : Array Ident) (goals : List MVarId) : MetaM (List MVarId) := do
  if !remove.isEmpty && goals.length > 1 then
    throwError "Removing local hypotheses is not supported when operating on multiple goals."
  let ⟨lemmas, ctx⟩ ← mkAssumptionSet only star add remove use
  solveByElim cfg lemmas ctx goals

elab_rules : tactic |
    `(tactic| solve_by_elim $[*%$s]? $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
  let (star, add, remove) := parseArgs t
  let use := parseUsing use
  let goals ← if s.isSome then
    getGoals
  else
    pure [← getMainGoal]
  let cfg ← elabConfig (mkOptionalNode cfg)
  let [] ← solveByElim.processSyntax cfg o.isSome star add remove use goals |
    throwError "solve_by_elim unexpectedly returned subgoals"
  pure ()

/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

You can specify additional rules to apply using `apply_assumption [...]`.
By default `apply_assumption` will also try `rfl`, `trivial`, `congrFun`, and `congrArg`.
If you don't want these, or don't want to use all hypotheses, use `apply_assumption only [...]`.
You can use `apply_assumption [-h]` to omit a local hypothesis.
You can use `apply_assumption using [a₁, ...]` to use all lemmas which have been tagged
with the attributes `aᵢ` (these attributes must be created using `register_tag_attr`).

`apply_assumption` will use consequences of local hypotheses obtained via `symm`.

If `apply_assumption` fails, it will call `exfalso` and try again.
Thus if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

You can pass a further configuration via the syntax `apply_rules (config := {...}) lemmas`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).
-/
syntax (name := applyAssumptionSyntax)
  "apply_assumption" (config)? (&" only")? (args)? (using_)? : tactic

elab_rules : tactic |
    `(tactic| apply_assumption $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
  let (star, add, remove) := parseArgs t
  let use := parseUsing use
  let cfg ← elabConfig (mkOptionalNode cfg)
  let cfg := { cfg with
    maxDepth := 1
    failAtMaxDepth := false }
  replaceMainGoal (← solveByElim.processSyntax cfg o.isSome star add remove use [← getMainGoal])

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.
You can use `apply_rules [-h]` to omit a local hypothesis.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

You can use `apply_rules using [a₁, ...]` to use all lemmas which have been tagged
with the attributes `aᵢ` (these attributes must be created using `register_tag_attr`).

You can pass a further configuration via the syntax `apply_rules (config := {...})`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

`apply_rules` will try calling `symm` on hypotheses and `exfalso` on the goal as needed.
This can be disabled with `apply_rules (config := {symm := false, exfalso := false})`.

You can bound the iteration depth using the syntax `apply_rules (config := {maxDepth := n})`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.
-/
syntax (name := applyRulesSyntax) "apply_rules" (config)? (&" only")? (args)? (using_)? : tactic

-- See also `Lean.MVarId.applyRules` for a `MetaM` level analogue of this tactic.
elab_rules : tactic |
    `(tactic| apply_rules $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?)  => do
  let (star, add, remove) := parseArgs t
  let use := parseUsing use
  let cfg ← elabApplyRulesConfig (mkOptionalNode cfg)
  let cfg := { cfg.noBackTracking with
    failAtMaxDepth := false }
  liftMetaTactic fun g => solveByElim.processSyntax cfg o.isSome star add remove use [g]
