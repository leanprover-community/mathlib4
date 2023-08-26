/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, David Renshaw
-/
import Mathlib.Tactic.Backtracking
import Lean.Meta.Tactic.Apply
import Mathlib.Lean.LocalContext
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.LabelAttr
import Mathlib.Control.Basic

/-!
# `solve_by_elim`, `apply_rules`, and `apply_assumption`.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

initialize registerTraceClass `Meta.Tactic.solveByElim

namespace Mathlib.Tactic.SolveByElim

/--
`applyTactics lemmas goal` will return a list of tactics,
corresponding to applying each one of the lemmas to the goal `goal`.

Providing this to the `backtracking` tactic,
we can perform backtracking search based on applying a list of lemmas.

``applyTactics (trace := `name)`` will construct trace nodes for ``name` indicating which
calls to `apply` succeeded or failed.
-/
def applyTactics (cfg : ApplyConfig := {}) (transparency : TransparencyMode := .default)
    (lemmas : List Expr) :
    MVarId → MetaM (List (MetaM (List MVarId))) :=
  fun g => pure <|
    lemmas.map fun e =>
      withTraceNode `Meta.Tactic.solveByElim (return m!"{·.emoji} trying to apply: {e}") do
        let goals ← withTransparency transparency (g.apply e cfg)
        -- When we call `apply` interactively, `Lean.Elab.Tactic.evalApplyLikeTactic`
        -- deals with closing new typeclass goals by calling
        -- `Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing`.
        -- It seems we can't reuse that machinery down here in `MetaM`,
        -- so we just settle for trying to close each subgoal using `inferInstance`.
        goals.filterM fun g => try g.inferInstance; pure false catch _ => pure true

/--
`applyFirst lemmas goal` applies the first of the `lemmas`
which can be successfully applied to `goal`, and fails if none apply.

We use this in `apply_rules` and `apply_assumption` where backtracking is not needed.
-/
def applyFirst (cfg : ApplyConfig := {}) (transparency : TransparencyMode := .default)
    (lemmas : List Expr) : MVarId → MetaM (List MVarId) :=
  fun g => do
    (← applyTactics cfg transparency lemmas g).firstM (fun t => t)

/--
Configuration structure to control the behaviour of `solve_by_elim`:
* transparency mode for calls to `apply`
* whether to use `symm` on hypotheses and `exfalso` on the goal as needed,
* see also `BacktrackConfig` for hooks allowing flow control.
-/
structure Config extends BacktrackConfig, ApplyConfig where
  /-- Transparency mode for calls to `apply`. -/
  transparency : TransparencyMode := .default
  /-- Also use symmetric versions (via `@[symm]`) of local hypotheses. -/
  symm : Bool := true
  /-- Try proving the goal via `exfalso` if `solve_by_elim` otherwise fails.
  This is only used when operating on a single goal. -/
  exfalso : Bool := true
  backtracking : Bool := true

instance : Coe Config BacktrackConfig := ⟨Config.toBacktrackConfig⟩

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

/-!
These functions could be lifted up to `BacktrackConfig`,
but we'd still need to keep copies here.
-/
namespace Config

/-- Create or modify a `Config` which allows a class of goals to be returned as subgoals. -/
def accept (cfg : Config := {}) (test : MVarId → MetaM Bool) : Config :=
  { cfg with
    discharge := fun g => do
      if (← test g) then
        pure none
      else
        cfg.discharge g }

/--
Create or modify a `Config` which runs a tactic on the main goal.
If that tactic fails, fall back to the `proc` behaviour of `cfg`.
-/
def mainGoalProc (cfg : Config := {}) (proc : MVarId → MetaM (List MVarId)) : Config :=
  { cfg with
    proc := fun orig goals => match goals with
    | [] => cfg.proc orig []
    | g :: gs => try
        return (← proc g) ++ gs
      catch _ => cfg.proc orig goals }

/-- Create or modify a `Config` which calls `intro` on each goal before applying lemmas. -/
-- Because `SolveByElim` works on each goal in sequence, even though
-- `mainGoalProc` only applies this operation on the main goal,
-- it is applied to every goal before lemmas are applied.
def intros (cfg : Config := {}) : Config :=
  cfg.mainGoalProc fun g => do pure [(← g.intro1P).2]

/-- Attempt typeclass inference on each goal, before applying lemmas. -/
-- Because `SolveByElim` works on each goal in sequence, even though
-- `mainGoalProc` only applies this operation on the main goal,
-- it is applied to every goal before lemmas are applied.
def synthInstance (cfg : Config := {}) : Config :=
  cfg.mainGoalProc fun g => do g.synthInstance; pure []

/-- Add a discharging tactic, falling back to the original discharging tactic if it fails.
Return `none` to return the goal as a new subgoal, or `some goals` to replace it. -/
def withDischarge (cfg : Config := {}) (discharge : MVarId → MetaM (Option (List MVarId))) :
    Config :=
  { cfg with
    discharge := fun g => try discharge g
      catch _ => cfg.discharge g }

/-- Create or modify a `Config` which calls `intro` on any goal for which no lemma applies. -/
def introsAfter (cfg : Config := {}) : Config :=
  cfg.withDischarge fun g => do pure [(← g.intro1P).2]

/-- Create or modify a `Config` which
calls `synthInstance` on any goal for which no lemma applies. -/
def synthInstanceAfter (cfg : Config := {}) : Config :=
  cfg.withDischarge fun g => do g.synthInstance; pure (some [])

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
  g.withContext (Elab.Term.TermElabM.run' do pure ((← ctx) ++ (← lemmas.mapM id)))

/-- Returns the list of tactics corresponding to applying the available lemmas to the goal. -/
def applyLemmas (cfg : Config) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr))
    (g : MVarId) : MetaM (List (MetaM (List MVarId))) := do
let es ← elabContextLemmas g lemmas ctx
applyTactics cfg.toApplyConfig cfg.transparency es g

/-- Applies the first possible lemma to the goal. -/
def applyFirstLemma (cfg : Config) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr))
    (g : MVarId) : MetaM (List MVarId) := do
let es ← elabContextLemmas g lemmas ctx
applyFirst cfg.toApplyConfig cfg.transparency es g

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

  try
    run goals
  catch e => do
    -- Implementation note: as with `cfg.symm`, this is different from the mathlib3 approach,
    -- for (not as severe) performance reasons.
    match goals, cfg.exfalso with
    | [g], true =>
      withTraceNode `Meta.Tactic.solveByElim
          (fun _ => return m!"⏮️ starting over using `exfalso`") do
        run [← g.exfalso]
    | _, _ => throw e
where
  -- Run either backtracking search, or repeated application, on the list of goals.
  run : List MVarId → MetaM (List MVarId) := if cfg.backtracking then
    backtrack cfg `Meta.Tactic.solveByElim (applyLemmas cfg lemmas ctx)
  else
    repeat1' (maxIters := cfg.maxDepth) (applyFirstLemma cfg lemmas ctx)

/--
A `MetaM` analogue of the `apply_rules` user tactic.

We pass the lemmas as `TermElabM Expr` rather than just `Expr`,
so they can be generated fresh for each application, to avoid stuck metavariables.

By default it uses all local hypotheses, but you can disable this with `only := true`.
If you need to remove particular local hypotheses, call `solveByElim` directly.
-/
def _root_.Lean.MVarId.applyRules (cfg : Config) (lemmas : List (TermElabM Expr))
    (only : Bool := false) (g : MVarId) : MetaM (List MVarId) := do
  let ctx : TermElabM (List Expr) := if only then pure [] else do pure (← getLocalHyps).toList
  solveByElim { cfg with backtracking := false } lemmas ctx [g]

open Lean.Parser.Tactic
open Mathlib.Tactic.LabelAttr

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
  let labelledLemmas := (← use.mapM (labelled ·.raw.getId)).flatten.toList
    |>.map (liftM <| mkConstWithFreshMVarLevels ·)
  let lemmas := if noDefaults then
    add.map elab' ++ labelledLemmas
  else
    add.map elab' ++ labelledLemmas ++ defaults

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
syntax args := " [" SolveByElim.arg,* "]"
/-- Syntax for using all lemmas labelled with an attribute in `solve_by_elim`. -/
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
    args.filterMap fun o => o.bind Sum.getLeft?,
    args.filterMap fun o => o.bind Sum.getRight?)

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
* `solve_by_elim using [a₁, ...]` uses all lemmas which have been labelled
  with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

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

See also the doc-comment for `Mathlib.Tactic.BacktrackConfig` for the options
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
You can use `apply_assumption using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

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
    backtracking := false
    maxDepth := 1 }
  replaceMainGoal (← solveByElim.processSyntax cfg o.isSome star add remove use [← getMainGoal])

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.
You can use `apply_rules [-h]` to omit a local hypothesis.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

You can use `apply_rules using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

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
    `(tactic| apply_rules $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
  let (star, add, remove) := parseArgs t
  let use := parseUsing use
  let cfg ← elabApplyRulesConfig (mkOptionalNode cfg)
  let cfg := { cfg with
    backtracking := false }
  liftMetaTactic fun g => solveByElim.processSyntax cfg o.isSome star add remove use [g]
