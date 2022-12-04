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

/-!
A work-in-progress replacement for Lean3's `solve_by_elim` tactic.
We'll gradually bring it up to feature parity.
-/

open Lean Meta Elab Tactic

/-- Visualize an `Except` using a checkmark or a cross. -/
def exceptEmoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

/-- If a `Expr` has form `.fvar n`, then returns `some n`, otherwise `none`. -/
def Lean.Expr.fvarId? : Expr → Option FVarId
  | .fvar n => n
  | _ => none

namespace Lean.MVarId

/--
`applyFirst lemmas cont goal` will try to apply one of the `lemmas` to the goal `goal`,
and then call `cont` on the resulting `List MVarId` of subgoals.

It returns the result from `cont` for the first such lemma for which
both the `apply` and the call to `cont` succeed.

``applyFirst (trace := `name)`` will construct trace nodes for ``name` indicating which
calls to `apply` succeeded or failed.
-/
def applyFirst (cfg : ApplyConfig := {}) (trace : Name := .anonymous) (lemmas : List Expr)
    (cont : List MVarId → MetaM α) (g : MVarId) : MetaM α :=
  lemmas.firstM fun e =>
    withTraceNode trace (return m!"{exceptEmoji ·} tried to apply: {e}") do
      cont (← g.apply e cfg)

end Lean.MVarId

initialize registerTraceClass `Meta.Tactic.solveByElim

namespace Mathlib.Tactic.SolveByElim

/-- Elaborate the context and the list of lemmas -/
def elabContextLemmas (g : MVarId) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr)) :
    MetaM (List Expr) :=
  g.withContext (Elab.Term.TermElabM.run' do pure ((← lemmas.mapM id) ++ (← ctx)))

/-- Configuration structure to control the behaviour of `solve_by_elim`,
by modifying intermediate goals, returning goals as subgoals, and discharging subgoals. -/
structure Config extends ApplyConfig where
  /-- Maximum recursion depth. -/
  maxDepth : Nat := 12
  /-- If `failAtDepth`, then `solve_by_elim` will fail (and backtrack) upon reaching the max depth.
  Otherwise, upon reaching the max depth, all remaining goals will be returned.
  (defaults to `true`) -/
  failAtMaxDepth : Bool := true
  /-- Also use symmetric versions (via `@[symm]`) of local hypotheses. -/
  -- At least for now, this does not operate on lemmas provided explicitly.
  symm : Bool := true
  /-- Try proving the goal via `exfalso` if `solve_by_elim` otherwise fails. -/
  -- This is only tried when operating on a single goal.
  exfalso : Bool := true
  /-- An arbitrary procedure which can be used to modify the list of goals
    before each attempt to apply a lemma.
    Called as `proc orig goals`, where `orig` are the original goals for `solve_by_elim`,
    and `goals` are the current goals.
    Returning `some l` will replace the active goals with `l` and recurse.
    Returning `none` will proceed to applying lemmas.
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

/--
Solve a collection of goals by repeatedly applying lemmas, backtracking as necessary.

Arguments:
* `cfg : Config` additional configuration options (options for `apply` and custom flow control)
* `lemmas : List (TermElabM Expr)` lemmas to apply.
  These are thunks in `TermElabM` to avoid stuck metavariables.
* `ctx : TermElabM (List Expr)` monadic function returning the local hypotheses to use.
* `goals : List MVarId` the inital list of goals for `solveByElim`

Returns a list of suspended goals, if it succeeded on all other subgoals.
By default `cfg.suspend` is `false,` `cfg.discharge` fails, and `cfg.failAtMaxDepth` is `true`,
and so the returned list is always empty.
Custom wrappers (e.g. `apply_assumption` and `apply_rules`) may modify this behaviour.
-/
def solveByElim (cfg : Config) (lemmas : List (TermElabM Expr)) (ctx : TermElabM (List Expr))
    (goals : List MVarId) : MetaM (List MVarId) := do
  -- We handle `cfg.symm` by saturating hypotheses of all goals using `symm`.
  let goals ← if cfg.symm then
    goals.mapM fun g => g.symmSaturate
  else
    pure goals

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
      return acc.reverse ++ curr
  | n + 1 => do
  -- First, run `cfg.proc`, to see if it wants to modify the goals.
  match ← cfg.proc goals curr with
  | some curr' => run n curr' acc
  | none =>
  match curr with
  -- If there are no active goals, return the accumulated goals:
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
        g.applyFirst cfg.toApplyConfig `Meta.Tactic.solveByElim es fun res =>
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

open Lean.Parser.Tactic

/-- Separate a list of terms into those that elaborate to local hypotheses
and those that do not. -/
def partitionLocalHyps (l : List Term) : MetaM (List Term × List Term) := do
  l.partitionM fun t => Elab.Term.TermElabM.run' do
    pure (← Elab.Term.elabTerm t.raw none).isFVar
  -- let s ← l.mapM fun t => Elab.Term.TermElabM.run' do
  --     let e ← Elab.Term.elabTerm t.raw none
  --     match e.fvarId? with
  --     | some h => pure <| Sum.inl h
  --     | none => pure <| Sum.inr t
  -- pure <| s.partitionMap id -- TODO I guess we need `List.partitionMapM`.

/--
`mkAssumptionSet` builds a collection of lemmas for use in
the backtracking search in `solve_by_elim`.

* By default, it includes all local hypotheses, along with `rfl`, `trivial`, `congrFun` and
  `congrArg`.
* The flag `noDefaults` removes these.
* The argument `hs` is the list of arguments inside the square braces
  and can be used to add lemmas or expressions from the set. (TODO support removal.)

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
def mkAssumptionSet (noDefaults star : Bool) (add remove : List Term) :
    MetaM (List (TermElabM Expr) × TermElabM (List Expr)) := do
  if star && !noDefaults then
    throwError "It does make sense to use `*` without `only`."

  let (addLocal, addExpr) ← partitionLocalHyps add
  let (removeLocal, removeExpr) ← partitionLocalHyps remove

  if !removeExpr.isEmpty then
    throwError "It doesn't make sense to remove expressions which are not local hypotheses."
  let defaults : List Term := [← `(rfl), ← `(trivial), ← `(congrFun), ← `(congrArg)]
  let hyps := (if noDefaults then addExpr else defaults ++ addExpr).map elab'

  if !removeLocal.isEmpty && noDefaults && !star then
    throwError "It doesn't make sense to remove local hypotheses when using `only` without `*`."
  -- TODO Consider extracting `FVarId`s to avoid re-elaborating here.
  let locals : TermElabM (List Expr) := if noDefaults && !star then
    (addLocal.removeAll removeLocal).mapM elab'
  else do
    if !addLocal.isEmpty then
      throwError "It doesn't make sense to add local hypotheses unless you use `only` without `*`."
    pure <| (← getLocalHyps).toList.removeAll (← removeLocal.mapM elab')

  return (hyps, locals)
  where
  /-- Run `elabTerm`. -/
  elab' (t : Term) : TermElabM Expr := Elab.Term.elabTerm t.raw none

-- def mkAssumptionSet (noDflt : Bool) (hs : List (TSyntax `term)) :
--     MetaM (List (TermElabM Expr) × TermElabM (List Expr)) := do
--   let hs := if noDflt then hs else [← `(rfl), ← `(trivial), ← `(congrFun), ← `(congrArg)] ++ hs
--   let hs := hs.map (λ s => Elab.Term.elabTerm s.raw none)
--   let locals : TermElabM (List Expr) := if noDflt then pure [] else do
--     pure (← getLocalHyps).toList
--   return (hs, locals)

syntax erase := "-" term:max
syntax star := "*"
syntax arg := star <|> erase <|> term
syntax args := " [" SolveByElim.arg,* "] "

open Syntax

instance Sum.beq [BEq α] [BEq β] : BEq (α ⊕ β) where
  beq x y := match x, y with
  | .inl x, .inl y => x == y
  | .inr x, .inr y => x == y
  | _, _ => false

/--
Parse the lemma argument of a call to `solve_by_elim`.
The first component should be true if `*` appears at least once.
The second component should contain each term `t`in the arguments.
The third component should contain `t` for each `-t` in the arguments.
-/
def parseArgs (s : Option (TSyntax ``args)) :
    Bool × List (TSyntax `term) × List (TSyntax `term) :=
  let args : Array (TSyntax ``arg) := match s with
  | some s => match s with
    | `(args| [$args,*]) => args.getElems
    | _ => #[]
  | none => #[]
  let args : Array (Option (TSyntax `term ⊕ TSyntax `term)) := args.map fun t => match t with
    | `(arg| $_:star) => none
    | `(arg| - $t:term) => some (Sum.inr t)
    | `(arg| $t:term) => some (Sum.inl t)
    | _ => panic! "Unreachable parse of solve_by_elim arguments."
  let args := args.toList
  (args.contains none,
    args.filterMap fun o => o.bind Sum.getLeft,
    args.filterMap fun o => o.bind Sum.getRight)

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `maxDepth` (currently hard-coded to 12) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs backtracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ, attr₁, ... attrᵣ]` also applies the named lemmas,
  (not implemented yet:) as well as all lemmas tagged with the specified attributes.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* (not implemented yet:) `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions,
   removing the specified ones.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated subgoals
- `symm`: allow `solve_by_elim` to call `symm` on subgoals (defaults to `true`)
- `exfalso`: allow calling `exfalso` (defaults to `true`)

See also the doc-comment for `Mathlib.Tactic.SolveByElim.Config` for the options
`proc`, `suspend`, and `discharge` which allow further customization of `solve_by_elim`.
-/
syntax (name := solveByElimSyntax) "solve_by_elim" "*"? (config)? (&" only")? (args)? : tactic

/-- Wrapper for `solveByElim` that processes a list of ``TSyntax `term``
that specify the lemmas to use. -/
def solveByElim.processSyntax
    (cfg : Config := {}) (only star : Bool := false) (add remove : List (TSyntax `term))
    (goals : List MVarId) : MetaM (List MVarId) := do
  let ⟨lemmas, ctx⟩ ← mkAssumptionSet only star add remove
  trace[Meta.Tactic.solveByElim] "parsed assumptions"
  solveByElim cfg lemmas ctx goals

elab_rules : tactic |
    `(tactic| solve_by_elim $[*%$s]? $[$cfg]? $[only%$o]? $[$t:args]?) => do
  let (star, add, remove) := parseArgs t
  let goals ← if s.isSome then
    getGoals
  else
    pure [← getMainGoal]
  let cfg ← elabConfig (mkOptionalNode cfg)
  let [] ← solveByElim.processSyntax cfg o.isSome star add remove goals |
    throwError "solve_by_elim unexpectedly returned subgoals"
  pure ()

/--
`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

You can specify additional rules to apply using `apply_assumption [...]`.
By default `apply_assumption` will also try `rfl`, `trivial`, `congrFun`, and `congrArg`.
If you don't want these, or don't want to use all hypotheses, use `apply_assumption only [...]`.

If `apply_assumption` fails it will call `symm` and try again.

If this also fails, it will call `exfalso` and try again,
so that if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

You can pass a further configuration via the syntax `apply_rules (config := {...}) lemmas`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).
-/
syntax (name := applyAssumptionSyntax) "apply_assumption" (config)? (&" only")? (args)? : tactic

elab_rules : tactic |
    `(tactic| apply_assumption $[$cfg]? $[only%$o]? $[$t:args]?) => do
  let (star, add, remove) := parseArgs t
  let cfg ← elabConfig (mkOptionalNode cfg)
  let cfg := { cfg with
    maxDepth := 1
    failAtMaxDepth := false }
  replaceMainGoal (← solveByElim.processSyntax cfg o.isSome star add remove [← getMainGoal])

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

(TODO: not yet supported in mathlib4)
You may include attributes amongst the lemmas:
`apply_rules` will include all lemmas marked with these attributes.

You can pass a further configuration via the syntax `apply_rules (config := {...})`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

`apply_rules` will try calling `symm` and `exfalso` as needed.
This can be disabled with `apply_rules (config := {symm := false, exfalso := false})`.

You can bound the iteration depth using the syntax `apply_rules (config := {maxDepth := n})`.
The default bound is 12.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.

TODO: copy the other tests/examples from Lean 3
-/
syntax (name := applyRulesSyntax) "apply_rules" (config)? (&" only")? (args)? : tactic

elab_rules : tactic |
    `(tactic| apply_rules $[$cfg]? $[only%$o]? $[$t:args]?)  => do
  let (star, add, remove) := parseArgs t
  let cfg ← elabConfig (mkOptionalNode cfg)
  let cfg := { cfg.noBackTracking with
    failAtMaxDepth := false }
  liftMetaTactic fun g => solveByElim.processSyntax cfg o.isSome star add remove [g]
