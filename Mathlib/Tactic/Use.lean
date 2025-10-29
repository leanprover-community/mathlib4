/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Kyle Miller
-/
import Mathlib.Tactic.WithoutCDot
import Lean.Meta.Tactic.Util
import Lean.Elab.Tactic.Basic

/-!
# The `use` tactic

The `use` and `use!` tactics are for instantiating one-constructor inductive types
just like the `exists` tactic, but they can be a little more flexible.

`use` is the more restrained version for mathlib4, and `use!` is the exuberant version
that more closely matches `use` from mathlib3.

Note: The `use!` tactic is almost exactly the mathlib3 `use` except that it does not try
applying `exists_prop`. See the failing test in `MathlibTest/Use.lean`.
-/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic

initialize registerTraceClass `tactic.use

/--
When the goal `mvarId` is an inductive datatype with a single constructor,
this applies that constructor, then returns metavariables for the non-parameter explicit arguments
along with metavariables for the parameters and implicit arguments.

The first list of returned metavariables correspond to the arguments that `⟨x,y,...⟩` notation uses.
The second list corresponds to everything else: the parameters and implicit arguments.
The third list consists of those implicit arguments that are instance implicits, which one can
try to synthesize. The third list is a sublist of the second list.

Returns metavariables for all arguments whether or not the metavariables are assigned.
-/
def applyTheConstructor (mvarId : MVarId) :
    MetaM (List MVarId × List MVarId × List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `constructor
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId
                  m!"target is not an inductive datatype{indentExpr target}")
      fun ival us => do
        match ival.ctors with
        | [ctor] =>
          let cinfo ← getConstInfoCtor ctor
          let ctorConst := Lean.mkConst ctor us
          let (args, binderInfos, _) ← forallMetaTelescopeReducing (← inferType ctorConst)
          let mut explicit := #[]
          let mut implicit := #[]
          let mut insts := #[]
          for arg in args, binderInfo in binderInfos, i in [0:args.size] do
            if cinfo.numParams ≤ i ∧ binderInfo.isExplicit then
              explicit := explicit.push arg.mvarId!
            else
              implicit := implicit.push arg.mvarId!
              if binderInfo.isInstImplicit then
                insts := insts.push arg.mvarId!
          let e := mkAppN ctorConst args
          let eType ← inferType e
          unless (← withAssignableSyntheticOpaque <| isDefEq eType target) do
            throwError m!"type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType target}"
          mvarId.assign e
          return (explicit.toList, implicit.toList, insts.toList)
        | _ => throwTacticEx `constructor mvarId
                m!"target inductive type does not have exactly one constructor{indentExpr target}"

/-- Use the `args` to refine the goals `gs` in order, but whenever there is a single
goal remaining then first try applying a single constructor if it's for a single-constructor
inductive type. In `eager` mode, instead we always first try to refine, and if that fails we
always try to apply such a constructor no matter if it's the last goal.

Returns the remaining explicit goals `gs`, any goals `acc` due to `refine`, and a sublist of these
of instance arguments that we should try synthesizing after the loop.
The new set of goals should be `gs ++ acc`. -/
partial
def useLoop (eager : Bool) (gs : List MVarId) (args : List Term) (acc insts : List MVarId) :
    TermElabM (List MVarId × List MVarId × List MVarId) := do
  trace[tactic.use] "gs = {gs}\nargs = {args}\nacc = {acc}"
  match gs, args with
  | gs, [] =>
    return (gs, acc, insts)
  | [], arg :: _ =>
    throwErrorAt arg "too many arguments supplied to `use`"
  | g :: gs', arg :: args' => g.withContext do
    if ← g.isAssigned then
      -- Goals might become assigned in inductive types with indices.
      -- Let's check that what's supplied is defeq to what's already there.
      let e ← Term.elabTermEnsuringType arg (← g.getType)
      unless ← isDefEq e (.mvar g) do
        throwErrorAt arg
          "argument is not definitionally equal to inferred value{indentExpr (.mvar g)}"
      return ← useLoop eager gs' args' acc insts
    -- Type ascription is a workaround for `refine` ensuring the type after synthesizing mvars.
    let refineArg ← `(tactic| refine ($arg : $(← Term.exprToSyntax (← g.getType))))
    if eager then
      -- In eager mode, first try refining with the argument before applying the constructor
      if let some newGoals ← observing? (run g do withoutRecover <| evalTactic refineArg) then
        return ← useLoop eager gs' args' (acc ++ newGoals) insts
    if eager || gs'.isEmpty then
      if let some (expl, impl, insts') ← observing? do
                try applyTheConstructor g
                catch e => trace[tactic.use] "Constructor. {e.toMessageData}"; throw e then
        trace[tactic.use] "expl.length = {expl.length}, impl.length = {impl.length}"
        return ← useLoop eager (expl ++ gs') args (acc ++ impl) (insts ++ insts')
    -- In eager mode, the following will give an error, which hopefully is more informative than
    -- the one provided by `applyTheConstructor`.
    let newGoals ← run g do evalTactic refineArg
    useLoop eager gs' args' (acc ++ newGoals) insts

/-- Run the `useLoop` on the main goal then discharge remaining explicit `Prop` arguments. -/
def runUse (eager : Bool) (discharger : TacticM Unit) (args : List Term) : TacticM Unit := do
  let egoals ← focus do
    let (egoals, acc, insts) ← useLoop eager (← getGoals) args [] []
    -- Try synthesizing instance arguments
    for inst in insts do
      if !(← inst.isAssigned) then
        discard <| inst.withContext <| observing? do inst.assign (← synthInstance (← inst.getType))
    -- Set the goals.
    setGoals (egoals ++ acc)
    pruneSolvedGoals
    pure egoals
  -- Run the discharger on non-assigned proposition metavariables
  -- (`trivial` uses `assumption`, which isn't great for non-propositions)
  for g in egoals do
    if !(← g.isAssigned) then
      g.withContext do
        if ← isProp (← g.getType) then
          trace[tactic.use] "running discharger on {g}"
          discard <| run g discharger

/-- Default discharger to try to use for the `use` and `use!` tactics.
This is similar to the `trivial` tactic but doesn't do things like `contradiction` or `decide`. -/
syntax "use_discharger" : tactic

macro_rules | `(tactic| use_discharger) => `(tactic| apply exists_prop.mpr <;> use_discharger)
macro_rules | `(tactic| use_discharger) => `(tactic| apply And.intro <;> use_discharger)
macro_rules | `(tactic| use_discharger) => `(tactic| rfl)
macro_rules | `(tactic| use_discharger) => `(tactic| assumption)
macro_rules | `(tactic| use_discharger) => `(tactic| apply True.intro)

/-- Returns a `TacticM Unit` that either runs the tactic sequence from `discharger?` if it's
non-`none`, or it does `try with_reducible use_discharger`. -/
def mkUseDischarger (discharger? : Option (TSyntax ``Parser.Tactic.discharger)) :
    TacticM (TacticM Unit) := do
  let discharger ←
    if let some disch := discharger? then
      match disch with
      | `(Parser.Tactic.discharger| ($_ := $d)) => `(tactic| ($d))
      | _ => throwUnsupportedSyntax
    else
      `(tactic| try with_reducible use_discharger)
  return evalTactic discharger

/--
`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out, with the supplied values being used along the
leaves and nodes of the tree of constructors.
With `use!` one can feed in each `42` one at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
To allow "heavy refls", use `(discharger := try use_discharger)`.
-/
elab (name := useSyntax)
    "use" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse false (← mkUseDischarger discharger?) args.getElems.toList

@[inherit_doc useSyntax]
elab "use!" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse true (← mkUseDischarger discharger?) args.getElems.toList

end Mathlib.Tactic
