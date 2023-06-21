/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Kyle Miller
-/

import Lean

/-!
# The `use` tactic

The `use` and `use!` tactics are for instantiating one-constructor inductive types
just like the `exists` tactic, but they can be a little more flexible.

`use` is the more restrained version for mathlib4, and `use!` is the exuberant version
that more closely matches `use` from mathlib3.

Note: The `use!` tactic is almost exactly the mathlib3 `use` except that it does not try
applying `exists_prop`. See the failing test in `test/Use.lean`.
-/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic

initialize registerTraceClass `tactic.use

/--
When the goal `mvarId` is an inductive datatype with a single constructor,
this applies that constructor, then returns metavariables for the non-parameter explicit arguments
along with metavariables for the parameters and implicit arguments.

The first list of returned metavariables correspond to the arguments that `⟨x,y,...⟩` notation uses.

Returns metavariables for all arguments whether or not the metavariables are assigned.
-/
def _root_.Lean.MVarId.constructor1 (mvarId : MVarId) :
    MetaM (List MVarId × List MVarId) := do
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
          for arg in args, binderInfo in binderInfos, i in [0:args.size] do
            if cinfo.numParams ≤ i ∧ binderInfo.isExplicit then
              explicit := explicit.push arg.mvarId!
            else
              implicit := implicit.push arg.mvarId!
          let e := mkAppN ctorConst args
          let eType ← inferType e
          unless (← withAssignableSyntheticOpaque <| isDefEq eType target) do
            throwError m!"type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType target}"
          mvarId.assign e
          return (explicit.toList, implicit.toList)
        | _ => throwTacticEx `constructor mvarId
                m!"target inductive type does not have exactly one constructor{indentExpr target}"

/-- Use the `args` to refine the goals `gs` in order, but whenever there is a single
goal remaining then first try applying a single constructor if it's for a single-constructor
inductive type. In `eager` mode, instead we always first try to refine, and if that fails we
always try to apply such a constructor no matter if it's the last goal.

Returns the remaining explicit goals `gs` and any goals `acc` due to `refine`. The new set
of goals should be `gs ++ acc`. -/
partial
def useLoop (eager : Bool) (gs : List MVarId) (args : List Term) (acc : List MVarId) :
    TermElabM (List MVarId × List MVarId) := do
  trace[tactic.use] "gs = {gs}\nargs = {args}\nacc = {acc}"
  if args.isEmpty then
    return (gs, acc)
  else if gs.isEmpty then
    throwErrorAt args[0]! "too many arguments supplied to `use`"
  else if let (g :: gs', arg :: args') := (gs, args) then
    if ← g.isAssigned then
      -- Goals might become assigned in inductive types with indices.
      -- Let's check that what's supplied is defeq to what's already there.
      let e ← Term.elabTermEnsuringType arg (← g.getType)
      unless ← isDefEq e (.mvar g) do
        throwErrorAt arg
          "argument is not definitionally equal to inferred value{indentExpr (.mvar g)}"
      return ← useLoop eager gs' args' acc
    if eager then
      -- In eager mode, first try refining with the argument before applying the constructor
      if let some newGoals ← observing? (run g do
                                withoutRecover <| evalTactic (← `(tactic| refine $arg))) then
        return ← useLoop eager gs' args' (acc ++ newGoals)
    if eager || gs'.isEmpty then
      if let some (expl, impl) ← observing? do
                try g.constructor1 catch e => trace[tactic.use] "{e.toMessageData}"; throw e then
        trace[tactic.use] "expl.length = {expl.length}, impl.length = {impl.length}"
        return ← useLoop eager (expl ++ gs') args (acc ++ impl)
    -- In eager mode, this will give an error, which hopefully is more informative than
    -- the one provided by `constructor1`.
    let newGoals ← run g do evalTactic (← `(tactic| refine $arg))
    useLoop eager gs' args' (acc ++ newGoals)
  else
    throwError "useLoop: impossible"

/-- Run the `useLoop` on the main goal then discharge remaining explicit `Prop` arguments. -/
def runUse (eager : Bool) (discharger : TacticM Unit) (args : List Term) : TacticM Unit := do
  let egoals ← focus do
    let (egoals, acc) ← useLoop eager (← getGoals) args []
    setGoals (egoals ++ acc)
    pure egoals
  -- Run the discharger on non-assigned proposition metavariables
  -- (`trivial` uses `assumption`, which would be bad for non-propositions)
  for g in egoals do
    if !(← g.isAssigned) then
      if ← isProp (← g.getType) then
        trace[tactic.use] "running discharger on {g}"
        discard <| run g discharger

/-- Returns a `TacticM Unit` that either runs the tactic sequence from `discharger?` if it's
non-`none`, or it does `try with_reducible trivial`. -/
def mkUseDischarger (discharger? : Option (TSyntax ``Parser.Tactic.discharger)) :
    TacticM (TacticM Unit) := do
  let discharger ←
    if let some disch := discharger? then
      match disch with
      | `(Parser.Tactic.discharger| ($_ := $d)) => `(tactic| ($d))
      | _ => throwUnsupportedSyntax
    else
      `(tactic| try with_reducible trivial)
  return evalTactic discharger

/--
`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with `try with_reducible trivial` (rather
than `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it eagerly applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out. Thus, with `use!` one can feed in each `42` one
at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses `trivial` to discharge goals,
so `use! 42` will close the goal in this example since `trivial` applies `rfl`, which as a
consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible trivial) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
-/
elab (name := useSyntax)
    "use" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse false (← mkUseDischarger discharger?) args.getElems.toList

@[inherit_doc useSyntax]
elab "use!" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse true (← mkUseDischarger discharger?) args.getElems.toList
