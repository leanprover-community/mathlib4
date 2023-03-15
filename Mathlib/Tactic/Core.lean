/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Aurélien Saue, Mario Carneiro
-/
import Std.Tactic.Simpa
import Mathlib.Lean.Expr

/-!
#

Generally useful tactics.

-/

open Lean.Elab.Tactic

namespace Lean

open Elab

/--
Return the modifiers of declaration `nm` with (optional) docstring `newDoc`.
Currently, recursive or partial definitions are not supported, and no attributes are provided.
-/
def toModifiers (nm : Name) (newDoc : Option String := none) :
  CoreM Modifiers := do
  let env ← getEnv
  let d ← getConstInfo nm
  let mods : Modifiers :=
  { docString? := newDoc
    visibility :=
    if isPrivateNameExport nm then
      Visibility.private
    else if isProtected env nm then
      Visibility.regular
    else
      Visibility.protected
    isNoncomputable := if (env.find? $ nm.mkStr "_cstage1").isSome then false else true
    recKind := RecKind.default -- nonrec only matters for name resolution, so is irrelevant (?)
    isUnsafe := d.isUnsafe
    attrs := #[] }
  return mods

/--
Make a PreDefinition taking some metadata from declaration `nm`.
You can provide a new type, value and (optional) docstring, but the remaining information is taken
from `nm`.
Currently only implemented for definitions and theorems. Also see docstring of `toModifiers`
-/
def toPreDefinition (nm newNm : Name) (newType newValue : Expr) (newDoc : Option String := none) :
  CoreM PreDefinition := do
  let d ← getConstInfo nm
  let mods ← toModifiers nm newDoc
  let predef : PreDefinition :=
  { ref := Syntax.missing
    kind := if d.isDef then DefKind.def else DefKind.theorem
    levelParams := d.levelParams
    modifiers := mods
    declName := newNm
    type := newType
    value := newValue }
  return predef

/-- Make `nm` protected. -/
def setProtected {m : Type → Type} [MonadEnv m] (nm : Name) : m Unit :=
  modifyEnv (addProtected · nm)

namespace Parser.Tactic

syntax withArgs := " with " (colGt ident)+
syntax usingArg := " using " term

/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
def getSimpArgs : Syntax → TacticM (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _                      => Elab.throwUnsupportedSyntax

/-- Extract the arguments from a `dsimpArgs` syntax as an array of syntaxes -/
def getDSimpArgs : Syntax → TacticM (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _                       => Elab.throwUnsupportedSyntax

/-- Extract the arguments from a `withArgs` syntax as an array of syntaxes -/
def getWithArgs : Syntax → TacticM (Array Syntax)
  | `(withArgs| with $args*) => pure args
  | _                        => Elab.throwUnsupportedSyntax

/-- Extract the argument from a `usingArg` syntax as a syntax term -/
def getUsingArg : Syntax → TacticM Syntax
  | `(usingArg| using $e) => pure e
  | _                     => Elab.throwUnsupportedSyntax

/--
`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| (($seq); repeat $seq))

end Parser.Tactic
end Lean

namespace Lean.Elab.Tactic

/-- Given a local context and an array of `FVarIds` assumed to be in that local context, remove all
implementation details. -/
def filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVarId) : Array FVarId :=
  fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

/-- Elaborate syntax for an `FVarId` in the local context of the given goal. -/
def getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId := withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _                => throwError "unexpected term '{e}'; expected single reference to variable"

/-- Get the array of `FVarId`s in the local context of the given `goal`.

If `ids` is specified, elaborate them in the local context of the given goal to obtain the array of
`FVarId`s.

If `includeImplementationDetails` is `false` (the default), we filter out implementation details
(`implDecl`s and `auxDecl`s) from the resulting list of `FVarId`s. -/
def getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax) := none)
    (includeImplementationDetails : Bool := false) : TacticM (Array FVarId) :=
  goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
    | some ids => ids.mapM <| getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds

/--
Run a tactic on all goals, and always succeeds.

(This is parallel to `Lean.Elab.Tactic.evalAllGoals` in core,
which takes a `Syntax` rather than `TacticM Unit`.
This function could be moved to core and `evalAllGoals` refactored to use it.)
-/
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/-- Simulates the `<;>` tactic combinator. First runs `tac1` and then runs
    `tac2` on all newly-generated subgoals.
-/
def andThenOnSubgoals (tac1 : TacticM Unit)  (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2

variable [Monad m] [MonadExcept Exception m]

/-- Repeats a tactic at most `n` times, stopping sooner if the
tactic fails. Always succeeds. -/
def iterateAtMost : Nat → m Unit → m Unit
| 0, _ => pure ()
| n + 1, tac => try tac; iterateAtMost n tac catch _ => pure ()

/-- `iterateExactly' n t` executes `t` `n` times. If any iteration fails, the whole tactic fails.
-/
def iterateExactly' : Nat → m Unit → m Unit
| 0, _ => pure ()
| n+1, tac => tac *> iterateExactly' n tac

/--
`iterateRange m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` times.
-/
def iterateRange : Nat → Nat → m Unit → m Unit
| 0, 0, _   => pure ()
| 0, b, tac => iterateAtMost b tac
| (a+1), n, tac => do tac; iterateRange a (n-1) tac

/-- Repeats a tactic until it fails. Always succeeds. -/
partial def iterateUntilFailure (tac : m Unit) : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()

/-- `iterateUntilFailureWithResults` is a helper tactic which accumulates the list of results
obtained from iterating `tac` until it fails. Always succeeds.
-/
partial def iterateUntilFailureWithResults {α : Type} (tac : m α) : m (List α) := do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []

/-- `iterateUntilFailureCount` is similar to `iterateUntilFailure` except it counts
the number of successful calls to `tac`. Always succeeds.
-/
def iterateUntilFailureCount {α : Type} (tac : m α) : m Nat := do
  let r ← iterateUntilFailureWithResults tac
  return r.length

--TODO: add heartbeats?
/-- Given a function `f` that maps its elements to lists of elements in a monad that supports
failure, we recursively apply `f` to all elements in an accumulated list of results, starting with
`init`. If an element leads to a failure, we keep the element and stop evaluating `f` on it; if it
leads to a success, we collect all produced elements and recurse. This function will run until no
more progress can be made. -/
partial def repeatM [Monad m] [MonadExcept ε m] [MonadBacktrack s m] (init : List α)
    (f : α → m (List α)) : m (List α) := do
  go #[] init.toArray
where
  /-- Given an accumulated list of `finished` `α`s, and an array of `continuing` ones, recurse
  after evaluating `f` on all `continuing` elements. -/
  go (finished : Array α) (continuing : Array α) : m (List α) := do
    if continuing.isEmpty then
      pure finished.toList
    else
      let (finished, continuing) ←
        continuing.foldlM
          (fun (fin, con) a => do
            let s ← saveState
            try
              let c ← f a
              pure (fin, con.appendList c)
            catch _ =>
              restoreState s
              pure (fin.push a, con))
          (finished, #[])
      go finished continuing

end Lean.Elab.Tactic

namespace Mathlib
open Lean

/-- Returns the root directory which contains the package root file, e.g. `Mathlib.lean`. -/
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← initSrcSearchPath (← findSysroot)
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
  throw <| IO.userError s!"Could not find {pkg} directory. {
    ""}Make sure the LEAN_SRC_PATH environment variable is set correctly."

/-- Returns the mathlib root directory. -/
def getMathlibDir := getPackageDir "Mathlib"
