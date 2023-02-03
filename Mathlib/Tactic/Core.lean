/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Aurélien Saue, Mario Carneiro
-/
import Std.Tactic.Simpa
import Mathlib.Lean.Expr

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

/-- 
Variant on `rewriteTarget` that behaves more like the Lean 3 version 
-/
def rewriteTarget' (stx : Syntax) (symm : Bool) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).rewrite (← getMainTarget) e symm (config := {})
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal ([mvarId'])

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

variable [Monad m] [MonadExceptOf Exception m]

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
| (a+1), n, tac => do 
  let _ ← tac 
  let _ ← iterateRange a (n-1) tac 
  pure ()

/-- Repeats a tactic until it fails. Always succeeds. -/
partial def iterateUntilFailure (tac : m Unit) : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()

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
