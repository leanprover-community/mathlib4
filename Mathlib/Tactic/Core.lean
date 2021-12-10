/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/

import Lean.Expr
import Mathlib.Lean.Expr

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
def setProtected {m : Type → Type} [Monad m] [MonadEnv m] (nm : Name) : m Unit := do
  modifyEnv (addProtected · nm)

namespace Parser.Tactic

-- syntax simpArg := simpStar <|> simpErase <|> simpLemma
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

end Parser.Tactic
end Lean
