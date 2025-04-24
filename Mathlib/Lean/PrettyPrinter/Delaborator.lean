/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Init
import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Additions to the delaborator
-/

namespace Lean.PrettyPrinter.Delaborator

open SubExpr

/-- Assuming the current expression in a lambda or pi,
descend into the body using an unused name generated from the binder's name.
Provides `d` with both `Syntax` for the bound name as an identifier
as well as the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName`. -/
def withBindingBodyUnusedName' {α} (d : Syntax → Expr → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)

/-- Update `OptionsPerPos` at the given position, setting the key `n`
to have the boolean value `v`. -/
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
  let e := opts.findD p {} |>.setBool n v
  opts.insert p e

/-- Annotates `stx` with the go-to-def information of `target`. -/
def annotateGoToDef (stx : Term) (target : Name) : DelabM Term := do
  let module := (← findModuleOf? target).getD (← getEnv).mainModule
  let some range ← findDeclarationRanges? target | return stx
  let stx ← annotateCurPos stx
  let location := { module, range := range.selectionRange }
  addDelabTermInfo (← getPos) stx (← getExpr) (location? := some location)
  return stx

/-- Annotates `stx` with the go-to-def information of the notation used in `stx`. -/
def annotateGoToSyntaxDef (stx : Term) : DelabM Term := do
  annotateGoToDef stx stx.raw.getKind

end Lean.PrettyPrinter.Delaborator
