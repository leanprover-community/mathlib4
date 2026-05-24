/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Util.AddRelatedDecl

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.NonemptyAttr

/-- Given an expression assumed of type `α`, returns an expression for of type `Nonempty α`. -/
def toNonempty (e : Expr) : MetaM Expr := do
  mapForallTelescope
    (fun e' => do
      let e ← instantiateMVars e'
      let e2 ← mkAppM ``Nonempty.intro #[e]
      return e2) e

initialize registerBuiltinAttribute {
  name := `nonempty
  descr := "Adds a declaration of type `Nonempty α` when tagging a declaration of type `α`"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| nonempty) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "nonempty failed"
    addRelatedInst src ref (hoverInfo := true)
      fun value levels => do
        let newValue ← (toNonempty value)
        pure (newValue, levels)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic.NonemptyAttr

end

