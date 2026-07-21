/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Mathlib.Tactic.EnsureConstructive.Core
public meta import Lean.Elab.Command

open Lean Elab Command Mathlib.Tactic.EnsureConstructive

/--
`ensure_constructive foo` ensures that `foo` does not depend on any axioms besides `propext`
and `Quot.sound`.

`ensure_constructive foo up_to bar baz` ensures the same, except possibly for classicality in uses
of `bar` and `baz`.
-/
syntax "ensure_constructive " ident (&" up_to " ident,+)? : command

elab_rules : command
| `(ensure_constructive $id $[up_to $ignored,*]?) => runTermElabM fun _ => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let allowed ← ignored.elim #[] (·.getElems) |>.mapM (realizeGlobalConstNoOverloadWithInfo ·.raw)
  let constructiveBasic ← isConstructive n (constructiveAxioms ++ allowed)
  let constructive ← ensureConstructiveVerbose id (ignored.elim #[] (·.getElems))
  if !constructive && !(← MonadLog.hasErrors) then
    throwErrorAt id "`{id}` is not constructive, but no errors were logged. \
      This is an internal error."
  if !constructiveBasic && constructive then
    throwErrorAt id "`{id}` is not constructive, but rich errors were not logged. \
      This is an internal error."
