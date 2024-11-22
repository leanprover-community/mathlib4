/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Tactic.DeclarationNames
import Mathlib.Lean.Expr.Basic

/-!
#  The "findDefEqAbuse" linter

The "findDefEqAbuse" linter emits a warning when a variable declared in variable ...
is globally unused.
-/

open Lean Parser Elab Command

namespace Mathlib.Linter

/--
The "findDefEqAbuse" linter emits a warning when a declaration relies on the implementation of
the definition stored in the `findDefEqAbuseRef` `IO.Ref`.
-/
register_option linter.findDefEqAbuse : Bool := {
  defValue := true
  descr := "enable the findDefEqAbuse linter"
}

/--
`findDefEqAbuseRef` is the `IO.Ref` containing the name of the declaration used by
`linter.findDefEqAbuse` to flag (ab)uses of definitional equality.
-/
initialize findDefEqAbuseRef : IO.Ref NameSet ← IO.mkRef (NameSet.insert ∅ `ENat)

/-- `find_defeq_abuse id` replaces the current value of the `findDefEqAbuseRef` with `id`.

The variant `find_defeq_abuse ! id` also reports if the declaration `id` is already present in
the environment or not.
-/
elab "find_defeq_abuse" tk:("!")? ppSpace id:ident : command => do
  findDefEqAbuseRef.set (NameSet.insert ∅ id.getId)
  match tk.isSome, ((← getEnv).find? id.getId).isSome with
    | true, false => logWarningAt id m!"There is no declaration named '{id}' in the environment"
    | true, true => logInfoAt id m!"The environment contains declaration '{id}'"
    | false, _ => return

namespace FindDefEqAbuse

@[inherit_doc Mathlib.Linter.linter.findDefEqAbuse]
def findDefEqAbuseLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.findDefEqAbuse (← getOptions) do
    return
  let nm ← findDefEqAbuseRef.get
  if (← get).messages.hasErrors then
    return
  unless stx.isOfKind ``declaration do
    return
  let env ← getEnv
  if nm.isEmpty then return
  if nm.all (env.find? · |>.isNone) then return
  let declIds := ← getNamesFrom <| stx.getPos?.getD default
  -- we re-elaborate the declaration in a new namespace, opening the old one
  let data ← withScope (fun s => {s with
      currNamespace := s.currNamespace ++ `another
      opts := diagnostics.threshold.set (diagnostics.set s.opts true) 1000000000
      openDecls := .simple s.currNamespace [] :: s.openDecls
    }) do
    elabCommand stx
    return Kernel.getDiagnostics (← getEnv)

  let declId := match stx.find? (·.isOfKind ``declId) with
    | none => declIds.back?.getD default
    | some d => d

  let mut bad : Option Name := none
  for forbidden in nm do
    if data.unfoldCounter.contains forbidden then
      bad := some forbidden
      break

  if let some v := bad then
    logWarningAt declId m!"'{declId}' relies on the definition of '{v}'"
    -- if let some var := env.find? declId.getId then
    --   let type ← liftTermElabM (Meta.inferType var.type)
    --   if type != .sort .zero then
    --     findDefEqAbuseRef.modify (NameSet.insert · declId.getId)

initialize addLinter findDefEqAbuseLinter

end FindDefEqAbuse

end Mathlib.Linter
