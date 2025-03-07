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
initialize findDefEqAbuseRef : IO.Ref Name ← IO.mkRef `ENat

/-- `find_defeq_abuse id` replaces the current value of the `findDefEqAbuseRef` with `id`.

The variant `find_defeq_abuse ! id` also reports if the declaration `id` is already present in
the environment or not.
-/
elab "find_defeq_abuse" tk:("!")? ppSpace id:ident : command => do
  findDefEqAbuseRef.set id.getId
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
  let id := mkIdent nm
  let env ← getEnv
  if (env.find? nm).isNone then return
  let declIds := ← getNamesFrom <| stx.getPos?.getD default
  let names := declIds.map (·.getId)
  -- ignore the declarations that do not contain `nm` in their *type*
  let names := ← names.filterM fun n => do
    if let some cinfo := env.find? n then
      return cinfo.type.containsConst (· == nm)
    else return false
  if names.isEmpty then return
  -- creating the syntax `attribute [local irreducible] nm`
  let irred := mkIdent `irreducible
  let preMkIrred ← `(command| attribute [$(⟨irred⟩)] $id)
  let mkIrred : Syntax := preMkIrred.raw.replaceM (m := Id) fun s =>
    if s.getId == `irreducible then
      some <| .node default `Lean.Parser.Term.attrInstance #[
        .node default `Lean.Parser.Term.attrKind (#[mkNullNode #[
          .node default ``Lean.Parser.Term.local #[mkAtom "local"]]]),
        .node default `Lean.Parser.Attr.simple #[s, mkNullNode]]
    else none
  let s ← get
  -- we re-elaborate the declaration in a new namespace, opening the old one
  withScope (fun s => {s with
      currNamespace := s.currNamespace ++ `another
      openDecls := .simple s.currNamespace [] :: s.openDecls
    }) do
    elabCommand <| mkNullNode #[mkIrred, stx]
  -- if the new elaboration produced errors, the linter assumes that the error was a defeq (ab)use
  -- this may not always be correct!
  if (← get).messages.hasErrors then
    set s
    let declId := match stx.find? (·.isOfKind ``declId) with
      | none => declIds.back?.getD default
      |some d => d
    logWarningAt declId m!"'{declId}' relies on the definition of '{nm}'"

initialize addLinter findDefEqAbuseLinter

end FindDefEqAbuse

end Mathlib.Linter
