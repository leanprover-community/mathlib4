/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Anne Baanen
-/
import ImportGraph.Imports
import Mathlib.Init

/-! # The `upstreamableDecl` linter

The `upstreamableDecl` linter detects declarations that could be moved to a file higher up in the
import hierarchy. This is intended to assist with splitting files.
-/

open Lean Elab Command Linter

/-- Does this declaration come from the current file? -/
def Lean.Name.isLocal (env : Environment) (decl : Name) : Bool :=
  (env.getModuleIdxFor? decl).isNone

open Mathlib.Command.MinImports

/-- Does the declaration with this name depend on definitions in the current file?

Here, "definition" means everything that is not a theorem, and so includes `def`,
`structure`, `inductive`, etc.
-/
def Lean.Environment.localDefinitionDependencies (env : Environment) (stx id : Syntax) :
    CommandElabM Bool := do
  let declName ← getDeclName stx
  let immediateDeps ← getAllDependencies stx id

  -- Drop all the unresolvable constants, otherwise `transitivelyUsedConstants` fails.
  let immediateDeps : NameSet := immediateDeps.fold (init := ∅) fun s n =>
    if (env.find? n).isSome then s.insert n else s

  let deps ← liftCoreM <| immediateDeps.transitivelyUsedConstants
  let constInfos := deps.toList.filterMap env.find?
  -- We allow depending on theorems and constructors.
  -- We explicitly allow constructors since `inductive` declarations are reported to depend on their
  -- own constructors, and we want inductives to behave the same as definitions, so place one
  -- warning on the inductive itself but nothing on its downstream uses.
  -- (There does not seem to be an easy way to determine, given `Syntax` and `ConstInfo`,
  -- whether the `ConstInfo` is a constructor declared in this piece of `Syntax`.)
  let defs := constInfos.filter (fun constInfo => !(constInfo matches .thmInfo _ | .ctorInfo _))

  return defs.any fun constInfo => declName != constInfo.name && constInfo.name.isLocal env

namespace Mathlib.Linter

/--
The `upstreamableDecl` linter detects declarations that could be moved to a file higher up in the
import hierarchy. If this is the case, it emits a warning.

By default, this linter will not fire on definitions, nor private declarations:
see options `linter.upstreamableDecl.defs` and `linter.upstreamableDecl.private`.

This is intended to assist with splitting files.
-/
register_option linter.upstreamableDecl : Bool := {
  defValue := false
  descr := "enable the upstreamableDecl linter"
}

/--
If set to `true`, the `upstreamableDecl` linter will add warnings on definitions.

The linter does not place a warning on any declaration depending on a definition in the current file
(while it does place a warning on the definition itself), since we often create a new file for a
definition on purpose.
-/
register_option linter.upstreamableDecl.defs : Bool := {
  defValue := false
  descr := "upstreamableDecl warns on definitions"
}

/--
If set to `true`, the `upstreamableDecl` linter will add warnings on private declarations.
-/
register_option linter.upstreamableDecl.private : Bool := {
  defValue := false
  descr := "upstreamableDecl warns on private declarations"
}

namespace DoubleImports

@[inherit_doc Mathlib.Linter.linter.upstreamableDecl]
def upstreamableDeclLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.upstreamableDecl (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let skipDef := !getLinterValue linter.upstreamableDecl.defs (← getLinterOptions)
    let skipPrivate := !getLinterValue linter.upstreamableDecl.private (← getLinterOptions)
    if stx == (← `(command| set_option $(mkIdent `linter.upstreamableDecl) true)) then return
    let env ← getEnv
    let id ← getId stx
    if id != .missing then
      -- Skip defs and private decls by default.
      let name ← getDeclName stx
      if (skipDef && if let some constInfo := env.find? name
         then !(constInfo matches .thmInfo _ | .ctorInfo _)
         else true) ||
       (skipPrivate && isPrivateName name) then
        return

      let minImports := getIrredundantImports env (← getAllImports stx id)
      match minImports with
      | ⟨(RBNode.node _ .leaf upstream _ .leaf), _⟩ => do
        if !(← env.localDefinitionDependencies stx id) then
          let p : GoToModuleLinkProps := { modName := upstream }
          let widget : MessageData := .ofWidget
            (← liftCoreM <| Widget.WidgetInstance.ofHash
              GoToModuleLink.javascriptHash <|
              Server.RpcEncodable.rpcEncode p)
            (toString upstream)
          Linter.logLint linter.upstreamableDecl id
            m!"Consider moving this declaration to the module {widget}."
      | _ => pure ()

initialize addLinter upstreamableDeclLinter

end DoubleImports

end Mathlib.Linter
