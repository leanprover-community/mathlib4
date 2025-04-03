/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Batteries.Tactic.Basic

/-!
# Environment extension for the forward-reasoning part of the `gcongr` tactic
-/

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.GCongr

/-- An extension for `gcongr_forward`. -/
structure ForwardExt where
  eval (h : Expr) (goal : MVarId) : MetaM Unit

/-- Read a `gcongr_forward` extension from a declaration of the right type. -/
def mkForwardExt (n : Name) : ImportM ForwardExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck ForwardExt opts ``ForwardExt n

/-- Environment extensions for `gcongrForward` declarations -/
initialize forwardExt : PersistentEnvExtension Name (Name × ForwardExt)
    (List Name × List (Name × ForwardExt)) ←
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt n => do
        return (n, ← mkForwardExt n) :: dt
      pure ([], dt)
    addEntryFn := fun (entries, s) (n, ext) => (n :: entries, (n, ext) :: s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `gcongr_forward
  descr := "adds a gcongr_forward extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| gcongr_forward) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'gcongr_forward', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'gcongr_forward', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkForwardExt declName
      setEnv <| forwardExt.addEntry env (declName, ext)
    | _ => throwUnsupportedSyntax
}
