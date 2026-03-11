/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Helper functions for environment extensions and attributes.
-/

public meta section

namespace Lean

open SimpleScopedEnvExtension

private initialize sharedScopedEnvExtensions :
    IO.Ref (NameMap (Descr EnvExtensionEntry EnvExtensionState)) ←
  IO.mkRef {}

private noncomputable local instance {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

private initialize sharedScopedEnvExtension :
    SimpleScopedEnvExtension (Name × EnvExtensionEntry)
      (NameMap (Descr EnvExtensionEntry EnvExtensionState × EnvExtensionState)) ←
  registerScopedEnvExtension {
    mkInitial := return (← sharedScopedEnvExtensions.get).map fun _ descr ↦ (descr, descr.initial)
    addEntry s e := s.modify e.1 fun (descr, s) ↦ (descr, descr.addEntry s e.2)
    toOLeanEntry := id
    ofOLeanEntry := fun _ a => return a
    finalizeImport s := s.map fun _ (descr, s) ↦ (descr, descr.finalizeImport s)
  }

variable {α σ : Type}

deriving instance Inhabited for Descr

/-- `SharedScopedEnvExtension` is an alternative to `SimpleScopedEnvExtension`
which may be more efficient. -/
structure SharedScopedEnvExtension (α σ : Type) where
  /-- The underlying `SimpleScopedEnvExtension.Descr`. -/
  descr : Descr α σ
  deriving Inhabited

private unsafe def registerSharedScopedEnvExtensionUnsafe (descr : Descr α σ) :
    IO (SharedScopedEnvExtension α σ) := do
  if (← sharedScopedEnvExtensions.get).contains descr.name then
    throw <| IO.userError s!"A shared scoped env extension called `{descr.name}` already exists"
  sharedScopedEnvExtensions.modify (·.insert descr.name (unsafeCast descr))
  return { descr }

/-- Register a new `SharedScopedEnvExtension`. -/
@[implemented_by registerSharedScopedEnvExtensionUnsafe]
opaque registerSharedScopedEnvExtension (descr : Descr α σ) : IO (SharedScopedEnvExtension α σ)

namespace SharedScopedEnvExtension

private unsafe def addCoreUnsafe (env : Environment) (ext : SharedScopedEnvExtension α σ)
    (a : α) (kind : AttributeKind) (namespaceName : Name) : Environment :=
  sharedScopedEnvExtension.addCore env (ext.descr.name, unsafeCast a) kind namespaceName

/-- Add an entry to the environment extension. -/
@[implemented_by addCoreUnsafe]
opaque addCore (env : Environment) (ext : SharedScopedEnvExtension α σ)
    (a : α) (kind : AttributeKind) (namespaceName : Name) : Environment

/-- Add an entry to the environment extension. -/
def add {m} [Monad m] [MonadResolveName m] [MonadEnv m]
    (ext : SharedScopedEnvExtension α σ) (a : α) (kind := AttributeKind.global) : m Unit := do
  let ns ← getCurrNamespace
  modifyEnv (ext.addCore · a kind ns)

private unsafe def getStateUnsafe [Inhabited σ] (ext : SharedScopedEnvExtension α σ)
    (env : Environment) : σ :=
  if let some (_, s) := (sharedScopedEnvExtension.getState env).get? ext.descr.name then
    unsafeCast s
  else
    panic! s!"There is no shared scoped env extension called `{ext.descr.name}`."

/-- Get the state of the environment extension. -/
@[implemented_by getStateUnsafe]
opaque getState [Inhabited σ] (ext : SharedScopedEnvExtension α σ) (env : Environment) : σ

end Lean.SharedScopedEnvExtension
