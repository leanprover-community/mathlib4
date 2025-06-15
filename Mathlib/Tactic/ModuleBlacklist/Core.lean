/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init

/-!

## A blacklist for modules whose theorems are implementation details

This blacklist is intended for library search tactics like `rw??`.
It is similar in spirit to what is being done in https://github.com/leanprover/lean4/pull/6672

-/

open Lean

initialize directoryBlackListExt : SimpleScopedEnvExtension Name (Std.HashSet Name) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := .insert
  }

elab "blacklist_dir" dirs:ident+ : command => do
  for dir in dirs do withRef dir do
    let dir := dir.getId
    if dir matches .anonymous then
      throwError "expected a directory name, not `.anonymous`"
    unless (← getEnv).header.moduleNames.any dir.isPrefixOf do
      throwError "could not find any imported module starting with {dir}"
    directoryBlackListExt.add dir

elab "whitelist_dir" dirs:ident+ : command => do
  for dir in dirs do withRef dir do
    let dir := dir.getId
    if dir matches .anonymous then
      throwError "expected a directory name, not `.anonymous`"
    unless (directoryBlackListExt.getState (← getEnv)).contains dir do
      throwError "could not whitelist {dir} as it hasn't been blacklisted"
    modifyEnv (directoryBlackListExt.modifyState · (·.erase dir))

def Lean.Name.isBlacklistedModule (moduleName : Name) (env : Environment) : Bool :=
  (directoryBlackListExt.getState env).any (·.isPrefixOf moduleName)

def Lean.Name.hasBlacklistedModule (constName : Name) (env : Environment) : Bool :=
  env.header.moduleNames[env.const2ModIdx[constName]!]!.isBlacklistedModule env
