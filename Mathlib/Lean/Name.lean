/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap
import Mathlib.Lean.SMap
import Mathlib.Lean.Expr.Basic

/-!
# Additional functions on `Lean.Name`.

We provide `Name.getModule`,
and `allNames` and `allNamesByModule`.
-/

open Lean Meta Elab

private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.toString.startsWith "Lean" then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

/--
Retrieve all names in the environment satisfying a predicate.
-/
def allNames (p : Name → Bool) : CoreM (Array Name) := do
  (← getEnv).constants.foldM (init := #[]) fun names n _ => do
    if p n && !(← isBlackListed n) then
      return names.push n
    else
      return names

/--
Retrieve all names in the environment satisfying a predicate,
gathered together into a `HashMap` according to the module they are defined in.
-/
def allNamesByModule (p : Name → Bool) : CoreM (Std.HashMap Name (Array Name)) := do
  (← getEnv).constants.foldM (init := Std.HashMap.empty) fun names n _ => do
    if p n && !(← isBlackListed n) then
      let some m ← findModuleOf? n | return names
      -- TODO use `Std.HashMap.modify` when we bump Std4 (or `alter` if that is written).
      match names.find? m with
      | some others => return names.insert m (others.push n)
      | none => return names.insert m #[n]
    else
      return names

/-- Returns the very first part of a name: for `Mathlib.Data.Set.Basic` it returns `Mathlib`. -/
def getModule (name : Name) (s := "") : Name :=
  match name with
    | .anonymous => s
    | .num _ _ => panic s!"panic in `getModule`: did not expect numerical name: {name}."
    | .str pre s => getModule pre s
