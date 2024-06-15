/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Batteries.Data.HashMap.Basic
import Batteries.Lean.SMap
import Batteries.Lean.Name
import Lean.Meta.Match.MatcherInfo

/-!
# Additional functions on `Lean.Name`.

We provide `allNames` and `allNamesByModule`.
-/

open Lean Meta Elab

private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.toString.startsWith "Lean" then return true
  let env ← getEnv
  pure <| declName.isInternalDetail
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
def allNamesByModule (p : Name → Bool) : CoreM (Batteries.HashMap Name (Array Name)) := do
  (← getEnv).constants.foldM (init := Batteries.HashMap.empty) fun names n _ => do
    if p n && !(← isBlackListed n) then
      let some m ← findModuleOf? n | return names
      -- TODO use `Batteries.HashMap.modify` when we bump Batteries (or `alter` if that is written).
      match names.find? m with
      | some others => return names.insert m (others.push n)
      | none => return names.insert m #[n]
    else
      return names

/-- Decapitalize the last component of a name. -/
def Lean.Name.decapitalize (n : Name) : Name :=
  n.modifyBase fun
    | .str p s => .str p s.decapitalize
    | n       => n
