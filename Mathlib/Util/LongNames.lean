/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap
import Mathlib.Lean.Expr.Basic

/-!
# Commands `#long_names` and `#long_instances`

For finding declarations with excessively long names.
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
  let mut names := #[]
  for (n, _) in (← getEnv).constants.map₁.toList ++ (← getEnv).constants.map₂.toList do
    if p n && !(← isBlackListed n) then
      names := names.push n
  pure names

def Lean.Name.getModule (n : Name) : CoreM (Option Name) := do
  let env ← getEnv
  let modules := env.header.moduleNames
  match env.const2ModIdx[n] with
  | none => pure none
  | some (idx : Nat) => pure modules[idx]?

/--
Collect the values in an `Array` into a `HashMap`, according to their values under a function.
-/
def gatherBy [BEq β] [Hashable β] (x : Array α) (f : α → β) : Std.HashMap β (Array α) := Id.run do
  let mut h := Std.HashMap.empty
  for a in x do
    let b := f a
    h := h.insert b (match h.find? b with
    | none => #[a]
    | some l => l.push a)
  pure h

/--
Retrieve all names in the environment satisfying a predicate,
gathered together into a `HashMap` according to the module they are defined in. -/
def allNamesByModule (p : Name → Bool) : CoreM (Std.HashMap Name (Array Name)) := do
  let names ← (← allNames p) |>.filterMapM fun n => do pure <| (n, ·) <$> (← n.getModule)
  pure <| gatherBy names (·.2) |>.mapVal fun _ n => n.map (·.1)

/-- Helper function for `#long_names` and `#long_instances`. -/
def printNameHashMap (h : Std.HashMap Name (Array Name)) : IO Unit :=
  for (m, names) in h.toList do
    IO.println "----"
    IO.println $ m.toString ++ ":"
    for n in names do
      IO.println n

/--
Lists all declarations with a long name, gathered according to the module they are defined in.
Use as `#long_names` or `#long_names 100` to specify the length.
-/
elab "#long_names " N:(num)? : command =>
  Command.runTermElabM fun _ => do
    let N := N.map TSyntax.getNat |>.getD 50
    let namesByModule ← allNamesByModule (fun n => n.toString.length > N)
    let namesByModule := namesByModule.filter fun m _ => m.getRoot.toString = "Mathlib"
    printNameHashMap namesByModule

/--
Lists all instances with a long name beginning with `inst`,
gathered according to the module they are defined in.
This is useful for finding automatically named instances with absurd names.

Use as `#long_names` or `#long_names 100` to specify the length.
-/
elab "#long_instances " N:(num)?: command =>
  Command.runTermElabM fun _ => do
    let N := N.map TSyntax.getNat |>.getD 50
    let namesByModule ← allNamesByModule
      (fun n => n.getString.startsWith "inst" && n.getString.length > N)
    let namesByModule := namesByModule.filter fun m _ => m.getRoot.toString = "Mathlib"
    printNameHashMap namesByModule
