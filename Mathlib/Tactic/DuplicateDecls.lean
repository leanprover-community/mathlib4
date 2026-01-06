/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Mathlib.Init

/-!
# A tool for finding duplicate declarations

It is easy to accidentally create multiple instances of the same theorem or instance.
This file defines a tool to automatically detect such cases.
The order of hypotheses, and their binder info and binder names are ignored.
Universe parameters are also ignored.

For theorems, it is completely redundant to have multiple of the same type.
For instances, it is typical that we also don't want to have multiple of the same type.
-/

public meta section

namespace Mathlib.Tactic.DuplicateDecls
open Lean Meta

/-- Clear all universe levels from an expression, so that they are ignored.

Note: I tried using a cache in the implementation, but that seemed to only slow things down. -/
partial def eraseUnivs (e : Expr) : Expr :=
  match e with
  | .sort _ => .sort 0
  | .const declName _ => .const declName []
  | .app fn arg => e.updateApp! (eraseUnivs fn) (eraseUnivs arg)
  | .lam _ t b _ => e.updateLambdaE! (eraseUnivs t) (eraseUnivs b)
  | .forallE _ t b _ => e.updateForallE! (eraseUnivs t) (eraseUnivs b)
  | .letE _ t v b _ => e.updateLetE! (eraseUnivs t) (eraseUnivs v) (eraseUnivs b)
  | .mdata _ expr => e.updateMData! (eraseUnivs expr)
  | .proj _ _ s => e.updateProj! (eraseUnivs s)
  | e => e

/-- Sort the hypotheses in `e` into a normalized order by sorting their types.
Also replace universe levels with a default value.

TODO: When there are multiple variables of the same type, their order will not be changed.
  This is a limitation of the current approach. -/
def sortBinders (e : Expr) : MetaM Expr := do
  (if e.isLambda then lambdaTelescope else forallTelescope) e fun fvars e ↦ do
  let n := fvars.size
  let fvars : Vector Expr n := fvars.toVector
  let mut remainingTypes ← fvars.mapM (return some <| eraseUnivs <| ← inferType ·)
  let mut e := eraseUnivs e
  let mut sortedTypes := #[]
  for _ in *...n do
    let mut optMinIdx : Option (Fin n) := none
    let mut minType : Expr := default
    for h : i in [:n] do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if optMinIdx.isNone || type.quickLt minType then
            optMinIdx := some ⟨i, by get_elem_tactic⟩
            minType := type
    let some minIdx := optMinIdx | panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e ↦ .forallE `_ type e .default

/-- Return `true` if `cinfo` is defined as another constant.

Note: this check will not work for imported theorems in a `module`,
because the theorem body won't be imported. -/
def isAlias (cinfo : ConstantInfo) : Bool := cinfo.value?.any isConstBVarApp
where
  isConstBVarApp : Expr → Bool
  | .const .. => true
  | .app f (.bvar _) => isConstBVarApp f
  | .lam _ _ b _ => isConstBVarApp b
  | _ => false

/-- An inductive type for the kind of duplicate declarations to search for. -/
inductive Target where
  /-- Search for duplicate theorems. -/
  | theorems
  /-- Search for duplicate instances that aren't theorems.-/
  | instances
  /-- Search for duplicate definitions that aren't instances or theorems,
  Also indexing on the value, not just the type. -/
  | defs

/-- Compute an array of duplicate declarations in the current environment. -/
def duplicateDeclarations (cfg : Target) : CoreM (Array (Name × Name)) := MetaM.run' do
  let env ← getEnv
  let mut s : Std.HashMap Expr Name := {}
  let mut dups := #[]
  for (name, cinfo) in env.constants.map₁ do
    if name.isInternalDetail
      || name.isMetaprogramming
      || !allowCompletion env name
      || Linter.isDeprecated env name
      || isAlias cinfo then continue
    if ← Meta.isProp cinfo.type then
      unless cfg matches .theorems do continue
    else
      match cfg with
      | .theorems => continue
      | .instances => if (← isClass? cinfo.type).isNone then continue
      | .defs =>
        if (← isClass? cinfo.type).isNone then
          if let some value := cinfo.value? then
            let normValue ← sortBinders value
            let normType ← sortBinders cinfo.type
            let key := .app normValue normType
            if let some name' := s[key]? then
              dups := dups.push (name', name)
            else
              s := s.insert key name
        continue
    let normType ← sortBinders cinfo.type
    if let some name' := s[normType]? then
      dups := dups.push (name', name)
    else
      s := s.insert normType name
  return dups

/-- Get a number by which to sort the libraries. -/
private def libraryNumber (module : Name) : Nat :=
  #[`Init, `Lean, `Std, `Batteries, `Mathlib].idxOf module.getRoot

/-- Structure used for sorting imported modules. -/
private structure ModuleWithNum where
  number : Nat
  name : String

private instance : Ord ModuleWithNum := ⟨fun a b ↦ (compare a.1 b.1).then (compare a.2 b.2)⟩
private instance : LT ModuleWithNum := ltOfOrd
private instance : LE ModuleWithNum := leOfOrd

/-- Return the object by which to sort the module that `name` is from.
That is, the `libraryNumber` followed by the module as a string. -/
private def mkModuleWithNum (name : Name) (env : Environment) : ModuleWithNum :=
  let { module, .. } := env.header.modules[env.const2ModIdx[name]!]!
  { number := libraryNumber module, name := module.toString }

/-- Return the list of pairs of duplicate declarations, grouped by the name of the module
of one of the two lemmas. -/
def sortedDuplicateDeclarations (cfg : Target) :
    CoreM (Array (String × Array (Name × Name))) := do
  let env ← getEnv
  let dups ← duplicateDeclarations cfg
  let mut result : Std.TreeMap ModuleWithNum (Std.TreeMap ModuleWithNum (Array (Name × Name))) := {}
  for (a, b) in dups do
    let A := mkModuleWithNum a env
    let B := mkModuleWithNum b env
    if A < B then
      result := result.alter B (·.getD ∅ |>.alter A (·.getD #[] |>.push (b, a)))
    else
      result := result.alter A (·.getD ∅ |>.alter B (·.getD #[] |>.push (a, b)))
  return result.toArray.map fun (a, map) ↦ (a.2, map.valuesArray.flatten)

/-- Format the list of pairs of duplicate declarations. -/
def duplicateDeclarationsMessage (cfg : Target) : CoreM MessageData := do
  let dups ← sortedDuplicateDeclarations cfg
  let mut msg := m!"Number of duplicates: {dups.foldl (init := 0) (· + ·.2.size)}"
  for (module, dups) in dups do
    msg := msg ++ s!"\n\n-- {module}"
    for (a, b) in dups do
      msg := msg ++ m!"\n\n{.ofConstName a} : {(← getConstInfo a).type}\n\
                           {.ofConstName b} : {(← getConstInfo b).type}"
  return msg

end Mathlib.Tactic.DuplicateDecls
