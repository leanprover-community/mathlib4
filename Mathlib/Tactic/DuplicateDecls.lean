/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# A tool for finding duplicate declarations

It is easy to accidentally create multiple instances of the same theorem or instance.
This file defines a tool to automatically detect such cases.
The order of hypotheses, and their binder info and binder names are ignored.
Universe parameters are also ignored.

For theorems, it is completely redundant to have multiple of the same type.
For instances, we typically also don't want to have multiple of the same type.

To use it, simply run the following command in a file that does not use the module system:
```
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"
run_meta do logInfo m!"{← lintDuplicateDeclarations .instances}"
run_meta do logInfo m!"{← lintDuplicateDeclarations .defs}"
```
-/

meta section

namespace Mathlib.Tactic.DuplicateDecls
open Lean Meta

/-- Clear all universe levels from an expression, so that they are ignored. -/
-- Note: I tried using a cache in the implementation, but that seemed to only slow things down.
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
    let mut minType? : Option (Fin n × Expr) := none
    for h : i in [:n] do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if let some (minIdx, minType) := minType? then
            if type.quickLt minType then
              continue
          minType? := some (⟨i, by get_elem_tactic⟩, type)
    let some (minIdx, minType) := minType? |
      panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e ↦ .forallE `_ type e .default

/-- Return `true` if `cinfo` is defined as another constant.
If so, we assume that the declaration is intentionally duplicated.
This only works for exposed definitions. -/
def isAlias (cinfo : ConstantInfo) : Bool :=
  cinfo.value?.any isConstBVarApp
where
  isConstBVarApp : Expr → Bool
  | .const .. => true
  | .app f (.bvar _) => isConstBVarApp f
  | .lam _ _ b _ => isConstBVarApp b
  | _ => false

/-- Return `true` if `n₁` and `n₂` form a `rfl`-`refl` pair, which is a common case
of intentional theorem duplication. -/
def isRflRefl (n₁ n₂ : Name) : Bool :=
  match n₁, n₂ with
  | .str base₁ s₁, .str base₂ s₂ =>
    base₁ == base₂ && (
      match s₁.dropSuffix? "rfl", s₂.dropSuffix? "refl" with
      | some s₁, some s₂ => s₁ == s₂
      | _, _ =>
        match s₁.dropSuffix? "refl", s₂.dropSuffix? "rfl" with
        | some s₁, some s₂ => s₁ == s₂
        | _, _ => false)
  | _, _ => false

/-- An inductive type for the kind of duplicate declarations to search for. -/
public inductive Target where
  /-- Search for duplicate theorems. -/
  | theorems
  /-- Search for duplicate instances that aren't theorems. -/
  | instances
  /-- Search for duplicate definitions that aren't instances or theorems,
  Also indexes on the value, not just the type. -/
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
    if ← isProp cinfo.type then
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
              unless isRflRefl name name' do
                dups := dups.push (name', name)
            else
              s := s.insert key name
        continue
    let normType ← sortBinders cinfo.type
    if let some name' := s[normType]? then
      unless isRflRefl name name' do
        dups := dups.push (name', name)
    else
      s := s.insert normType name
  return dups

/-- Given a module name, return a number that can be used for sorting. -/
def libraryNumber (module : Name) : Nat :=
  #[`Init, `Lean, `Std, `Batteries, `Mathlib].idxOf module.getRoot

/-- Structure used for sorting imported modules:
1. The number given by `libraryNumber`.
2. The name of the module as a string.
-/
def ModuleKey := Nat × String

instance : Ord ModuleKey := ⟨fun a b ↦ (compare a.1 b.1).then (compare a.2 b.2)⟩
instance : LT ModuleKey := ltOfOrd
instance : LE ModuleKey := leOfOrd

/-- Return the object by which to sort the module that `name` is from.
That is, the `libraryNumber` followed by the module as a string. -/
def mkModuleKey (name : Name) (env : Environment) : ModuleKey :=
  let { module, .. } := env.header.modules[env.const2ModIdx[name]!]!
  (libraryNumber module, module.toString)

/-- Return the list of pairs of duplicate declarations, grouped by the name of the module
of one of the two lemmas. -/
public def sortedDuplicateDeclarations (cfg : Target) :
    CoreM (Array (String × Array (Name × Name))) := do
  let env ← getEnv
  let dups ← duplicateDeclarations cfg
  let mut result : Std.TreeMap ModuleKey (Std.TreeMap ModuleKey (Array (Name × Name))) := {}
  for (a, b) in dups do
    let A := mkModuleKey a env
    let B := mkModuleKey b env
    let (A, B, a, b) := if A < B then (B, A, b, a) else (A, B, a, b)
    result := result.alter A (·.getD ∅ |>.alter B (·.getD #[] |>.push (a, b)))
  return result.toArray.map fun (a, map) ↦ (a.2, map.valuesArray.flatten)

/-- The duplicate declarations linter. It tells you which duplicate declarations there are
in the current environment. -/
public def lintDuplicateDeclarations (cfg : Target) : CoreM MessageData := do
  let dups ← sortedDuplicateDeclarations cfg
  let mut msg := m!"Number of duplicates: {dups.foldl (init := 0) (· + ·.2.size)}"
  for (module, dups) in dups do
    msg := msg ++ s!"\n\n-- {module}"
    for (a, b) in dups do
      msg := msg ++ m!"\n\n{.ofConstName a} : {(← getConstInfo a).type}\n\
                           {.ofConstName b} : {(← getConstInfo b).type}"
  return msg

end Mathlib.Tactic.DuplicateDecls
