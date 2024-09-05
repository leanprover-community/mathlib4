/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
import Lean.Meta.LazyDiscrTree

/-!
# Constructing a RefinedDiscrTree

This file defines the initialization of a `RefinedDiscrTree`, and in particular for one that
is built using all constants in the environment. For this we use a parallel computation.

Because `RefinedDiscrTree` is lazy, adding entries initially only requires computing
the first `Key` of the encoding.

-/
namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/--
Structure for quickly initializing a lazy discrimination tree with a large number
of elements using concurrent functions for generating entries.
-/
structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  root : Std.HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

@[specialize]
private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry α) → Array (LazyEntry α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }

/-- Add an entry to the pre-discrimination tree.-/
def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a pre-discrimination tree to a lazy discrimination tree. -/
def toLazy (d : PreDiscrTree α) (config : WhnfCoreConfig := {}) : RefinedDiscrTree α :=
  let { root, tries } := d
  { config, root, tries := tries.map (.node #[] {} {}) }

/-- Merge two discrimination trees. -/
def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  let (x, y, f) :=
        if x.root.size ≥ y.root.size then
          (x, y, fun y x => x ++ y)
        else
          (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree


/-- Information about a failed import. -/
private structure ImportFailure where
  /-- Module with constant that import failed on. -/
  module  : Name
  /-- Constant that import failed on. -/
  const   : Name
  /-- Exception that triggers error. -/
  exception : Exception

/-- Information generation from imported modules. -/
private structure ImportData where
  errors : IO.Ref (Array ImportFailure)

private def ImportData.new : BaseIO ImportData := do
  return { errors := ← IO.mkRef #[] }

/-
It is expensive to create two new `IO.Ref` references for every `MetaM` operation,
so instead we reuse the same references `mstate` and `cstate`. These are also used to
store the cache, and the namegenerator
-/
private def addConstToPreDiscrTree
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (data : ImportData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (tree : PreDiscrTree α) (name : Name) (constInfo : ConstantInfo) :
    BaseIO (PreDiscrTree α) := do
  if constInfo.isUnsafe then return tree
  if LazyDiscrTree.blacklistInsertion env name then return tree
  /- We need to reset the metavariable context in `mstate` every time. -/
  mstate.modify fun s => { cache := s.cache }
  let ctx : Meta.Context := { config := { transparency := .reducible } }
  /- There seems to be no reason to reset `cstate`. -/
  -- cstate.modify fun s => { env := s.env, cache := s.cache, ngen := s.ngen }
  match ← (((act name constInfo) ctx mstate) cctx cstate).toBaseIO with
  | .ok a =>
    return a.foldl (fun t (key, entry) => t.push key entry) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    data.errors.modify (·.push i)
    return tree


/--
Contains the pre discrimination tree and any errors occuring during initialization of
the library search tree.
-/
private structure InitResults (α : Type) where
  tree  : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

namespace InitResults

/-- Combine two initial results. -/
protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

private def toFlat (data : ImportData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩

private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (data : ImportData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (mname : Name)
    (mdata : ModuleData)
    (tree : PreDiscrTree α)
    (i : Nat := 0) : BaseIO (PreDiscrTree α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname data mstate cstate act tree name constInfo
    loadImportedModule cctx env data mstate cstate act mname mdata state (i+1)
  else
    return tree

private def createImportInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (capacity start stop : Nat) : BaseIO (InitResults α) := do
  let tree := { root := .empty capacity }
  go start stop tree (← ImportData.new) (← IO.mkRef {}) (← IO.mkRef { env, ngen })
where
  go (start stop : Nat) (tree : PreDiscrTree α)
      (data : ImportData)
      (mstate : IO.Ref Meta.State)
      (cstate : IO.Ref Core.State) :
      BaseIO (InitResults α) := do
    if start < stop then
      let mname := env.header.moduleNames[start]!
      let mdata := env.header.moduleData[start]!
      let tree ← loadImportedModule cctx env data mstate cstate act mname mdata tree
      go (start+1) stop tree data mstate cstate
    else
      toFlat data tree
  termination_by stop - start

private def getChildNgen : MetaM NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

private def logImportFailure (f : ImportFailure) : MetaM Unit :=
  logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/-- Create a discriminator tree for imported environment. -/
def createImportedDiscrTree (cctx : Core.Context) (ngen : NameGenerator) (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (constantsPerTask capacityPerTask : Nat) (config : WhnfCoreConfig) :
    MetaM (RefinedDiscrTree α) := do
  let numModules := env.header.moduleData.size
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (ngen : NameGenerator) (tasks : Array (Task (InitResults α))) (start cnt idx : Nat) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (pure (← createImportInitResults
            cctx childNGen env act capacityPerTask start (idx+1)) : BaseIO _).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (pure (← createImportInitResults
            cctx childNGen env act capacityPerTask start numModules) : BaseIO _).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r : InitResults α := tasks.foldl (init := {}) (· ++ ·.get)
  r.errors.forM logImportFailure
  return r.tree.toLazy config

/--
A discriminator tree for the current module's declarations only.

Note. We use different discriminator trees for imported and current module
declarations since imported declarations are typically much more numerous but
not changed after the environment is created.
-/
structure ModuleDiscrTreeRef (α : Type _) where
  /-- The reference to the `RefinedDiscrTree`. -/
  ref : IO.Ref (RefinedDiscrTree α)

private def createLocalPreDiscrTree
    (cctx : Core.Context)
    (ngen : NameGenerator)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α))) :
    BaseIO (InitResults α) := do
  let modName := env.header.mainModule
  let data ← ImportData.new
  let r ← env.constants.map₂.foldlM (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act) { }
  toFlat data r

/-- Create a discriminator tree for current module declarations. -/
def createModuleDiscrTree (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α))) :
    MetaM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createLocalPreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toLazy

/--
Creates reference for lazy discriminator tree that only contains this module's definitions.
-/
def createModuleTreeRef (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α))) :
    MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (←getOptions) $ do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }
