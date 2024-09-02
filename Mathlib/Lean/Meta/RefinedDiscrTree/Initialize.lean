/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Evaluate
import Lean.Meta.CompletionName

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
private structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  root : HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

@[specialize]
private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry α) → Array (LazyEntry α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root.find? k with
  | .none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | .some i =>
    { root, tries := tries.modify i f }

/-- Add an entry to the pre-discrimination tree.-/
private def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a pre-discrimination tree to a lazy discrimination tree. -/
private def toLazy (d : PreDiscrTree α) (config : WhnfCoreConfig := {}) : RefinedDiscrTree α :=
  let { root, tries } := d
  { config, root, tries := tries.map (.node #[] {} {}) }

/-- Merge two discrimination trees. -/
protected def append (x y : PreDiscrTree α) : PreDiscrTree α :=
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

private structure State (α : Type) where
  tree   : PreDiscrTree α := {}
  ngen   : NameGenerator
  core   : Lean.Core.Cache := {}
  meta   : Lean.Meta.Cache := {}
  errors : Array ImportFailure := #[]
deriving Inhabited

private def blacklistInsertion (env : Environment) (declName : Name) : Bool :=
  !allowCompletion env declName
  || declName == ``sorryAx
  || declName.isInternalDetail
  || (declName matches .str _ "inj")
  || (declName matches .str _ "noConfusionType")

private def addConstToPreDiscrTree
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (state : State α) (name : Name) (constInfo : ConstantInfo) : BaseIO (State α) := do
  if constInfo.isUnsafe then return state
  if blacklistInsertion env name then return state
  let { ngen, core := core_cache, meta := meta_cache, tree, .. } := state
  let mstate : Meta.State := { cache := meta_cache }
  let ctx : Meta.Context := { config := { transparency := .reducible } }
  let cm := (act name constInfo).run ctx mstate
  let cstate : Core.State := {env, cache := core_cache, ngen}
  match ← (cm.run cctx cstate).toBaseIO with
  | .ok ((a, ms), cs) =>
    let tree := a.foldl (fun t (key, entry) => t.push key entry) tree
    return { state with tree, ngen := cs.ngen, core := cs.cache, meta := ms.cache }
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e
    }
    let errors := state.errors.push i
    return { state with errors, core := {}, meta := {} }


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

private def State.toInitResults (state : State α) : InitResults α := { state with }

private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (mname : Name)
    (mdata : ModuleData)
    (state : State α)
    (i : Nat := 0) : BaseIO (State α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo  := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname act state name constInfo
    loadImportedModule cctx env act mname mdata state (i+1)
  else
    pure state

private def importedEnvironmentInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (capacity start stop : Nat) : BaseIO (InitResults α) := do
  let tree := { root := mkHashMap capacity }
  let state := { tree, ngen }
  go start stop state
where
  go (start stop : Nat) (state : State α) :
      BaseIO (InitResults α) := do
    if start < stop then
      let mname := env.header.moduleNames[start]!
      let mdata := env.header.moduleData[start]!
      let state ← loadImportedModule cctx env act mname mdata state
      go (start+1) stop state
    else
      return state.toInitResults
  termination_by stop - start

/-- Get the results of each task and merge using combining function -/
private def combineGet [Append α] (z : α) (tasks : Array (Task α)) : α :=
  tasks.foldl (fun x t => x ++ t.get) (init := z)

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
    (droppedKeys : List (List RefinedDiscrTree.Key))
    (constantsPerTask : Nat := 1000) (capacityPerTask := 128) :
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
          let t ← (importedEnvironmentInitResults cctx childNGen env act capacityPerTask start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (importedEnvironmentInitResults cctx childNGen env act capacityPerTask start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r := combineGet {} tasks
  r.errors.forM logImportFailure
  r.tree.toLazy.dropKeys droppedKeys

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
    BaseIO (State α) := do
  let modName := env.header.mainModule
  env.constants.map₂.foldlM (addConstToPreDiscrTree cctx env modName act) { ngen }

/-- Create a discriminator tree for current module declarations. -/
def createModuleDiscrTree
    (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (droppedKeys : List (List RefinedDiscrTree.Key)) :
    MetaM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { errors, tree, .. } ← createLocalPreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  tree.toLazy.dropKeys droppedKeys

/--
Creates reference for lazy discriminator tree that only contains this module's definitions.
-/
def createModuleTreeRef (act : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (droppedKeys : List (List RefinedDiscrTree.Key)) : MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (←getOptions) $ do
    let t ← createModuleDiscrTree act droppedKeys
    pure { ref := ← IO.mkRef t }
