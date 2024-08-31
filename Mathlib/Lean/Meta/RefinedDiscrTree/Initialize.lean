import Mathlib.Lean.Meta.RefinedDiscrTree.Evaluate
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

private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry α) → Array (LazyEntry α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root.find? k with
  | .none =>
    let root := root.insert k tries.size
    { root, tries := tries.push (f #[]) }
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

/-- Information generation from imported modules. -/
private structure ImportData where
  errors : IO.Ref (Array ImportFailure)

private def ImportData.new : BaseIO ImportData := do
  let errors ← IO.mkRef #[]
  pure { errors }

private structure Cache where
  ngen : NameGenerator
  core : Lean.Core.Cache
  meta : Lean.Meta.Cache

private def Cache.empty (ngen : NameGenerator) : Cache := { ngen := ngen, core := {}, meta := {} }

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
    (d : ImportData)
    (cacheRef : IO.Ref Cache)
    (tree : PreDiscrTree α)
    (act : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (name : Name) (constInfo : ConstantInfo) : BaseIO (PreDiscrTree α) := do
  if constInfo.isUnsafe then return tree
  if blacklistInsertion env name then return tree
  let { ngen, core := core_cache, meta := meta_cache } ← cacheRef.get
  let mstate : Meta.State := { cache := meta_cache }
  cacheRef.set (Cache.empty ngen)
  let ctx : Meta.Context := { config := { transparency := .reducible } }
  let cm := (act name constInfo).run ctx mstate
  let cstate : Core.State := {env, cache := core_cache, ngen}
  match ← (cm.run cctx cstate).toBaseIO with
  | .ok ((a, ms), cs) =>
    cacheRef.set { ngen := cs.ngen, core := cs.cache, meta := ms.cache }
    pure <| a.foldl (fun t (key, entry) => t.push key entry) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e
    }
    d.errors.modify (·.push i)
    pure tree


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

private def toFlat (d : ImportData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← d.errors.swap #[]
  pure ⟨tree, de⟩

private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (d : ImportData)
    (cacheRef : IO.Ref Cache)
    (tree : PreDiscrTree α)
    (mname : Name)
    (mdata : ModuleData)
    (i : Nat := 0) : BaseIO (PreDiscrTree α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo  := mdata.constants[i]!
    let tree ← addConstToPreDiscrTree cctx env mname d cacheRef tree act name constInfo
    loadImportedModule cctx env act d cacheRef tree mname mdata (i+1)
  else
    pure tree

private def createImportedEnvironmentInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (start stop : Nat) : BaseIO (InitResults α) := do
      let cacheRef ← IO.mkRef (Cache.empty ngen)
      go (← ImportData.new) cacheRef {} start stop
where
  go (d : ImportData) (cacheRef : IO.Ref Cache) (tree : PreDiscrTree α) (start stop : Nat) :
      BaseIO (InitResults α) := do
    if start < stop then
      let mname := env.header.moduleNames[start]!
      let mdata := env.header.moduleData[start]!
      let tree ← loadImportedModule cctx env act d cacheRef tree mname mdata
      go d cacheRef tree (start+1) stop
    else
      toFlat d tree
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
    (act : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (droppedKeys : List (List RefinedDiscrTree.Key))
    (constantsPerTask : Nat := 1000) :
    MetaM (RefinedDiscrTree α) := do
  let n := env.header.moduleData.size
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go ngen tasks start cnt idx := do
      if h : idx < env.header.moduleData.size then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (createImportedEnvironmentInitResults cctx childNGen env act start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < n then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportedEnvironmentInitResults cctx childNGen env act start n).asTask
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
    (d : ImportData)
    (act : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α))) :
    BaseIO (PreDiscrTree α) := do
  let modName := env.header.mainModule
  let cacheRef ← IO.mkRef (Cache.empty ngen)
  env.constants.map₂.foldlM (init := {}) fun tree name cInfo =>
    addConstToPreDiscrTree cctx env modName d cacheRef tree act name cInfo

/-- Create a discriminator tree for current module declarations. -/
def createModuleDiscrTree
    (entriesForConst : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (droppedKeys : List (List RefinedDiscrTree.Key)) :
    MetaM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let d ← ImportData.new
  let ctx ← readThe Core.Context
  let t ← createLocalPreDiscrTree ctx ngen env d entriesForConst
  (← d.errors.get).forM logImportFailure
  t.toLazy.dropKeys droppedKeys

/--
Creates reference for lazy discriminator tree that only contains this module's definitions.
-/
def createModuleTreeRef (entriesForConst : Name → ConstantInfo → MetaM (Array (Key × LazyEntry α)))
    (droppedKeys : List (List RefinedDiscrTree.Key)) : MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (←getOptions) $ do
    let t ← createModuleDiscrTree entriesForConst droppedKeys
    pure { ref := ← IO.mkRef t }
