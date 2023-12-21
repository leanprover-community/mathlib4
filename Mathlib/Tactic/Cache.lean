/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
import Mathlib.Lean.Meta.DiscrTree

/-!
# Once-per-file cache for tactics

This file defines cache data structures for tactics
that are initialized the first time they are accessed.
Since Lean 4 starts one process per file,
these caches are once-per-file
and can for example be used to cache information
about the imported modules.

The `Cache α` data structure is
the most generic version we define.
It is created using `Cache.mk f`
where `f : MetaM α` performs
the initialization of the cache:
```
initialize numberOfImports : Cache Nat ← Cache.mk do
  (← getEnv).imports.size

-- (does not work in the same module where the cache is defined)
#eval show MetaM Nat from numberOfImports.get
```

The `DeclCache α` data structure computes
a fold over the environment's constants:
`DeclCache.mk empty f` constructs such a cache
where `empty : α` and `f : Name → ConstantInfo → α → MetaM α`.
The result of the constants in the imports is cached
between tactic invocations,
while for constants defined in the same file
`f` is evaluated again every time.
This kind of cache can be used e.g.
to populate discrimination trees.
-/

set_option autoImplicit true

open Lean Meta

namespace Mathlib.Tactic

/-- Once-per-file cache. -/
def Cache (α : Type) :=
  IO.Ref <| Sum (MetaM α) <|
    Task <| Except Exception α

instance : Nonempty (Cache α) :=
  inferInstanceAs <| Nonempty (IO.Ref _)

/-- Creates a cache with an initialization function. -/
def Cache.mk (init : MetaM α) : IO (Cache α) :=
  IO.mkRef <| Sum.inl init

/--
Access the cache.
Calling this function for the first time
will initialize the cache with the function
provided in the constructor.
-/
def Cache.get [Monad m] [MonadEnv m] [MonadLog m] [MonadOptions m] [MonadLiftT BaseIO m]
    [MonadExcept Exception m] (cache : Cache α) : m α := do
  let t ← match ← show BaseIO _ from ST.Ref.get cache with
    | Sum.inr t => pure t
    | Sum.inl init =>
      let env ← getEnv
      let fileName ← getFileName
      let fileMap ← getFileMap
      let options ← getOptions -- TODO: sanitize options?
      -- Default heartbeats to a reasonable value.
      -- otherwise librarySearch times out on mathlib
      -- TODO: add customization option
      let options := Core.maxHeartbeats.set options <|
        options.get? Core.maxHeartbeats.name |>.getD 1000000
      let res ← EIO.asTask do
        let metaCtx : Meta.Context := {}
        let metaState : Meta.State := {}
        let coreCtx : Core.Context := {options, fileName, fileMap}
        let coreState : Core.State := {env}
        pure (← ((init ‹_›).run ‹_› ‹_›).run ‹_›).1.1
      show BaseIO _ from cache.set (Sum.inr res)
      pure res
  match t.get with
    | Except.ok res => pure res
    | Except.error err => throw err

/--
Cached fold over the environment's declarations,
where a given function is applied to `α` for every constant.
-/
structure DeclCache (α : Type) where mk' ::
  /-- The cached data. -/
  cache : Cache α
  /-- Function for adding a declaration from the current file to the cache. -/
  addDecl : Name → ConstantInfo → α → MetaM α
  /-- Function for adding a declaration from the library to the cache.
  Defaults to the same behaviour as adding a declaration from the current file. -/
  addLibraryDecl : Name → ConstantInfo → α → MetaM α := addDecl
deriving Nonempty

/--
Creates a `DeclCache`.
The cached structure `α` is initialized with `empty`,
and then `addLibraryDecl` is called for every imported constant, and the result is cached.
After all imported constants have been added, we run `post`.
When `get` is called, `addDecl` is also called for every constant in the current file.
-/
def DeclCache.mk (profilingName : String) (empty : α)
    (addDecl : Name → ConstantInfo → α → MetaM α)
    (addLibraryDecl : Name → ConstantInfo → α → MetaM α := addDecl)
    (post : α → MetaM α := fun a => pure a) : IO (DeclCache α) := do
  let cache ← Cache.mk do
    profileitM Exception profilingName (← getOptions) do
    let mut a := empty
    for (n, c) in (← getEnv).constants.map₁.toList do
      a ← addLibraryDecl n c a
    return (← post a)
  pure { cache := cache, addDecl := addDecl }

/--
Access the cache.
Calling this function for the first time
will initialize the cache with the function
provided in the constructor.
-/
def DeclCache.get (cache : DeclCache α) : MetaM α := do
  let mut a ← cache.cache.get
  for (n, c) in (← getEnv).constants.map₂.toList do
    a ← cache.addDecl n c a
  return a

/--
A type synonym for a `DeclCache` containing a pair of discrimination trees.
The first will store declarations in the current file,
the second will store declarations from imports (and will hopefully be "read-only" after creation).
-/
@[reducible] def DiscrTreeCache (α : Type) : Type :=
  DeclCache (DiscrTree α true × DiscrTree α true)

/--
Build a `DiscrTreeCache`,
from a function that returns a collection of keys and values for each declaration.
-/
def DiscrTreeCache.mk [BEq α] (profilingName : String)
    (processDecl : Name → ConstantInfo → MetaM (Array (Array (DiscrTree.Key true) × α)))
    (post? : Option (Array α → Array α) := none)
    (init : Option (DiscrTree α true) := none) :
    IO (DiscrTreeCache α) :=
  let updateTree := fun name constInfo tree => do
    return (← processDecl name constInfo).foldl (fun t (k, v) => t.insertIfSpecific k v) tree
  let addDecl := fun name constInfo (tree₁, tree₂) => do
    return (← updateTree name constInfo tree₁, tree₂)
  let addLibraryDecl := fun name constInfo (tree₁, tree₂) => do
    return (tree₁, ← updateTree name constInfo tree₂)
  let post := match post? with
  | some f => fun (T₁, T₂) => return (T₁, T₂.mapArrays f)
  | none => fun T => pure T
  match init with
  | some t => return ⟨← Cache.mk (pure ({}, t)), addDecl, addLibraryDecl⟩
  | none => DeclCache.mk profilingName ({}, {}) addDecl addLibraryDecl (post := post)

/--
Get matches from both the discrimination tree for declarations in the current file,
and for the imports.

Note that if you are calling this multiple times with the same environment,
it will rebuild the discrimination tree for the current file multiple times,
and it would be more efficient to call `c.get` once,
and then call `DiscrTree.getMatch` multiple times.
-/
def DiscrTreeCache.getMatch (c : DiscrTreeCache α) (e : Expr) : MetaM (Array α) := do
  let (locals, imports) ← c.get
  -- `DiscrTree.getMatch` returns results in batches, with more specific lemmas coming later.
  -- Hence we reverse this list, so we try out more specific lemmas earlier.
  return (← locals.getMatch e).reverse ++ (← imports.getMatch e).reverse

/--
A structure that holds the cached discrimination tree,
and possibly a pointer to a memory region, if we unpickled the tree from disk.
-/
structure CachedData (α : Type) where
  pointer? : Option CompactedRegion
  cache : DiscrTreeCache α
deriving Nonempty
