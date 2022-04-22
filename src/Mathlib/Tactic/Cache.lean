/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean
import Mathlib.Logic.Nonempty

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

open Lean Meta

namespace Tactic

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
def Cache.get [Monad m] [MonadEnv m] [MonadOptions m] [MonadLiftT BaseIO m] [MonadExcept Exception m]
    (cache : Cache α) : m α := do
  let t ← match ← show BaseIO _ from ST.Ref.get cache with
    | Sum.inr t => t
    | Sum.inl init =>
      let env ← getEnv
      let options ← getOptions -- TODO: sanitize options?
      -- Default heartbeats to a reasonable value.
      -- otherwise librarySearch times out on mathlib
      -- TODO: add customization option
      let options := Core.maxHeartbeats.set options <|
        options.get? Core.maxHeartbeats.name |>.getD 1000000
      let res ← EIO.asTask do
        let metaCtx : Meta.Context := {}
        let metaState : Meta.State := {}
        let coreCtx : Core.Context := {options}
        let coreState : Core.State := {env}
        (← ((init ‹_›).run ‹_› ‹_›).run ‹_›).1.1
      show BaseIO _ from cache.set (Sum.inr res)
      pure res
  match t.get with
    | Except.ok res => pure res
    | Except.error err => throw err

/--
Cached fold over the environment's declarations,
where a given function is applied to `α` for every constant.
-/
def DeclCache (α : Type) :=
  Cache α × (Name → ConstantInfo → α → MetaM α)

instance : Nonempty (DeclCache α) :=
  inferInstanceAs <| Nonempty (_ × _)

/--
Creates a `DeclCache`.
The cached structure `α` is initialized with `empty`,
and then `addDecl` is called for every constant in the environment.
Calls to `addDecl` for imported constants are cached.
-/
def DeclCache.mk (profilingName : String) (empty : α) (addDecl : Name → ConstantInfo → α → MetaM α) : IO (DeclCache α) := do
  let cache ← Cache.mk do
    profileitM Exception profilingName (← getOptions) do
    let mut a ← empty
    for (n, c) in (← getEnv).constants.map₁.toList do
      a ← addDecl n c a
    return a
  (cache, addDecl)

/--
Access the cache.
Calling this function for the first time
will initialize the cache with the function
provided in the constructor.
-/
def DeclCache.get (cache : DeclCache α) : MetaM α := do
  let mut a ← cache.1.get
  for (n, c) in (← getEnv).constants.map₂.toList do
    a ← cache.2 n c a
  return a
