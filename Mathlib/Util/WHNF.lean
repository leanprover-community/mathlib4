/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init

/-!
# WHNF with configuration options

This file provides `Lean.Meta.whnfWithConfig`, a variant of the core function `Lean.Meta.whnf` which
takes a config option of type `Lean.Meta.WhnfCoreConfig`, allowing `iota`, `beta`, projection,
`zeta` and `zetaDelta` reduction to be turned on or off explicitly.
-/

namespace Lean.Meta

instance : BEq WhnfCoreConfig :=
  { beq := fun c1 c2 =>
    c1.iota == c2.iota && c1.beta == c2.beta && c1.proj == c2.proj && c1.zeta == c2.zeta
    && c1.zetaDelta == c2.zetaDelta }

@[inline] private def useWHNFCache (e : Expr) (config : WhnfCoreConfig := {}) : MetaM Bool := do
  -- We cache only closed terms without expr metavars.
  -- Potential refinement: cache if `e` is not stuck at a metavariable
  if e.hasFVar || e.hasExprMVar || (← read).canUnfold?.isSome then
    return false
  else
    match (← getConfig).transparency with
    | .default | .all => return config == {} -- do not cache if using a nonstandard whnf config
    | _        => return false

@[inline] private def cached? (useCache : Bool) (e : Expr) : MetaM (Option Expr) := do
  if useCache then
    match (← getConfig).transparency with
    | .default => return (← get).cache.whnfDefault.find? e
    | .all     => return (← get).cache.whnfAll.find? e
    | _        => unreachable!
  else
    return none

private def cache (useCache : Bool) (e r : Expr) : MetaM Expr := do
  if useCache then
    match (← getConfig).transparency with
    | .default => modify fun s => { s with cache.whnfDefault := s.cache.whnfDefault.insert e r }
    | .all     => modify fun s => { s with cache.whnfAll     := s.cache.whnfAll.insert e r }
    | _        => unreachable!
  return r

/-- Compute the "weak head-normal form" of an expression.  This is a variant of the core function
`Lean.Meta.whnf` which takes a config option of type `Lean.Meta.WhnfCoreConfig`, allowing `iota`,
`beta`, projection, `zeta` and `zetaDelta` reduction to be turned on or off explicitly. -/
partial def whnfWithConfig (e : Expr) (config : WhnfCoreConfig := {}) : MetaM Expr :=
  let k := fun e => do
    let useCache ← useWHNFCache e config
    match (← cached? useCache e) with
    | some e' => pure e'
    | none    =>
      withTraceNode `Meta.whnf (fun _ => return m!"Non-easy whnf: {e}") do
        checkSystem "whnf"
        let e' ← whnfCore e config
        match (← reduceNat? e') with
        | some v => cache useCache e v
        | none   =>
          match (← reduceNative? e') with
          | some v => cache useCache e v
          | none   =>
            match (← unfoldDefinition? e') with
            | some e'' => cache useCache e (← whnfWithConfig e'' config)
            | none => cache useCache e e'
  withIncRecDepth <| whnfEasyCases e k config

end Lean.Meta
