/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.GSimpTheorems

public meta section

namespace Mathlib.Tactic.GSimp
open Lean Meta

/-- The result of simplifying some expression `e` with respect to some relation `r`. -/
structure Result where
  /-- The simplified version of `e` -/
  expr : Expr
  /-- A proof that `$e` relates to `$expr`.
  If `none`, the two expressions are assumed to be equal. -/
  proof? : Option Expr := none
  deriving Inhabited

/-- The cache associated to a relation. -/
structure CacheEntry where
  /-- Cached simplification results for rewriting left to right. -/
  cache : Std.HashMap Expr Result := {}
  /-- Cached simplification results for rewriting right to left. -/
  invCache : Std.HashMap Expr Result := {}
  /-- An optional proof that `∀ x, x ~ x`. -/
  rfl? : Option Expr := none
  /-- An optional proof that `∀ x y z, x ~ y → y ~ z → x ~ z`. -/
  trans? : Option Expr := none
  deriving Inhabited

def CacheEntry.insert (entry : CacheEntry) (inv : Bool) (e : Expr) (r : Result) : CacheEntry :=
  if inv then
    { entry with cache := entry.cache.insert e r }
  else
    { entry with invCache := entry.invCache.insert e r }

def CacheEntry.find? (entry : CacheEntry) (inv : Bool) (e : Expr) : Option Result :=
  if inv then entry.invCache[e]? else entry.cache[e]?

theorem imp_rfl {p : Prop} : p → p := id
theorem imp_trans {p q r : Prop} : (p → q) → (q → r) → p → r := flip Function.comp

abbrev CacheIndex := Nat

/-- The cache used by `gsimp` to store previous rewrites.

Note: in the implementation of `simp`, when the local context is changed by adding a new variable
to it, the cache is maintained, unless `wellBehavedDischarge := true`, or `contextual := true`.
Here, we always reset the cache when the local context changes.
As a result, the expressions appearing in the `DefEqMap` are always valid.
-/
-- TODO: cache the proofs of side-goals, just like how it's done in `field_simp`
structure Cache where
  /-- Map from relations to array index. -/
  relMap : Std.HashMap Expr CacheIndex := {}
  /-- For each relation, a proof of transitivity, and a cache of previously handled expressions.
  By convention, the first element in the array corresponds to the implication relation. -/
  entries : Array CacheEntry := #[{
    trans? := Expr.const ``imp_trans [], rfl? := Expr.const ``imp_rfl [] }]

-- -- Instead of returning none, this should modify the `entries` to create a new index.
-- def Cache.findIdx? (c : Cache) (rel : Expr) : Option CacheIndex :=
--   c.relMap[rel]?

def Cache.insert (c : Cache) (idx : CacheIndex) (inv : Bool) (e : Expr) (r : Result) : Cache :=
  { c with entries := c.entries.modify idx (·.insert inv e r)}

/-- The state of the `GSimpM` monad. -/
structure State where
  cache : Cache := {}
  numSteps : Nat := 0

/--
The configuration for `simp`.
Passed to `simp` using, for example, the `simp +contextual` or `simp (maxSteps := 100000)` syntax.

See also `Lean.Meta.Simp.neutralConfig` and `Lean.Meta.DSimp.Config`.
-/
structure Config where
  /--
  The maximum number of subexpressions to visit when performing simplification.
  The default is 100000.
  -/
  maxSteps : Nat  := Simp.defaultMaxSteps
  /--
  When `singlePass` is `true` (default: `false`),
  the simplifier runs through a single round of simplification,
  which consists of running pre-methods, recursing using congruence lemmas,
  and then running post-methods.
  Otherwise, when it is `false`, it iteratively applies this simplification procedure.
  -/
  singlePass : Bool := false
  /--
  If `failIfUnchanged` is `true` (default: `true`), then calls to `simp`, `dsimp`, or `simp_all`
  will fail if they do not make progress.
  -/
  failIfUnchanged   : Bool := true
  /--
  When `index` (default : `true`) is `false`, `simp` will only use the root symbol
  to find candidate `simp` theorems. It approximates Lean 3 `simp` behavior.
  -/
  index             : Bool := true


structure Context where
  config : Config
  gsimpTheorems : GSimpTheorems
  gcongrTheorems : GCongr.GCongrLemmas
  /-- The index in the array of caches that is relevant to the current relation. -/
  idx : CacheIndex
  /-- The type on which the current relation operates. -/
  relType : Expr
  /-- The current relation. Set to `none` if the relation is implication. -/
  rel : Option Expr
  /-- The name of the current relation. -/
  relName : Name
  /-- Whether we are using the relation in the reverse direction. -/
  inv : Bool := false


private opaque MethodsRefPointed : NonemptyType.{0}

def MethodsRef : Type := MethodsRefPointed.type

instance : Nonempty MethodsRef :=
  by exact MethodsRefPointed.property

/-- The monad used by `gsimp`. -/
abbrev GSimpM := ReaderT MethodsRef <| ReaderT Context StateRefT State MetaM

def getContext : GSimpM Context := readThe Context

def getGCongrTheorems : GSimpM GCongr.GCongrLemmas :=
  return (← getContext).gcongrTheorems

def getConfig : GSimpM Config :=
  return (← getContext).config

def getCacheEntry : GSimpM CacheEntry := do
  match (← get).cache.entries[(← getContext).idx]? with
  | some entry => return entry
  | none => throwError "Interal `gsimp` error: no cache entry"

def modifyCacheEntry (f : CacheEntry → CacheEntry) : GSimpM Unit := do
  let idx := (← getContext).idx
  modify fun s ↦ { s with cache.entries := s.cache.entries.modify idx f }

def getRelType : GSimpM Expr :=
  return (← getContext).relType

def getRelName : GSimpM Name :=
  return (← getContext).relName

def getRel : GSimpM (Option Expr) :=
  return (← getContext).rel

@[inline]
def withRel {α} (rel : Option Expr) (x : GSimpM α) : GSimpM α := do
  let (idx, relType, relName) ← match rel with
    | some rel =>
      let .forallE _ type _ _ ← whnf (← inferType rel)
        | throwError "expected a relation{indentExpr rel}"
      let .const name _ := rel.getAppFn
        | throwError "expected a constant application{indentExpr rel}"
      pure (← getCacheIdx rel, type, name)
    | none =>
      pure (0,.sort 0, `_Implies)
  withTheReader Context (fun ctx ↦ { ctx with idx, relType, rel, relName }) x
where
  getCacheIdx (rel : Expr) : GSimpM CacheIndex := do
    let c := (← get).cache
    if let some idx := c.relMap[rel]? then
      return idx
    else
      let idx := c.entries.size
      modify fun s ↦ { s with
        cache.entries := s.cache.entries.push {}
        cache.relMap := s.cache.relMap.insert rel idx }
      return idx

def isInv : GSimpM Bool :=
  return (← getContext).inv

@[inline]
def withContra {α} (isContra : Bool) (x : GSimpM α) : GSimpM α :=
  if isContra then
    withTheReader Context (fun ctx ↦ { ctx with inv := !ctx.inv }) x
  else
    x

@[inline] def withFreshCache {α} (x : GSimpM α) : GSimpM α := do
  let cacheSaved := (← get).cache
  modify fun s => { s with cache := {} }
  try x finally modify fun s => { s with cache := cacheSaved }


/-- Get a proof of `∀ x, x ~ x`. -/
def getRfl : GSimpM Expr := do
  let entry ← getCacheEntry
  if let some proof := entry.rfl? then
    return proof
  let some rel ← getRel | unreachable!
  let proof ← mkAppOptM ``refl #[← getRelType, rel, none]
  modifyCacheEntry ({ · with rfl? := proof })
  return proof

/-- Get a proof of `∀ x y z, x ~ y → y ~ z → x ~ z`. -/
def getTrans : GSimpM Expr := do
  let entry ← getCacheEntry
  if let some proof := entry.trans? then
    return proof
  let some rel ← getRel | unreachable!
  let proof ← mkAppOptM ``IsTrans.trans #[← getRelType, rel, none]
  modifyCacheEntry ({ · with trans? := proof })
  return proof

def Result.getProof (r : Result) : GSimpM Expr := do
  match r.proof? with
  | some p => return p
  | none => return .app (← getRfl) r.expr

/-- `trans` is assumed to have type `∀ a b c, a ~ b → b ~ c → a ~ c`. -/
def Result.mkTrans (e : Expr) (r₁ r₂ : Result) :
    GSimpM Result := do
  match r₁.proof? with
  | none => return r₂
  | some p₁ => match r₂.proof? with
    | none => return { r₂ with proof? := p₁ }
    | some p₂ =>
      if ← isInv then
        return { r₂ with proof? := mkApp5 (← getTrans) r₂.expr r₁.expr e p₂ p₁ }
      else
        return { r₂ with proof? := mkApp5 (← getTrans) e r₁.expr r₂.expr p₁ p₂ }

/-- `symmRel` is assumed to have type `∀ a b, a ~ b → b ~ a`. -/
def mkSymm (e symmRel : Expr) (r : Result) : GSimpM Result := do
  match r.proof? with
  | none => return r
  | some p =>
    if ← isInv then
      return { r with proof? := mkApp3 symmRel r.expr e p}
    else
      return { r with proof? := mkApp3 symmRel e r.expr p }

/--
Result type for a simplification procedure. We have `pre` and `post` simplification procedures.
-/
inductive Step where
  /--
  For `pre` procedures, it returns the result without visiting any subexpressions.

  For `post` procedures, it returns the result.
  -/
  | done (r : Result)
  /--
  For `pre` procedures, the resulting expression is passed to `pre` again.

  For `post` procedures, the resulting expression is passed to `pre` again IF
  `Simp.Config.singlePass := false` and resulting expression is not equal to initial expression.
  -/
  | visit (e : Result)
  /--
  For `pre` procedures, continue transformation by visiting subexpressions, and then
  executing `post` procedures.

  For `post` procedures, this is equivalent to returning `visit`.
  -/
  | continue (e? : Option Result := none)
  deriving Inhabited

/--
A generalized simplification procedure. Recall that we have `pre` and `post` procedures.
See `Step`.
-/
abbrev GSimproc := Expr → GSimpM Step

structure Methods where
  pre : GSimproc := fun _ => return .continue
  post : GSimproc := fun e => return .done { expr := e }
  discharge? : Expr → MetaM (Option Expr) := fun _ => return none
  deriving Inhabited

unsafe def Methods.toMethodsRefImpl (m : Methods) : MethodsRef :=
  unsafeCast m

@[implemented_by Methods.toMethodsRefImpl]
opaque Methods.toMethodsRef (m : Methods) : MethodsRef

unsafe def MethodsRef.toMethodsImpl (m : MethodsRef) : Methods :=
  unsafeCast m

@[implemented_by MethodsRef.toMethodsImpl]
opaque MethodsRef.toMethods (m : MethodsRef) : Methods

def getMethods : GSimpM Methods :=
  return MethodsRef.toMethods (← read)

def pre (e : Expr) : GSimpM Step := do
  (← getMethods).pre e

def post (e : Expr) : GSimpM Step := do
  (← getMethods).post e


def GSimpM.run {α} (ctx : Context) (s : State := {}) (methods : Methods := {}) (k : GSimpM α) :
    MetaM α := do
  withReducible do
    k methods.toMethodsRef ctx |>.run' s

-- def defaultMethods : Methods where
--   mkMethods simprocs dischargeDefault? (wellBehavedDischarge := true)


end Mathlib.Tactic.GSimp
