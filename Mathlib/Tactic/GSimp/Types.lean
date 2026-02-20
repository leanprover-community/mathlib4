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
  cache : Std.HashMap Expr Result := {}
  rfl? : Option Expr := none
  trans? : Option Expr := none
  deriving Inhabited

def CacheEntry.insert (entry : CacheEntry) (e : Expr) (r : Result) : CacheEntry :=
  { entry with cache := entry.cache.insert e r }

theorem imp_rfl (p : Prop) : p → p := id
theorem imp_trans (p q r : Prop) : (p → q) → (q → r) → p → r := flip Function.comp

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
  /-- Map for relations in the reverse direction. -/
  invRelMap : Std.HashMap Expr CacheIndex := {}
  /-- For each relation, a proof of transitivity, and a cache of previously handled expressions.
  By convention, the first element in the array corresponds to the implication relation. -/
  entries : Array CacheEntry := #[{
    trans? := Expr.const ``imp_trans [], rfl? := Expr.const ``imp_rfl [] }]



-- Instead of returning none, this should modify the `entries` to create a new index.
def Cache.findIdx? (c : Cache) (rel : Expr) (inv : Bool) : Option CacheIndex :=
  if inv then c.invRelMap[rel]? else c.relMap[rel]?

def Cache.find? (c : Cache) (idx : CacheIndex) (e : Expr) : Option Result :=
  c.entries[idx]!.cache[e]?

def Cache.insert (c : Cache) (idx : CacheIndex) (e : Expr) (r : Result) : Cache :=
  { c with entries := c.entries.modify idx (·.insert e r)}

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
  /-- The current relation. -/
  rel : Expr
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

def isInv : GSimpM Bool :=
  return (← getContext).inv

def withContra {α} (isContra : Bool) (x : GSimpM α) : GSimpM α :=
  if isContra then
    withTheReader Context (fun ctx ↦ { ctx with inv := !ctx.inv }) x
  else
    x

@[inline] def withFreshCache {α} (x : GSimpM α) : GSimpM α := do
  let cacheSaved := (← get).cache
  modify fun s => { s with cache := {} }
  try x finally modify fun s => { s with cache := cacheSaved }

def getCacheIdx (rel : Expr) : GSimpM CacheIndex := do
  let c := (← get).cache
  if ← isInv then
    if let some idx := c.invRelMap[rel]? then
      return idx
    else
      let idx := c.entries.size
      modify fun s ↦ { s with
        cache.entries := s.cache.entries.push {}
        cache.invRelMap := s.cache.invRelMap.insert rel idx }
      return idx
  else
    if let some idx := c.relMap[rel]? then
      return idx
    else
      let idx := c.entries.size
      modify fun s ↦ { s with
        cache.entries := s.cache.entries.push {}
        cache.relMap := s.cache.relMap.insert rel idx }
      return idx

def getRfl (rel : Expr) (idx : CacheIndex) : GSimpM Expr := do
  if let some rflPf := (← get).cache.entries[idx]!.rfl? then
    return rflPf
  mkAppOptM ``refl #[none, rel, none]

def getTrans (rel : Expr) (idx : CacheIndex) : GSimpM Expr := do
  if let some transPf := (← get).cache.entries[idx]!.trans? then
    return transPf
  mkAppOptM ``IsTrans.trans #[none, rel, none]

def Result.getProof (rel : Expr) (idx : CacheIndex) (r : Result) : GSimpM Expr := do
  match r.proof? with
  | some p => return p
  | none => return .app (← getRfl rel idx) r.expr

/-- `trans` is assumed to have type `∀ a b c, a ~ b → b ~ c → a ~ c`. -/
def Result.mkTrans (e rel : Expr) (idx : CacheIndex) (r₁ r₂ : Result) :
    GSimpM Result := do
  match r₁.proof? with
  | none => return r₂
  | some p₁ => match r₂.proof? with
    | none => return { r₂ with proof? := p₁ }
    | some p₂ =>
      let trans ← getTrans rel idx
      if ← isInv then
        return { r₂ with proof? := mkApp5 trans r₂.expr r₁.expr e p₂ p₁ }
      else
        return { r₂ with proof? := mkApp5 trans e r₁.expr r₂.expr p₁ p₂ }

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
