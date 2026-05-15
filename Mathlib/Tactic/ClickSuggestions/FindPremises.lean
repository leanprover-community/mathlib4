/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.Rewrite
public import Mathlib.Tactic.ClickSuggestions.GRewrite
public import Mathlib.Tactic.ClickSuggestions.Apply
public import Mathlib.Tactic.ClickSuggestions.ApplyAt
public meta import Mathlib.Lean.FoldEnvironment
public meta import Mathlib.Lean.Meta.RefinedDiscrTree

/-!
# Generating a shortlist of candidate lemmas for suggestions

## Discrimination tree lookup

This file defines how to build and match with the discrimination trees, for premises that are
- imported
- from the current module
- local hypotheses

## Performance note

When importing all of mathlib, building the discrimination trees takes on the order of 10-15
seconds. This is because of two distinct performance bottlenecks:

1. Looping through the environment, and computing all of the discrimination tree entries is
  expensive, and is done in parallel to speed it up.
2. Building the final discrimination tree by inserting all of the computed entries is less
  expensive, but it cannot be done in parallel, because a single datastructure is being built.

These two bottlenecks cost about the same amount of time. Luckily, we can already start doing (2)
as soon as any of the parallel tasks from (1) have finished. So, we build the discrimination tree
(on the main thread) at the same time that the entries are being computed on various parallel
threads.
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta RefinedDiscrTree

/-- Return `true` if `s` and `t` are equal up to swapping the `MVarId`s. -/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some swaps
    | .sort _           , .sort _            => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some swaps
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
          some <| (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _                 , _                  => none
  else
    guard (t == s); some swaps


structure Entries where
  rw : Array (Key × LazyEntry × RwLemma) := #[]
  grw : Array (Key × LazyEntry × GrwLemma) := #[]
  app : Array (Key × LazyEntry × ApplyLemma) := #[]
  appAt : Array (Key × LazyEntry × ApplyAtLemma) := #[]

def insertEntry {α} (arr : Array (Key × LazyEntry × α)) (key : Expr) (a : α) :
    MetaM (Array (Key × LazyEntry × α)) := do
  let entries ← initializeLazyEntryWithEta key
  return entries.foldl (init := arr) fun arr (key, lazy) ↦ arr.push (key, lazy, a)

-- TODO: make `isBadMatch` more flexible, allowing the general equalities,
-- so that these lemmas are also in the discrimination tree.
-- We can then decide when/whether to actually show these lemmas.
/-- Determine whether the match `e` is too generic to be useful for insertion in
a discrimination tree of all imported theorems. -/
def isBadMatch (e : Expr) : Bool :=
  e.getAppFn.isMVar ||
  -- This extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r

public structure Choice where
  rw : Bool
  grw : Bool
  app : Bool
  appAt : Bool

def Choice.any (c : Choice) : Bool := c.rw || c.grw || c.app || c.appAt

/-- Return true if `declName` is automatically generated,
or otherwise unsuitable as a lemma suggestion. -/
def blacklist (env : Environment) (declName : Name) : Bool :=
  LazyDiscrTree.blacklistInsertion env declName ||
  declName.isMetaprogramming ||
  Linter.isDeprecated env declName ||
  match declName with | .str _ s => s == "eq_def" | _ => false

/-- Given a constant, compute what needs to be added to the various discrimination trees. -/
def Entries.addConst (choice : Choice) (env : Environment) (entries : Entries)
    (name : Name) (cinfo : ConstantInfo) : MetaM Entries := do
  if cinfo.isUnsafe then return entries
  if blacklist env name then return entries
  setMCtx {}
  let (xs, _, e) ← forallMetaTelescope cinfo.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    if !isBadMatch e then
      app ← insertEntry app e ⟨.const name⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType x
      if !isBadMatch e then
        appAt ← insertEntry appAt e ⟨.const name⟩
  if choice.rw || choice.grw then
    let mkApp2 rel lhs rhs := e | pure ()
    let .const relName _ := rel.getAppFn | pure ()
    -- rw
    if relName matches ``Iff | ``Eq then
      if choice.rw then
        if !isBadMatch lhs then
          rw ← insertEntry rw lhs ⟨.const name, false⟩
        if !isBadMatch rhs && (isBadMatch lhs || !isMVarSwap lhs rhs) then
          rw ← insertEntry rw rhs ⟨.const name, true⟩
    -- grw
    else
      if choice.grw then
        if !isBadMatch lhs then
          grw ← insertEntry grw lhs ⟨.const name, false, relName⟩
        if !isBadMatch rhs then
          grw ← insertEntry grw rhs ⟨.const name, true, relName⟩
  return { rw, grw, app, appAt }

/-- Given a free variable, compute what needs to be added to the various discrimination trees. -/
def Entries.addVar (choice : Choice) (entries : Entries) (decl : LocalDecl) : MetaM Entries := do
  let (xs, _, e) ← forallMetaTelescopeReducing (← instantiateMVars decl.type)
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    app ← insertEntry app e ⟨.fvar decl.fvarId⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType x
      appAt ← insertEntry appAt e ⟨.fvar decl.fvarId⟩
  -- rw
  if choice.rw then
    if let mkApp2 rel lhs rhs ← whnf e then
      if rel.getAppFn matches .const ``Iff _ | .const ``Eq _ then
        rw ← insertEntry rw lhs ⟨.fvar decl.fvarId, false⟩
        if !isMVarSwap lhs rhs then
          rw ← insertEntry rw rhs ⟨.fvar decl.fvarId, true⟩
  -- grw
  if choice.grw then
    if let mkApp2 rel lhs rhs := e.cleanupAnnotations then
      if let .const relName _ := rel.getAppFn then
        grw ← insertEntry grw lhs ⟨.fvar decl.fvarId, false, relName⟩
        grw ← insertEntry grw rhs ⟨.fvar decl.fvarId, true, relName⟩
  return { rw, grw, app, appAt }

public structure PreDiscrTrees where
  rw : PreDiscrTree RwLemma := {}
  grw : PreDiscrTree GrwLemma := {}
  app : PreDiscrTree ApplyLemma := {}
  appAt : PreDiscrTree ApplyAtLemma := {}

def PreDiscrTrees.append (pres : PreDiscrTrees) (maps : Entries) : PreDiscrTrees where
  rw := maps.rw.foldl (init := pres.rw) fun pre (key, e) ↦ pre.push key e
  grw := maps.grw.foldl (init := pres.grw) fun pre (key, e) ↦ pre.push key e
  app := maps.app.foldl (init := pres.app) fun pre (key, e) ↦ pre.push key e
  appAt := maps.appAt.foldl (init := pres.appAt) fun pre (key, e) ↦ pre.push key e

public initialize rwRef : IO.Ref (Option (RefinedDiscrTree RwLemma)) ← IO.mkRef none
public initialize grwRef : IO.Ref (Option (RefinedDiscrTree GrwLemma)) ← IO.mkRef none
public initialize appRef : IO.Ref (Option (RefinedDiscrTree ApplyLemma)) ← IO.mkRef none
public initialize appAtRef : IO.Ref (Option (RefinedDiscrTree ApplyAtLemma)) ← IO.mkRef none

/-- The configuration used when indexing into the discrimination tree, and when looking up in it.

We do not reduce projections so that e.g. `Fin.val_mk : ⟨m, h⟩.val = m` can be indexed properly.

TODO?: projections should be reduced inside implicit arguments,
because otherwise we may reject some valid matches.
-/
def librarySearchIndexConfig : Config where
  transparency := .reducible
  proj := .no

public def computeImportDiscrTrees (choice : Choice) : CoreM Unit := do
  let choice := {
    rw := choice.rw && (← rwRef.get).isNone
    grw := choice.grw && (← grwRef.get).isNone
    app := choice.app && (← appRef.get).isNone
    appAt := choice.appAt && (← appAtRef.get).isNone
  }
  unless choice.any do return
  let (tasks, errors) ←
    foldImportedDecls {} librarySearchIndexConfig (Entries.addConst choice (← getEnv))
  let pre : PreDiscrTrees ← MonadExcept.ofExcept <|
    tasks.foldlM (fun pre task ↦ pre.append <$> task.get) {}
  if choice.rw then setIfNone rwRef pre.rw.toRefinedDiscrTree
  if choice.grw then setIfNone grwRef pre.grw.toRefinedDiscrTree
  if choice.app then setIfNone appRef pre.app.toRefinedDiscrTree
  if choice.appAt then setIfNone appAtRef pre.appAt.toRefinedDiscrTree
  (← errors.get).forM logError
where
  setIfNone {α} (ref : IO.Ref (Option α)) (a : α) : BaseIO Unit := do
    if (← ref.get).isNone then
      ref.set a

public def computeModuleDiscrTrees (choice : Choice) (parentDecl? : Option Name) :
    CoreM PreDiscrTrees := do
  let env ← getEnv
  let (pre, errors) ← foldCurrFileDecls {} librarySearchIndexConfig fun entries name cinfo ↦ do
    if name == parentDecl? then return entries
    entries.addConst choice env name cinfo
  (← errors.get).forM logError
  return .append {} pre

public def computeLCtxDiscrTrees (choice : Choice) (fvarId? : Option FVarId) :
    MetaM PreDiscrTrees := withReducible do
  let mut entries : Entries := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && fvarId?.all (· != decl.fvarId) then
      entries ← entries.addVar choice decl
  return .append {} entries


public def getImportMatches {α} (ref : IO.Ref (Option (RefinedDiscrTree α)))
    (e : Expr) : MetaM (MatchResult α) := do
  let some tree ← ref.get |
    throwError "Internal click_suggestions error: discrimination tree was not computed."
  let (result, newTree) ← withConfig (fun _ ↦ librarySearchIndexConfig) do
    getMatch tree e false false
  Core.checkInterrupted
  ref.set newTree
  return result

public def getMatches {α} (tree : RefinedDiscrTree α) (e : Expr) : MetaM (MatchResult α) := do
  withConfig (fun _ ↦ librarySearchIndexConfig) do
    return (← getMatch tree e false false).1

end Mathlib.Tactic.ClickSuggestions
