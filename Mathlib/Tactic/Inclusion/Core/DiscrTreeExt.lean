/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Init
public meta import Lean.Meta.DiscrTree

/-!
# Discrimination-tree-indexed environment extensions

This file provides an API for scoped environment extensions whose declarations are indexed by
elaborated expression patterns in a `DiscrTree`.

## Implimentation Notes

The inclusion tactic uses two seperate types of `DiscrTree` indexed environment extensions. These
have nearly identical APIs except the stored values are different types (one is `InclusionExt`s
and the other is `HypothesisExt`s). This file essentially generalizes the `DiscrTree` valued
environment extension API from the implimentation for the `norm_num` tactic so that it can take
arbitrary values.

## TODO

Investigate the possibility of using this API for other tactics in Mathlib with `DiscrTree`
indexed environment extensions such as `norm_num` and `positivity`. This should perhaps be
part of a wider investigation into whether more API from the environment extensions of various
Mathlib tactics could be unified.

-/

public meta section

open Lean Elab Term Lean.Meta

namespace DiscrTreeExt

/-- Evaluate `declName` as a value of type `α`, checking that its Lean type is `typeName`. -/
def evalDecl (α : Type) (typeName declName : Name) : ImportM α := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck α opts typeName declName

/-- The discrimination-tree paths and declaration name stored in an `.olean` entry. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- The state of a discrimination-tree environment extension. -/
structure State (α : Type) where
  /-- The discrimination tree of the extension. -/
  tree : DiscrTree α := {}
  deriving Inhabited

/-- A scoped environment extension containing declaration values indexed by expression patterns. -/
abbrev EnvExt (α : Type) := ScopedEnvExtension Entry (Entry × α) (State α)

variable {α : Type}

/-- Return the declaration values whose `DiscrTree` keys match `e`. -/
def State.getMatch (state : State α) (e : Expr) : MetaM (Array α) := state.tree.getMatch e

/-- Create a scoped environment extension whose declarations have type `typeName`. By default, the
environment extension is named after the declaration in which this function is called. -/
def initializeEnvExt (typeName : Name)
    (envExtName : Name := by exact decl_name%) : IO (EnvExt α) := do
  -- we prevent any deduplication in the DiscrTree
  have : BEq α := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    name := envExtName
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← evalDecl α typeName n)
    toOLeanEntry := (·.1)
    addEntry := fun state ((kss, _), ext) ↦
      { tree := insert kss ext state.tree }
  }

/-- Elaborate expression patterns into `DiscrTree` paths. -/
def elabExtKeys (patterns : Array Syntax) : CoreM (Array (Array DiscrTree.Key)) :=
  MetaM.run' <| patterns.mapM fun stx => do
    let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
      withReader ({ · with ignoreTCFailures := true }) do
        let e ← elabTerm stx none
        let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
        return e
    DiscrTree.mkPath e

end DiscrTreeExt
