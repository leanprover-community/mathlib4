/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Lean.Meta.Tactic.Grind

/-!
# A `grind` propagator that normalizes morphism composition

This file installs a `grind` upward propagator on
`CategoryTheory.CategoryStruct.comp` that, every time `grind`
internalizes a composition `f ≫ g`, pushes the equality
`f ≫ g = (right-associated form with identity factors removed)`
back into the e-graph.

The reason this is a propagator rather than a set of `@[grind]`-tagged
lemmas: tagging `Category.assoc`, `Category.id_comp`, `Category.comp_id`
with `@[grind]` causes e-matching to instantiate `Category.assoc` once
per parenthesization of every composition chain — for a chain of
length `n` that is Catalan(n − 1) instantiations, each then attacked
by `id_comp` / `comp_id`. The e-graph blows up. A propagator that
commits to a single canonical representative per fresh composition
avoids the blowup: the normalized form is a fixed point of itself, so
the propagator only does work once per user-visible composition.

## Caveats

- "Identity factors" are detected *syntactically* by head symbol
  `CategoryStruct.id`. Opaque or reducible wrappers around `𝟙 _` are
  treated as atoms and will not be stripped.
- When a morphism's type does not `whnf` to a `Quiver.Hom` application
  (e.g. an irreducible user-defined morphism type) the propagator
  silently skips rather than throwing.
-/

@[expose] public section

namespace Mathlib.Tactic.CategoryTheory.GrindCatNorm

open Lean Meta

initialize registerTraceClass `grind.catNorm

/-- Returns `true` iff `e` is `𝟙 _`, i.e. `CategoryStruct.id _ _`. -/
def isIdMorphism (e : Expr) : Bool :=
  e.isAppOf ``CategoryTheory.CategoryStruct.id

/-- Cheap structural check: `e` is a `≫` already in right-associated
form with no identity factors.

A right-associated comp tree has shape `f ≫ (g ≫ (h ≫ ...))`: every
left argument is a non-comp non-identity. Identity-free means no leaf
is `𝟙 _`. -/
partial def isNormalizedComp (e : Expr) : Bool :=
  if e.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let f := e.appFn!.appArg!
    let g := e.appArg!
    if f.isAppOf ``CategoryTheory.CategoryStruct.comp || isIdMorphism f then
      false
    else if g.isAppOf ``CategoryTheory.CategoryStruct.comp then
      isNormalizedComp g
    else
      !isIdMorphism g
  else
    true

/-- Reduce `t` to the canonical `@Quiver.Hom V _ X Y` shape and return
`(X, Y)`. Returns `none` if `t` does not whnf to a `Quiver.Hom`
application — e.g. because of a non-reducible user-defined morphism
type, or because some implicit could not be elaborated. -/
def extractHomEndpoints (t : Expr) : MetaM (Option (Expr × Expr)) := do
  -- Reduce just far enough to expose a `Quiver.Hom` head — using default
  -- transparency so ordinary `def`-aliases unfold, but stopping at
  -- `Quiver.Hom` so we don't accidentally unfold the projection itself.
  let some t ← withDefault <| whnfUntil t ``Quiver.Hom | return none
  unless t.isAppOfArity ``Quiver.Hom 4 do return none
  let args := t.getAppArgs
  return some (args[2]!, args[3]!)

/-- Build the term `f ≫ g` given the two morphism arguments and a
"comp shell" `e0` from which we copy the `comp` head (with its
universe levels, category, and category-struct instance).

Returns `none` if the source/middle/target objects cannot be extracted
from `f`'s and `g`'s types — i.e. if either type fails to whnf to a
`Quiver.Hom` application. In that case the caller should skip rewriting. -/
def mkCompFromShell (e0 : Expr) (f g : Expr) : MetaM (Option Expr) := do
  let some (X', Y') ← extractHomEndpoints (← inferType f) | return none
  let some (_, Z') ← extractHomEndpoints (← inferType g) | return none
  let args := e0.getAppArgs
  let C := args[0]!
  let inst := args[1]!
  -- Reuse the original `comp` head from `e0` to preserve maximal sharing.
  return some (mkAppN e0.getAppFn #[C, inst, X', Y', Z', f, g])

/-- Normalize a morphism expression to right-associated identity-free
form. Returns `(e', proof?)` where:
- `e' = e` (semantically)
- `e'` is right-associated and identity-free
- `proof?` is `some p` with `p : e = e'`, or `none` if `e = e'` syntactically.
-/
partial def normalizeComp (e : Expr) : MetaM (Expr × Option Expr) := do
  unless e.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do
    return (e, none)
  -- e = a ≫ b
  let a := e.appFn!.appArg!
  let b := e.appArg!
  -- recurse on children first
  let (a', aProof?) ← normalizeComp a
  let (b', bProof?) ← normalizeComp b
  -- Build (potentially) an updated comp `a' ≫ b'` with proof e = a' ≫ b'.
  let (e1, e1Proof?) ← do
    if aProof?.isNone && bProof?.isNone then
      pure (e, none)
    else
      let some e1 ← mkCompFromShell e a' b' | return (e, none)
      -- proof: a ≫ b = a' ≫ b'
      let aP := aProof?.getD (← mkEqRefl a)
      let bP := bProof?.getD (← mkEqRefl b)
      -- e = `comp C inst X Y Z f g`, so e.appFn!.appFn! = `comp C inst X Y Z`,
      -- which is the binary function we are applying congruence to.
      let proof ← mkCongrArg₂ e.appFn!.appFn! aP bP
      pure (e1, some proof)
  -- Now consider `a' ≫ b'` (which is e1). Apply local rewrites.
  -- Identity left: 𝟙 X ≫ b' = b'
  if isIdMorphism a' then
    let p ← mkAppM ``CategoryTheory.Category.id_comp #[b']
    let proof ← combineProofs e1Proof? p
    return (b', some proof)
  -- Identity right: a' ≫ 𝟙 Y = a'
  if isIdMorphism b' then
    let p ← mkAppM ``CategoryTheory.Category.comp_id #[a']
    let proof ← combineProofs e1Proof? p
    return (a', some proof)
  -- Reassociation: (x ≫ y) ≫ b' = x ≫ (y ≫ b'), then recurse on x ≫ (y ≫ b')
  if a'.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let x := a'.appFn!.appArg!
    let y := a'.appArg!
    let p ← mkAppM ``CategoryTheory.Category.assoc #[x, y, b']
    -- new shape: x ≫ (y ≫ b')
    let some yb' ← mkCompFromShell e y b' | return (e1, e1Proof?)
    let some new ← mkCompFromShell e x yb' | return (e1, e1Proof?)
    -- now recursively normalize `new`
    let (newNorm, newNormProof?) ← normalizeComp new
    let combined ←
      match e1Proof?, newNormProof? with
      | none, none => pure p
      | some e1p, none => mkAppM ``Eq.trans #[e1p, p]
      | none, some np => mkAppM ``Eq.trans #[p, np]
      | some e1p, some np => do
        let t1 ← mkAppM ``Eq.trans #[e1p, p]
        mkAppM ``Eq.trans #[t1, np]
    return (newNorm, some combined)
  -- Otherwise, a' is a leaf and b' is either a leaf or already normalized comp.
  return (e1, e1Proof?)
where
  combineProofs (first : Option Expr) (second : Expr) : MetaM Expr := do
    match first with
    | none => return second
    | some p => mkAppM ``Eq.trans #[p, second]
  mkCongrArg₂ (f : Expr) (ha : Expr) (hb : Expr) : MetaM Expr := do
    -- Build a proof that f a b = f a' b' given ha : a = a', hb : b = b'.
    -- Use mkCongr: mkCongr (mkCongrArg f ha) hb gives f a b = f a' b'.
    let step1 ← mkCongrArg f ha
    mkCongr step1 hb

/-- The propagator body. -/
def catCompPropagatorImpl (e : Expr) : Grind.GoalM Unit := do
  trace[grind.catNorm] "fire on: {e}"
  unless e.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do return ()
  if isNormalizedComp e then
    trace[grind.catNorm] "  skip: already normalized"
    return ()
  let (e', proof?) ← normalizeComp e
  let some proof := proof? | return ()
  let e' ← Grind.shareCommon e'
  trace[grind.catNorm] "  normalized to: {e'}"
  let gen ← Grind.getGeneration e
  Grind.internalize e' gen (some e)
  Grind.pushEq e e' proof

initialize
  let name := ``CategoryTheory.CategoryStruct.comp
  Lean.Meta.Grind.registerBuiltinUpwardPropagator name catCompPropagatorImpl

end Mathlib.Tactic.CategoryTheory.GrindCatNorm
