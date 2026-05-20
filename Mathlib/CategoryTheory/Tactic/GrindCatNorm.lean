/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Lean.Meta.Tactic.Grind
public import Mathlib.Lean.Meta.Simp

/-!
# A `grind` propagator that normalizes morphism composition

This file installs a `grind` upward propagator on
`CategoryTheory.CategoryStruct.comp` that, every time `grind`
internalizes a composition `f ≫ g`, pushes the equality
`f ≫ g = (right-associated form with syntactic identity factors removed)`
back into the e-graph.

The reason this is a propagator rather than a set of `@[grind]`-tagged
lemmas: tagging `Category.assoc`, `Category.id_comp`, `Category.comp_id`
with `@[grind]` causes e-matching to instantiate `Category.assoc` once
per parenthesization of every composition chain — for a chain of
length `n` that is Catalan(n − 1) instantiations. The e-graph blows
up. Mathlib already has the runaway documented at
`Mathlib/CategoryTheory/Iso.lean:146`. A propagator that commits to a
single canonical representative per fresh composition avoids the
blowup: the normalized form is a fixed point of itself, so the
propagator only does work once per user-visible composition.

The rewrite itself is delegated to `simp` with a three-lemma simp
set; we only contribute the structural shortcut that recognises
already-normalised compositions and the glue that feeds the result
back into `grind`'s e-graph.

## Caveats

- Identity factors are detected *syntactically* by head symbol
  `CategoryStruct.id`. Opaque or reducible wrappers around `𝟙 _` are
  treated as atoms and will not be stripped at the shortcut layer
  (though they may still be normalised by `simp` if it can unfold them).
- If a composition's instance argument is `CategoryStruct` without a
  matching `Category` instance, the lemma applications fail; we catch
  this and silently skip the rewrite rather than aborting `grind`.
-/

@[expose] public section

namespace Mathlib.Tactic.CategoryTheory.GrindCatNorm

open Lean Meta

initialize registerTraceClass `grind.catNorm

/-- Returns `true` iff `e` is `𝟙 _`, i.e. `CategoryStruct.id _ _`. -/
def isIdMorphism (e : Expr) : Bool :=
  e.consumeMData.isAppOf ``CategoryTheory.CategoryStruct.id

/-- Cheap structural check: `e` is a `≫` already in right-associated
form with no identity factors. We use this to short-circuit the
propagator on terms that are already normalised, avoiding the cost of
invoking `simp` on every internalised sub-composition.

A right-associated identity-free comp tree has shape
`f ≫ (g ≫ (h ≫ ...))`: every left argument is a non-comp non-identity,
and the last right argument is a non-identity. -/
partial def isNormalizedComp (e : Expr) : Bool :=
  let e := e.consumeMData
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

/-- The propagator body. Fires on every `CategoryStruct.comp` term
`grind` internalises; if `e` is not already in right-associated
identity-free form, asks `simp` to normalise it and pushes the
resulting equality into the e-graph. -/
def catCompPropagatorImpl (e : Expr) : Grind.GoalM Unit := do
  unless e.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do return ()
  if isNormalizedComp e then return ()
  trace[grind.catNorm] "normalising: {e}"
  -- `simp` may fail if the necessary `Category` instance cannot be
  -- synthesised (e.g. for a bare `CategoryStruct` term). In that case
  -- we silently skip rather than aborting `grind`.
  let r ← try
    simpOnlyNames
      [``CategoryTheory.Category.id_comp,
       ``CategoryTheory.Category.comp_id,
       ``CategoryTheory.Category.assoc] e
      (config := { decide := false })
  catch _ => return ()
  if Lean.Meta.Sym.isSameExpr e r.expr then return ()
  let e' ← Grind.shareCommon r.expr
  let proof ← r.getProof' e
  trace[grind.catNorm] "  ↦ {e'}"
  let gen ← Grind.getGeneration e
  Grind.internalize e' gen (some e)
  Grind.pushEq e e' proof

initialize
  let name := ``CategoryTheory.CategoryStruct.comp
  Lean.Meta.Grind.registerBuiltinUpwardPropagator name catCompPropagatorImpl

end Mathlib.Tactic.CategoryTheory.GrindCatNorm
