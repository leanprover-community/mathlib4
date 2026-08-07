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

Installs a `grind` upward propagator on `CategoryTheory.CategoryStruct.comp`
that, every time `grind` internalizes a composition `f ≫ g`, pushes the
equality `f ≫ g = (right-associated form with identity factors removed)`
back into the e-graph.

The reason this is a propagator rather than a set of `@[grind]`-tagged
lemmas: tagging `Category.assoc`, `Category.id_comp`, `Category.comp_id`
with `@[grind]` causes e-matching to instantiate `Category.assoc` once
per parenthesization of every composition chain — for a chain of length
`n` that is Catalan(n − 1) instantiations. The e-graph blows up. (Mathlib
already has the runaway documented at
`Mathlib/CategoryTheory/Iso.lean:146`.) A propagator that commits to a
single canonical representative per fresh composition avoids the blowup:
the normalized form is a fixed point of itself, so the propagator only
does work once per user-visible composition.

The rewrite is delegated to `simp` with a three-lemma simp set
(`Category.id_comp`, `Category.comp_id`, `Category.assoc`); we just feed
simp's result back into `grind`'s e-graph.
-/

@[expose] public section

namespace Mathlib.Tactic.CategoryTheory.GrindCatNorm

open Lean Meta

initialize registerTraceClass `grind.catNorm

/-- Cheap syntactic check: `e` is `f ≫ g` already in right-associated
form with no `𝟙 _` factors. Used to short-circuit before invoking simp. -/
partial def isNormal (e : Expr) : Bool :=
  match_expr e with
  | CategoryTheory.CategoryStruct.comp _ _ _ _ _ l r =>
    !l.isAppOf ``CategoryTheory.CategoryStruct.comp &&
    !l.isAppOf ``CategoryTheory.CategoryStruct.id &&
    !r.isAppOf ``CategoryTheory.CategoryStruct.id &&
    (!r.isAppOf ``CategoryTheory.CategoryStruct.comp || isNormal r)
  | _ => true

/-- The propagator body. -/
def catCompPropagatorImpl (e : Expr) : Grind.GoalM Unit := do
  unless e.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do return ()
  if isNormal e then return ()
  -- `simp` may throw if no `Category` instance is available for the
  -- composition's `CategoryStruct`; we silently skip in that case but
  -- trace the exception so future regressions aren't invisible.
  let r ← try
    simpOnlyNames
      [``CategoryTheory.Category.id_comp,
       ``CategoryTheory.Category.comp_id,
       ``CategoryTheory.Category.assoc] e (config := { decide := false })
  catch ex =>
    trace[grind.catNorm] "skipped: {ex.toMessageData}"
    return ()
  if Lean.Meta.Sym.isSameExpr e r.expr then return ()
  trace[grind.catNorm] "{e} ↦ {r.expr}"
  let e' ← Grind.shareCommon r.expr
  let proof ← r.getProof' e
  let gen ← Grind.getGeneration e
  Grind.internalize e' gen (some e)
  Grind.pushEq e e' proof

initialize
  let name := ``CategoryTheory.CategoryStruct.comp
  Lean.Meta.Grind.registerBuiltinUpwardPropagator name catCompPropagatorImpl

end Mathlib.Tactic.CategoryTheory.GrindCatNorm
