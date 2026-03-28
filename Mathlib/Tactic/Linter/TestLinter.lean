/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Elab.Command
import Mathlib.Lean.Elab.InfoTree

/-! For benching. -/

open Lean Elab Command

namespace Mathlib.Tactic

/--
Tests if any of the binders of `(x₀ : A₀) → (x₁ : A₁) → ⋯ → X` which satisfy `p Aᵢ bi` (with `bi` the `binderInfo`) are unused in the renainder of the type (i.e. in `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X`).

Note that the argument to `p` may have loose bvars. This is a performance optimization.

This function runs `cleanupAnnotations` on each type suffix `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X` before examining it.

We see through `let`s, and do not report if any of them are unused.
-/
@[specialize p]
partial def _root_.Lean.Expr.hasUnusedForallBinderIdxsWhere
    (p : BinderInfo → Expr → Bool) (e : Expr) : Bool :=
  match e.cleanupAnnotations with
  | .forallE _ type body bi =>
    p bi type && !(body.hasLooseBVar 0) || body.hasUnusedForallBinderIdxsWhere p
  /- See through `letE` -/
  | .letE _ _ _ body _ => body.hasUnusedForallBinderIdxsWhere p
  | _ => false

/-- quick lt -/
@[inline] protected def _root_.Lean.Position.qlt : Position → Position → Bool
  | ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ => l₁.blt l₂ || l₁.beq l₂ && c₁.blt c₂

/--
If `pos` is a `String.Pos`, then `getNamesFrom pos` returns the array of identifiers
for the names of the declarations whose syntax begins in position at least `pos`.
-/
def getDeclsAfterPos (env : Environment) (map : FileMap) (pos : String.Pos.Raw) : Array Name :=
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let pos := map.toPosition pos
  declRangeExt.getState (asyncMode := .local) env |>.foldl (init := #[])
    fun acc name { range .. } => if range.pos.qlt pos then acc else acc.push name

/-- Does work. -/
def workLinter : Linter where
  run cmd := do
    let some pos := cmd.getPos? | return
    for n in getDeclsAfterPos (← getEnv) (← getFileMap) pos do
      unless ← liftCoreM <| Meta.isInstance n do continue
      let some info := (← getEnv).find? n | continue
      let impossibleIdxs := info.type.hasUnusedForallBinderIdxsWhere fun bi _ =>
        !bi.isInstImplicit

initialize addLinter workLinter
