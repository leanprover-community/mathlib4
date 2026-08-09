/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Module
public meta import Mathlib.Tactic.Ring.RingNF

/-! # `module_nf` tactic -/

public meta section

open Lean hiding Module
open Qq Parser.Tactic Elab.Tactic Meta

namespace Mathlib.Tactic.ModuleNF

def evalExpr (postCtx : Simp.Context) (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp
  let ⟨_, M, e⟩ ← inferTypeQ' e
  let iM : Q(AddCommMonoid $M) ← synthInstanceQ q(AddCommMonoid $M)
  let r ← Mathlib.Tactic.Module.eval iM postCtx e
  if r.proof?.isNone then failure
  return r

/-- The `Simp.Context` used by `ModuleNF.cleanup` -/
def cleanupCtx : MetaM Simp.Context := do
  let thms ← [``one_smul, ``zero_smul, ``add_zero, ``zero_add, ``mul_one,
    ``one_mul].foldlM (·.addConst ·) ({} : SimpTheorems)
  Simp.mkContext { failIfUnchanged := false }
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Clean up a rewritten expression with the `cleanupCtx` lemmas. -/
def cleanup (ctx : Simp.Context) (r : Simp.Result) : MetaM Simp.Result := do
  r.mkEqTrans (← Simp.main r.expr ctx (methods := Simp.mkDefaultMethodsCore {})).1

/-- Run the `module_nf` rewrite on the expression `e` -/
def moduleNFCore (s : IO.Ref AtomM.State) (e : Expr) : ReaderT Simp.Context MetaM Simp.Result := do
  let postCtx ← read
  let cleanCtx ← cleanupCtx
  AtomM.recurse s { red := .instances } (wellBehavedDischarge := true) (evalExpr postCtx)
    (cleanup cleanCtx) e

/-- Normalization tactic for module expressions, it writes each linear combination of atoms as
`c₁ • x₁ + c₂ • x₂ + ... + cₙ • xₙ`, collecting the scalars of repeated atoms and normalizing them
with `ring_nf`.

Like `match_scalars` and `module`, linear combinations are parsed from `+`, `-`, `•` and `0`,
other subexpressions (including variables) are atoms, and the scalars are interpreted in the
largest scalar ring encountered (see `match_scalars` for the requirements on scalar types).

Examples:
```
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (a + b) • x := by
  module_nf

example [AddCommMonoid V] (x y : V) : x + (y + x) = x + x + y := by
  module_nf  -- both sides normalize to `2 • x + y`

example [AddCommMonoid M] [CommSemiring R] [Module R M] (f : M → M) (a b : R) (x : M) :
    f (a • x + b • x) = f ((a + b) • x) := by
  module_nf  -- rewrites under `f`

example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M)
    (h : a • x + b • x = 0) : (b + a) • x = 0 := by
  module_nf at h ⊢
  exact h
```
-/
elab (name := moduleNF) "module_nf" loc:(location)? : tactic => do
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let postCtx ← Mathlib.Tactic.Module.postprocessCtx
  transformAtNondepPropLocation (moduleNFCore s) "module_nf" loc .error false postCtx

end Mathlib.Tactic.ModuleNF

end
