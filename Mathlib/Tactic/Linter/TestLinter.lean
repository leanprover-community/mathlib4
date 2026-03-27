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
Gets the indices `i` (in ascending order) of the binders of a nested `.forallE`,
`(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`, such that
-  `p Aᵢ bi` is `true`, with `bi` the `biinderInfo`
- The rest of the type `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that
  `xᵢ : Aᵢ` is "unused".)

Note that the argument to `p` may have loose bvars. This is a performance optimization.

This function runs `cleanupAnnotations` on each expression before examining it.

We see through `let`s, and do not increment the index when doing so. This behavior is compatible
with `forallBoundedTelescope`.
-/
@[specialize p]
partial def _root_.Lean.Expr.getUnusedForallBinderIdxsWhere
    (p : BinderInfo → Expr → Bool) (e : Expr) : Array Nat :=
  go e 0 #[]
where
  /-- Inspects `body`, and if it is a `.forallE` of an instance with type `type` such that `p type`
  is `true` and the remainder of the type does not depend on it, pushes the `current` index onto
  the accumulated array. -/
  go (body : Expr) (current : Nat) (acc : Array Nat) : Array Nat :=
    match body.cleanupAnnotations with
    | .forallE _ type body bi => go body (current+1) <|
      if p bi type && !(body.hasLooseBVar 0) then
        acc.push current
      else
        acc
    /- See through `letE`, and just as in the interpretation of a bound provided to
    `forallBoundedTelescope`, do not increment the number of binders we've counted. -/
    | .letE _ _ _ body _ => go body current acc
    | _ => acc

/-- Does work. -/
def workLinter : Linter where
  run _ := do
    for t in ← getInfoTrees do
      for n in t.getDeclsByBody do
        unless ← liftCoreM <| Meta.isInstance n do continue
        let some info := (← getEnv).find? n | continue
        let impossibleIdxs := info.type.getUnusedForallBinderIdxsWhere fun bi _ =>
          !bi.isInstImplicit

initialize addLinter workLinter
