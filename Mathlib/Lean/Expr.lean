/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn,
Thomas R. Murrills
-/
import Mathlib.Init
import Mathlib.Lean.Expr.Basic

/-!
# Additional utilities for `Expr`s
-/

namespace Lean.Expr

/--
Returns `true` if `type` is an application of a constant `decl` for which `p decl` is true, or a
forall with return type of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, decl ..` where
`p decl`).

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfConstP (p : Name → Bool) (type : Expr) : Bool :=
    match type.cleanupAnnotations.getAppFn' with
    | .const n _ => p n
    | .forallE _ _ body _ => isAppOrForallOfConstP p body
    | _ => false

/--
Returns `true` if `type` is an application of a constant `declName`, or a
forall with return type of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, declName ..`).

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfConst (declName : Name) (type : Expr) : Bool :=
  isAppOrForallOfConstP (· == declName) type

/--
Gets the indices `i` (in ascending order) of the binders of a nested `.forallE`,
`(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`, such that
- the binder `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
-  `p Aᵢ` is `true`
- The rest of the type `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that
  `xᵢ : Aᵢ` is "unused".)

Note that the argument to `p` may have loose bvars. This is a performance optimization.

This function runs `cleanupAnnotations` on each expression before examining it.

We see through `let`s, and do not increment the index when doing so. This behavior is compatible
with `forallBoundedTelescope`.
-/
partial def getUnusedForallInstanceBinderIdxsWhere (p : Expr → Bool) (e : Expr) :
    Array Nat :=
  go e 0 #[]
where
  /-- Inspects `body`, and if it is a `.forallE` of an instance with type `type` such that `p type`
  is `true` and the remainder of the type does not depend on it, pushes the `current` index onto
  the accummulated array. -/
  go (body : Expr) (current : Nat) (acc : Array Nat) : Array Nat :=
    match body.cleanupAnnotations with
    | .forallE _ type body bi => go body (current+1) <|
      if bi.isInstImplicit && p type && !(body.hasLooseBVar 0) then
        acc.push current
      else
        acc
    /- See through `letE`, and just as in the interpretation of a bound provided to
    `forallBoundedTelescope`, do not increment the number of binders we've counted. -/
    | .letE _ _ _ body _ => go body current acc
    | _ => acc

end Lean.Expr
