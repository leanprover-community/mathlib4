/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot, Scott Morrison
-/
import Mathlib.Lean.Expr.Basic
-- TODO
-- import Tactic.Monotonicity

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic

/--
Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f := by
  intros x x' h,
  apply_fun g at h,
  exact H h
```
 -/
syntax (name := applyFun) "apply_fun " term (ppSpace location)? (" using " term)? : tactic

def applyFunHyp (f : Expr) (u : Option Expr) (h : FVarId) : TacticM Unit := do
  let d ← h.getDecl
  match d.type.getAppFnArgs with
  | (``Eq, #[_ty, e₁, e₂]) => sorry
  | (``LE.le, #[_ty, e₁, e₂]) => sorry
  | _ => throwError "apply_fun can only handle hypotheses of the form `a = b` or `a ≤ b`."

def applyFunTarget (f : Expr) (u : Option Expr) : TacticM Unit :=
  sorry

elab_rules : tactic | `(tactic| apply_fun $f $[$loc]? $[using $h]?) => do
  let f ← Tactic.elabTerm f none
  let h ← h.mapM (Tactic.elabTerm · none)
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := applyFunHyp f h)
    (atTarget := applyFunTarget f h)
    (failed := fun _ => throwError "apply_fun failed")
