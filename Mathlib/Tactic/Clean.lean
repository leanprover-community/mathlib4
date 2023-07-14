/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn, Michail Karatarakis
-/

import Lean

/-!
# `clean` tactic

Remove identity functions from a term.
-/

open Lean Meta Elab.Tactic

set_option autoImplicit false

namespace Lean.Expr

/-- List of names removed by `clean`. All these names must resolve to functions defeq `id`.
We use `` `hidden`` because `hidden` is not yet imported. -/
def cleanIds : List Name :=
[``Id, ``id, `hidden]

/-- Clean an expression by removing `id`s listed in `cleanIds`. -/
def clean (e : Expr) : Expr :=
  e.replace (fun e =>
   match e with
   | (app (app (const n _) _) e') =>
      if n ∈ cleanIds then some e' else none
   | (app (lam _ _ (bvar 0) _ ) e') => some e'
   | _ => none)

end Lean.Expr

/--
Remove identity functions from a term. These are normally
automatically generated with terms like `show t, from p` or
`(p : t)` which translate to some variant on `@id t p` in
order to retain the ty/-! # `classical` and `classical!` tactics -/
pe.
-/
elab "clean " t:term : tactic =>
withMainContext do
  closeMainGoalUsing (checkUnassigned := false) fun type => do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← elabTermEnsuringType t type
    logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
    return r.clean
