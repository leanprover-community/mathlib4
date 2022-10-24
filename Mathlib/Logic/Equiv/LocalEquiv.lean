/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Frédéric Dupuis, Heather Macbeth
-/

import Mathlib.Init.Logic
import Mathlib.Init.Set
import Mathlib.Logic.Equiv.MfldSimpsAttr
import Mathlib.Tactic.Core

open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`LocalEquiv`, `LocalHomeomorph`, etc).

This is in a separate file from `Mathlib.Logic.Equiv.MfldSimpsAttr` because attributes need a new
file to become functional.
-/

namespace Tactic.MfldSetTac

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another. -/
elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try (simp only [*, mfld_simps] at h_my_y; simp only [*, mfld_simps]))))
  | (``Subset, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try (simp only [*, mfld_simps] at h_my_y; simp only [*, mfld_simps]))))
  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply
