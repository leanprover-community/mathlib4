/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable

/-!
# Eisenstein series are Modular Forms

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are Modular Forms.

# TODO

Add q-expansions and prove that they are not all identically zero.
-/

noncomputable section

namespace ModularForm

open EisensteinSeries CongruenceSubgroup

/-- This defines Eisenstein series as modular forms of weight `k`, level `Γ(N)` and congruence
condition given by `a : Fin 2 → ZMod N`. -/
def eisensteinSeries_MF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm (Gamma N) k where
  toFun := eisensteinSeries_SIF a k
  slash_action_eq' := (eisensteinSeries_SIF a k).slash_action_eq'
  holo' := eisensteinSeries_SIF_MDifferentiable hk a
  bdd_at_infty' := isBoundedAtImInfty_eisensteinSeries_SIF a hk

/-- Normalised Eisenstein series of level 1 and weight `k`,
here they have been scaled by `1/2` since we sum over coprime pairs. -/
noncomputable def E {k : ℕ} (hk : 3 ≤ k) : ModularForm Γ(1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF (mod_cast hk) 0

end ModularForm
