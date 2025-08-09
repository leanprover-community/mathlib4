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
condition given by `a: Fin 2 → ZMod N`. -/
def eisensteinSeries_MF {k : ℤ} {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm (Gamma N) k where
  toFun := eisensteinSeries_SIF a k
  slash_action_eq' := (eisensteinSeries_SIF a k).slash_action_eq'
  holo' := eisensteinSeries_SIF_MDifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [isCusp_SL2Z_subgroup_iff] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ ↦ isBoundedAtImInfty_eisensteinSeries_SIF a hk γ

end ModularForm
