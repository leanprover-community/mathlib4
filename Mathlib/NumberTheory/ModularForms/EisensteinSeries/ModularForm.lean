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
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Matrix
  SlashInvariantForm

open scoped Topology BigOperators Nat Classical MatrixGroups

namespace EisensteinSeries

def eisensteinSeries_MF {k : ℤ} {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm (Gamma N) k where
  toFun := eisensteinSeries_SIF a k
  slash_action_eq' := (eisensteinSeries_SIF a k).slash_action_eq'
  holo' := eisensteinSeries_SIF_MDifferentiable k a hk
  bdd_at_infty' := eisensteinSeries_IsBoundedAtImInfty a k hk
