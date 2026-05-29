/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable

/-!
# Eisenstein series are Modular Forms

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are Modular Forms.

## TODO

Add q-expansions and prove that they are not all identically zero.
-/

@[expose] public section

noncomputable section

namespace ModularForm

open EisensteinSeries CongruenceSubgroup MatrixGroups

/-- This defines Eisenstein series as modular forms of weight `k`, level `Γ(N)` and congruence
condition given by `a : Fin 2 → ZMod N`. -/
def eisensteinSeriesMF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm Γ(N) k where
  toFun := eisensteinSeriesSIF a k
  slash_action_eq' := (eisensteinSeriesSIF a k).slash_action_eq'
  holo' := eisensteinSeriesSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ ↦ isBoundedAtImInfty_eisensteinSeriesSIF a hk γ

@[deprecated (since := "2026-02-10")] noncomputable alias eisensteinSeries_MF := eisensteinSeriesMF

/-- Normalised Eisenstein series of level 1 and weight `k`,
here they have been scaled by `1/2` since we sum over coprime pairs. -/
def E {k : ℕ} (hk : 3 ≤ k) : ModularForm 𝒮ℒ k :=
  ((1 / 2 : ℂ) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm

/-- The normalised level 1 Eisenstein series of weight 4. -/
abbrev E₄ : ModularForm 𝒮ℒ 4 := E (by norm_num : 3 ≤ 4)

/-- The normalised level 1 Eisenstein series of weight 6. -/
abbrev E₆ : ModularForm 𝒮ℒ 6 := E (by norm_num : 3 ≤ 6)

end ModularForm
