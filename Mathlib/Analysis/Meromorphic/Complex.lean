/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Meromorphic complex functions

## Main statements

* `MeromorphicOn.Gamma`: The Gamma function is meromorphic.
* `MeromorphicOn.hurwitzZeta`: The Hurwitz zeta function is meromorphic.
* `MeromorphicOn.riemannZeta`: The Riemann zeta function is meromorphic.
-/


open Set Complex Filter Function HurwitzZeta

open scoped Topology

lemma Complex.meromorphicAt_of_differentiable_on_punctured_nhds_of_exists_tendsto_sub_pow_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (ht : ∃ (n : ℕ) (r : E), Tendsto (fun s : ℂ => (s - c) ^ n • f s) (𝓝[≠] c) (𝓝 r)) :
    MeromorphicAt f c := by
  obtain ⟨n, r, ht⟩ := ht
  use n + 1
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hd] with s hd'; fun_prop
  · conv => arg 1; equals update (fun s : ℂ => (s - c) ^ (n + 1) • f s) c 0 => simp
    rw [continuousAt_update_same]
    replace ht := ((tendsto_id.sub_const c).mono_left nhdsWithin_le_nhds).prodMk ht
    simp only [id_eq, sub_self, ← nhds_prod_eq] at ht
    simpa [pow_succ', mul_smul] using Tendsto.comp continuous_smul.continuousAt ht

lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

/-- The Gamma function is meromorphic. -/
lemma MeromorphicOn.Gamma : MeromorphicOn Gamma univ :=
  MeromorphicNFOn.Gamma.meromorphicOn

/-- The Hurwitz zeta function is meromorphic. -/
lemma MeromorphicOn.hurwitzZeta (a : UnitAddCircle) : MeromorphicOn (hurwitzZeta a) univ := by
  simp only [MeromorphicOn, mem_univ, forall_const]
  intro s
  by_cases hs : s = 1
  case neg =>
    apply AnalyticAt.meromorphicAt
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hs] with s hs
    exact differentiableAt_hurwitzZeta a hs
  subst hs
  apply meromorphicAt_of_differentiable_on_punctured_nhds_of_exists_tendsto_sub_pow_smul
  · filter_upwards [eventually_mem_nhdsWithin] with s hs; exact differentiableAt_hurwitzZeta a hs
  · use 1, 1; simpa using HurwitzZeta.hurwitzZeta_residue_one a

/-- The Riemann zeta function is meromorphic. -/
lemma MeromorphicOn.riemannZeta : MeromorphicOn riemannZeta univ :=
  hurwitzZeta_zero ▸ MeromorphicOn.hurwitzZeta 0
