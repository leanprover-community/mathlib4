/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Meromorphic complex functions

## Main statements

* `MeromorphicOn.Gamma`: The Gamma function is meromorphic.
-/


open scoped Topology

public section

open Set Complex Filter Function HurwitzZeta

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
  · rw [continuousAt_iff_punctured_nhds]
    replace ht := ((tendsto_id.sub_const c).mono_left nhdsWithin_le_nhds).prodMk ht
    simp only [id_eq, sub_self, ← nhds_prod_eq] at ht
    simpa [pow_succ', mul_smul] using Tendsto.comp continuous_smul.continuousAt ht

lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

-- TODO: restate `MeromorphicNFOn.Gamma` when `MeromorphicNF` is defined

lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
