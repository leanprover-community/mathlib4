/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analytic functions are `C^∞`.
-/

open Set ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {s : Set E} {x : E} {n : WithTop ℕ∞}

/-- An analytic function is infinitely differentiable. -/
protected theorem AnalyticOnNhd.contDiffOn [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    ContDiffOn 𝕜 n f s := by
  let t := { x | AnalyticAt 𝕜 f x }
  suffices ContDiffOn 𝕜 ω f t from (this.of_le le_top).mono h
  rw [← contDiffOn_infty_iff_contDiffOn_omega]
  have H : AnalyticOnNhd 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_analyticAt 𝕜 f
  exact contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)

/-- An analytic function on the whole space is infinitely differentiable there. -/
theorem AnalyticOnNhd.contDiff [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f univ) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]
  exact h.contDiffOn

theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := by
  obtain ⟨s, hs, hf⟩ := h.exists_mem_nhds_analyticOnNhd
  exact hf.contDiffOn.contDiffAt hs

protected lemma AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) {n : ℕ∞} : ContDiffWithinAt 𝕜 n f s x := by
  rcases h.exists_analyticAt with ⟨g, fx, fg, hg⟩
  exact hg.contDiffAt.contDiffWithinAt.congr (fg.mono (subset_insert _ _)) fx

protected lemma AnalyticOn.contDiffOn [CompleteSpace F] {f : E → F} {s : Set E}
    (h : AnalyticOn 𝕜 f s) {n : ℕ∞} : ContDiffOn 𝕜 n f s :=
  fun x m ↦ (h x m).contDiffWithinAt

@[deprecated (since := "2024-09-26")]
alias AnalyticWithinOn.contDiffOn := AnalyticOn.contDiffOn
