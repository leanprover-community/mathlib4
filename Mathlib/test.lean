/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.Connected

/-!
# Empty header

To appease the linter
-/

open Submodule

lemma bar {E 𝕜 : Type _} [AddCommGroup E] [Field 𝕜] [Module 𝕜 E](x y : E)
    (h : Module.rank 𝕜 E = 1) (hx : x ≠ 0) :
    ∃ (c : 𝕜), c • x = y := by
  have : Submodule.span 𝕜 {x} = ⊤ := by
    have A : Submodule.span 𝕜 {x} ≤ ⊤ := sorry
    have B : Module.rank (Submodule.span 𝕜 {x}) = 1 := sorry
    have C : Module.rank (⊤ : Submodule 𝕜 E) = 1 := sorry
    have Z := FiniteDimensional.eq_top_of_finrank_eq

  have : y ∈ Submodule.span 𝕜 {x} := by
    rw [this]; trivial
  exact Iff.mp mem_span_singleton this

--  have : Submodule.span 𝕜 {x} = ⊤ := by
--    have Z := Span_singleton


#exit

variable {E : Type _} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

lemma foo (x : E) (h : Module.rank ℝ E = 0) (hx : x ≠ 0) : False := by
  have : Subsingleton E := (rank_zero_iff (R := ℝ)).1 h
  exact hx (Subsingleton.elim x 0)



lemma bar (x y : E) (h : Module.rank ℝ E = 1) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : E ≃L[ℝ] E, A x = y := by
  have : ∃ (c : ℝ), y = c • x := by
    exact?
