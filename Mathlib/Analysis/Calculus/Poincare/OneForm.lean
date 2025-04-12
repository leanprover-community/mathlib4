/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Topology.Homotopy.Path

open scoped unitInterval Pointwise
open MeasureTheory

theorem derivWithin_comp_neg {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (s : Set 𝕜) (a : 𝕜) :
    derivWithin (f <| -·) s a = -derivWithin f (-s) (-a) := by
  sorry

-- TODO: add `derivWithin_comp_add_left` etc
theorem derivWithin_comp_const_sub {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (s : Set 𝕜) (a b : 𝕜) :
    derivWithin (f <| a - ·) s b = -derivWithin f (a +ᵥ (-s)) (a - b) := by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·), derivWithin, derivWithin, fderivWithin_comp_add_left]

section PathIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : E}

noncomputable def pathIntegral (ω : E → E →L[ℝ] F) (γ : Path a b) : F :=
  ∫ t in (0)..1, ω (γ.extend t) (derivWithin γ.extend I t)

def PathIntegrable (ω : E → E →L[ℝ] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (fun t ↦ ω (γ.extend t) (derivWithin γ.extend I t)) volume 0 1

@[simp]
theorem pathIntegral_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegral ω (.refl a) = 0 := by
  simp [pathIntegral]

@[simp]
theorem pathIntegrable_refl {ω : E → E →L[ℝ] F} {γ : Path a b} :
    PathIntegrable ω γ.symm ↔ PathIntegrable ω γ := by
  simp only [PathIntegrable]
  

@[simp]
theorem pathIntegral_symm (ω : E → E →L[ℝ] F) (γ : Path a b) :
    pathIntegral ω γ.symm = -pathIntegral ω γ := calc
  pathIntegral ω γ.symm = ∫ t in (0)..1, ω (γ.symm.extend t) (derivWithin γ.symm.extend I t) := rfl
  _ = -∫ t in (1 - 0)..(1 - 1),
        ω (γ.symm.extend (1 - t)) (derivWithin γ.symm.extend I (1 - t)) := by
    rw [← intervalIntegral.integral_comp_sub_left, ← intervalIntegral.integral_symm]
    simp
  _ = -pathIntegral ω γ := by
    rw [intervalIntegral.integral_symm]
    simp only [Path.extend_symm, sub_sub_cancel, sub_self, sub_zero,
      ← intervalIntegral.integral_neg, neg_neg, pathIntegral, ← map_neg, derivWithin_comp_const_sub]
    simp

end PathIntegral
