/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of analytic functions with power factors

This file contains lemmas about the iterated derivative of a function that factors as a
power of `(· - z₀)` times an analytic function.
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]

/-- If a function `R : 𝕜 → 𝕜` factors as `R z = (z - z₀) ^ (k + t) * R₁ z`, where `R₁` is
analytic everywhere, then there exists an everywhere analytic function `R₂ : 𝕜 → 𝕜` such that
the `k`-th iterated derivative of `R` is given by
`iteratedDeriv k R z = (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z)`. -/
lemma iteratedDeriv_mul_pow_sub_of_analytic {k t : ℕ} {z₀ : 𝕜} {R R₁ : 𝕜 → 𝕜}
    (hf1 : ∀ z, AnalyticAt 𝕜 R₁ z) (hR₁ : ∀ z, R z = (z - z₀) ^ (k + t) * R₁ z) :
    ∃ R₂, (∀ z, AnalyticAt 𝕜 R₂ z) ∧ ∀ z, iteratedDeriv k R z =
      (z - z₀) ^ t * ((k + t)! / t ! * R₁ z + (z - z₀) * R₂ z) := by
  induction k generalizing t with
  | zero => exact ⟨0, fun _ ↦ analyticAt_const, by simp [hR₁, Nat.factorial_ne_zero]⟩
  | succ k IH =>
    obtain ⟨R₂, hR₂, hR₂_eq⟩ := IH (t := t + 1) (by grind)
    set R₂' : 𝕜 → 𝕜 := fun z ↦ (t + 1) * R₂ z + ((k + (t + 1))! / (t + 1)! * deriv R₁ z +
      (R₂ z + (z - z₀) * deriv R₂ z))
    refine ⟨R₂', by fun_prop, fun z ↦ ?_⟩
    calc iteratedDeriv (k + 1) R z
      _ = deriv (fun w ↦ (w - z₀) ^ (t + 1)
          * (↑(k + (t + 1))! / ↑(t + 1)! * R₁ w + (w - z₀) * R₂ w)) z := by
        rw [iteratedDeriv_succ, funext hR₂_eq]
      _ = (t + 1) * (z - z₀) ^ t * ((k + (t + 1))! / (t + 1)! * R₁ z + (z - z₀) * R₂ z) +
        (z - z₀) ^ (t + 1) * ((k + (t + 1))! / (t + 1)! * deriv R₁ z +
          (R₂ z + (z - z₀) * deriv R₂ z)) := by
        have hsub : HasDerivAt (· - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
        simpa using! ((hsub.fun_pow (t + 1)).mul
          (((hf1 z).differentiableAt.hasDerivAt.const_mul ((k + (t + 1))! / (t + 1)! : 𝕜)).add
            (hsub.mul (hR₂ z).differentiableAt.hasDerivAt))).deriv
      _ = (z - z₀) ^ t * ((k + 1 + t)! / t ! * R₁ z + (z - z₀) * R₂' z) := by
        have : (t : 𝕜) + 1 ≠ 0 := mod_cast t.succ_ne_zero
        have : ((t + 1)! : 𝕜) = (t + 1) * t ! := by simp [Nat.factorial_succ]
        grind
