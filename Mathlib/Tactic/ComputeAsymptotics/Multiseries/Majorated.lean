/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `Majorated` predicate

This file defines the `Majorated` predicate, along with a few basic lemmas.

## Main definitions

* `Majorated f b exp` means that `f =o[atTop] (b ^ exp')` for any `exp' > exp`. This predicate is
  used in the definition of the `PreMS.Approximates` predicate.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Topology Filter Asymptotics

/-- `Majorated f g exp` for real functions `f` and `g` means that for any `exp' < exp`,
`f =o[atTop] g ^ exp'`. This is used to define the `PreMS.Approximates` predicate. The naming
`Majorated` is non-standard because this notion is invented for the purposes of this tactic, and
does not exists in literature. -/
def Majorated (f b : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp' > exp, f =o[atTop] (b ^ exp')

namespace Majorated

variable {f g b : ℝ → ℝ} {exp : ℝ}

/-- Replacing the first argument of `Majorated` by an eventually equal function preserves it. -/
theorem of_eventuallyEq (h_eq : g =ᶠ[atTop] f) (h : Majorated f b exp) :
    Majorated g b exp := by
  simp only [Majorated] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

/-- For any function `f` tending to infinity, `f ^ exp` is majorated by `f` with exponent `exp`. -/
theorem self (h : Tendsto f atTop atTop) :
    Majorated (f ^ exp) f exp := by
  simp only [Majorated]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t ↦ f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t ↦ (f t) ^ (exp - exp') :=
      (h.eventually_gt_atTop 0).mono (fun _ h ↦ by simp [← Real.rpow_sub h])
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t ↦ f t ^ (exp - exp')) = ((fun t ↦ t ^ (-(exp' - exp))) ∘ f) by ext; simp]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h
  · apply (Tendsto.eventually_gt_atTop h 0).mono
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/-- If `f` is majorated with exponent `exp₁`, then it is majorated with any `exp₂ ≥ exp₁`. -/
theorem of_le {exp1 exp2 : ℝ} (h_lt : exp1 ≤ exp2) (h : Majorated f b exp1) :
    Majorated f b exp2 := by
  simp only [Majorated] at *
  exact fun exp' h_exp ↦ h _ (by linarith)

/-- If `f` is majorated with a negative exponent, then it tends to zero. -/
theorem tendsto_zero_of_neg (h_lt : exp < 0) (h : Majorated f b exp) :
    Tendsto f atTop (𝓝 0) := by
  simpa [Pi.pow_def, Majorated] using h 0 (by linarith)

/-- Constants are majorated with exponent `exp = 0` by any functions which tends to infinity. -/
theorem const (h_tendsto : Tendsto b atTop atTop) {c : ℝ} :
    Majorated (fun _ ↦ c) b 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

/-- The zero function is majorated with any exponent. -/
theorem zero : Majorated 0 b exp :=
  fun _ _ ↦ Asymptotics.isLittleO_zero _ _

/-- `c • f` is majorated with the same exponent as `f` for any constant `c`. -/
theorem smul (h : Majorated f b exp) {c : ℝ} :
    Majorated (c • f) b exp :=
  fun exp h_exp ↦ (h exp h_exp).const_mul_left _

/-- The sum of two functions that are majorated with exponents `f_exp` and `g_exp` is
majorated with exponent `exp` whenever `exp ≥ max f_exp g_exp`. -/
theorem add {f_exp g_exp : ℝ} (hf : Majorated f b f_exp)
    (hg : Majorated g b g_exp) (hf_exp : f_exp ≤ exp) (hg_exp : g_exp ≤ exp) :
    Majorated (f + g) b exp := by
  simp only [Majorated] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

/-- The product of two functions that are majorated with exponents `f_exp` and `g_exp` is
majorated with exponent `f_exp + g_exp`. -/
theorem mul {f_exp g_exp : ℝ} (hf : Majorated f b f_exp)
    (hg : Majorated g b g_exp) (h_pos : ∀ᶠ t in atTop, 0 < b t) :
    Majorated (f * g) b (f_exp + g_exp) := by
  simp only [Majorated] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t ↦ b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos.mono
  intro t hx
  simp only [Pi.pow_apply]
  conv_rhs => rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf, Real.rpow_add hx]

end Majorated

end Tactic.ComputeAsymptotics
