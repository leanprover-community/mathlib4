/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `Majorized` predicate

This file defines the `Majorized` predicate, along with a few basic lemmas.

## Main definitions

* `Majorized f b exp` means that `f =o[atTop] (b ^ exp')` for any `exp' > exp`.
  Intuitively, this means that the right order of `f` in terms of `b` is at most `b ^ exp`.
  This predicate is used in the definition of the `MultiseriesExpansion.Approximates` predicate.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Topology Filter Asymptotics

/-- `Majorized f g exp` for real functions `f` and `g` means that for any `exp' > exp`,
`f =o[atTop] g ^ exp'`. This is used to define the `MultiseriesExpansion.Approximates` predicate.
The naming `Majorized` is non-standard because this notion is invented for the purposes of
this tactic, and does not exists in literature. -/
def Majorized (f b : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp' > exp, f =o[atTop] (b ^ exp')

namespace Majorized

variable {f g b : ℝ → ℝ} {exp : ℝ}

/-- Replacing the first argument of `Majorized` by an eventually equal function preserves it. -/
theorem of_eventuallyEq (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp) :
    Majorized g b exp := by
  simp only [Majorized] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

/-- For any function `f` tending to infinity, `f ^ exp` is majorized by `f` with exponent `exp`. -/
theorem self (h : Tendsto f atTop atTop) :
    Majorized (f ^ exp) f exp := by
  simp only [Majorized]
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

/-- If `f` is majorized with exponent `exp₁`, then it is majorized with any `exp₂ ≥ exp₁`. -/
theorem of_le {exp1 exp2 : ℝ} (h_lt : exp1 ≤ exp2) (h : Majorized f b exp1) :
    Majorized f b exp2 := by
  simp only [Majorized] at *
  exact fun exp' h_exp ↦ h _ (by linarith)

/-- If `f` is majorized with a negative exponent, then it tends to zero. -/
theorem tendsto_zero_of_neg (h_lt : exp < 0) (h : Majorized f b exp) :
    Tendsto f atTop (𝓝 0) := by
  simpa [Pi.pow_def, Majorized] using h 0 (by linarith)

/-- Constants are majorized with exponent `exp = 0` by any functions which tends to infinity. -/
theorem const (h_tendsto : Tendsto b atTop atTop) {c : ℝ} :
    Majorized (fun _ ↦ c) b 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

/-- The zero function is majorized with any exponent. -/
theorem zero : Majorized 0 b exp :=
  fun _ _ ↦ Asymptotics.isLittleO_zero _ _

/-- `c • f` is majorized with the same exponent as `f` for any constant `c`. -/
theorem smul (h : Majorized f b exp) {c : ℝ} :
    Majorized (c • f) b exp :=
  fun exp h_exp ↦ (h exp h_exp).const_mul_left _

/-- The sum of two functions that are majorized with exponents `f_exp` and `g_exp` is
majorized with exponent `exp` whenever `exp ≥ max f_exp g_exp`. -/
theorem add {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (hf_exp : f_exp ≤ exp) (hg_exp : g_exp ≤ exp) :
    Majorized (f + g) b exp := by
  simp only [Majorized] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

set_option backward.isDefEq.respectTransparency false in
/-- The product of two functions that are majorized with exponents `f_exp` and `g_exp` is
majorized with exponent `f_exp + g_exp`. -/
theorem mul {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (h_pos : ∀ᶠ t in atTop, 0 < b t) :
    Majorized (f * g) b (f_exp + g_exp) := by
  simp only [Majorized] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t ↦ b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos.mono
  intro t hx
  simp only [Pi.pow_apply]
  conv_rhs => rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf, Real.rpow_add hx]

theorem mul_bounded {f g basis_hd : ℝ → ℝ} {exp : ℝ} (hf : Majorized f basis_hd exp)
    (hg : g =O[atTop] (fun _ ↦ (1 : ℝ))) :
    Majorized (f * g) basis_hd exp := by
  intro exp h_exp
  convert IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp
  rfl

end Majorized

end Tactic.ComputeAsymptotics
