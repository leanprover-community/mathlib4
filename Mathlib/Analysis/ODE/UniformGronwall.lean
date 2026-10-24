/-
Copyright (c) 2026 Daiduo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daiduo
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Uniform Grönwall inequality

The uniform Grönwall inequality is an integral-form variant of Grönwall's inequality
commonly used in PDE theory. It provides a uniform bound on `y(t)` over `[r, T]`
when the integrals of `y`, `g`, and `h` over any interval of length `r` are bounded.

## Main results

* `uniformGronwallBound`: the explicit bound `(a₃ / r + a₂) * exp a₁`.
* `le_uniformGronwallBound_of_deriv_le`: the uniform Grönwall inequality for real-valued
  functions satisfying `y'(t) ≤ g(t) * y(t) + h(t)`.

## References

* [R. Temam, *Infinite-Dimensional Dynamical Systems in Mechanics and Physics*,
  Appendix A][Temam_1988]
-/

@[expose] public section

open intervalIntegral MeasureTheory Set Real
open scoped Topology

/-- The uniform Grönwall bound `(a₃ / r + a₂) * exp a₁`. -/
noncomputable def uniformGronwallBound (a₁ a₂ a₃ r : ℝ) : ℝ :=
  (a₃ / r + a₂) * exp a₁

@[simp]
theorem uniformGronwallBound_of_a₂0_a₃0 (a₁ r : ℝ) :
    uniformGronwallBound a₁ 0 0 r = 0 := by
  simp [uniformGronwallBound]

@[simp]
theorem uniformGronwallBound_nonneg {a₁ a₂ a₃ r : ℝ}
    (_ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hr : 0 ≤ r) :
    0 ≤ uniformGronwallBound a₁ a₂ a₃ r := by
  apply mul_nonneg
  · apply add_nonneg
    · apply div_nonneg ha₃ hr
    · exact ha₂
  · exact exp_nonneg a₁

/-- Main theorem: Uniform Grönwall inequality for real-valued functions.

Let `y, g, h : ℝ → ℝ` satisfy `y'(t) ≤ g(t) * y(t) + h(t)` on `[0, T)`.
If the integrals of `g`, `h`, and `y` over any interval of length `r` are bounded
by `a₁`, `a₂`, and `a₃` respectively, then `y(t)` is uniformly bounded
by `(a₃/r + a₂) * exp(a₁)` for all `t ∈ [r, T]`. -/
theorem le_uniformGronwallBound_of_deriv_le {y y' g h : ℝ → ℝ} {T r a₁ a₂ a₃ : ℝ}
    (hr : 0 < r) (_hT : r ≤ T)
    (hy : ContinuousOn y (Icc 0 T))
    (hy' : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (y' t) (Ici t) t)
    (hg : ContinuousOn g (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T))
    (hg_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hh_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (h_ineq : ∀ t ∈ Ico 0 T, y' t ≤ g t * y t + h t)
    (hg_bound : ∀ t ∈ Icc 0 (T - r), ∫ s in t..(t + r), g s ≤ a₁)
    (hh_bound : ∀ t ∈ Icc 0 (T - r), ∫ s in t..(t + r), h s ≤ a₂)
    (hy_bound : ∀ t ∈ Icc 0 (T - r), ∫ s in t..(t + r), y s ≤ a₃)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (_ha₃ : 0 ≤ a₃) :
    ∀ t ∈ Icc r T, y t ≤ uniformGronwallBound a₁ a₂ a₃ r := by
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htT : t ≤ T := ht.2
  have htr : t - r ≤ T - r := by linarith
  have htr0 : 0 ≤ t - r := by linarith [ht.1]
  have hsr : ∀ s ∈ Icc (t - r) t, s ∈ Icc 0 T := by
    intro s hs
    constructor
    · linarith [hs.1]
    · linarith [hs.2]
  -- Step 1: For any s ∈ [t-r, t], apply standard Grönwall on [s, t] to get
  -- y(t) ≤ y(s) * exp(∫_s^t g) + ∫_s^t h(τ) * exp(∫_τ^t g) dτ
  have hstep1 : ∀ s ∈ Icc (t - r) t, y t ≤ y s * Real.exp a₁ + a₂ * Real.exp a₁ := by
    intro s hs
    have hs_in_Ico : s ∈ Ico (t - r) t ∨ s = t := by
      by_cases hst : s = t
      · right; exact hst
      · left
        constructor
        · exact hs.1
        · exact lt_of_le_of_ne hs.2 hst
    rcases hs_in_Ico with hs_Ico | hst
    · -- Case s ∈ [t-r, t)
      have hs0 : s ∈ Ico 0 T := by
        constructor
        · linarith [hs_Ico.1]
        · linarith [hs_Ico.2]
      -- Define ψ(τ) = y(τ) * exp(-∫_s^τ g(σ) dσ) for τ ∈ [s, t]
      -- Then ψ'(τ) = (y'(τ) - g(τ) * y(τ)) * exp(-∫_s^τ g(σ) dσ) ≤ h(τ) * exp(-∫_s^τ g(σ) dσ)
      let ψ (τ : ℝ) := y τ * Real.exp (-∫ σ in s..τ, g σ)
      have hψ_deriv : ∀ τ ∈ Ico s t, HasDerivWithinAt ψ
          ((y' τ - g τ * y τ) * Real.exp (-∫ σ in s..τ, g σ)) (Ici τ) τ := by
        intro τ hτ
        have hτ0 : τ ∈ Ico 0 T := by
          constructor
          · linarith [hs0.1, hτ.1]
          · linarith [hs0.2, hτ.2]
        have h1 : HasDerivWithinAt (fun u => y u) (y' τ) (Ici τ) τ := hy' τ hτ0
        have h2 : HasDerivWithinAt (fun u => Real.exp (-∫ σ in s..u, g σ))
            (-g τ * Real.exp (-∫ σ in s..τ, g σ)) (Ici τ) τ := by
          have h3 : HasDerivWithinAt (fun u => -∫ σ in s..u, g σ) (-g τ) (Ici τ) τ := by
            have h4 : HasDerivWithinAt (fun u => ∫ σ in s..u, g σ) (g τ) (Ici τ) τ := by
              have h5 : IntervalIntegrable g volume s τ := by
                apply ContinuousOn.intervalIntegrable
                apply hg.mono
                intro x hx
                have hx1 : 0 ≤ x := by
                  have h1 : x ∈ uIcc s τ := hx
                  simp only [mem_uIcc] at h1
                  rcases h1 with (h | h)
                  · linarith [hs0.1]
                  · linarith [hs0.1, hτ.1]
                have hx2 : x ≤ T := by
                  have h1 : x ∈ uIcc s τ := hx
                  simp only [mem_uIcc] at h1
                  rcases h1 with (h | h)
                  · linarith [hs0.2, hτ.2]
                  · linarith [hs0.2]
                constructor
                · exact hx1
                · exact hx2
              have hτ_Icc : τ ∈ Icc 0 T := hsr τ ⟨by linarith [hs.1, hτ.1], by linarith [hτ.2]⟩
              have hτ_lt : τ < T := hτ0.2
              have h6 : ContinuousWithinAt g (Ioi τ) τ := by
                have h7 : ContinuousWithinAt g (Icc 0 T) τ := hg.continuousWithinAt hτ_Icc
                have h8 : Icc 0 T ∈ 𝓝[Ioi τ] τ := by
                  rw [mem_nhdsWithin]
                  use Iio T
                  constructor
                  · exact isOpen_Iio
                  constructor
                  · exact hτ_lt
                  · intro x hx
                    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Icc] at hx ⊢
                    constructor
                    · linarith [hτ0.1, hx.2]
                    · linarith [hx.1]
                exact h7.mono_of_mem_nhdsWithin h8
              have h7 : StronglyMeasurableAtFilter g (𝓝[Ioi τ] τ) volume := by
                have h8 : StronglyMeasurableAtFilter g (𝓝[Icc 0 T] τ) volume := by
                  apply ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin hg measurableSet_Icc τ
                apply h8.filter_mono
                rw [nhdsWithin_le_iff]
                have h9 : Icc 0 T ∈ 𝓝[Ioi τ] τ := by
                  rw [mem_nhdsWithin]
                  use Iio T
                  constructor
                  · exact isOpen_Iio
                  constructor
                  · exact hτ_lt
                  · intro x hx
                    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Icc] at hx ⊢
                    constructor
                    · linarith [hτ0.1, hx.2]
                    · linarith [hx.1]
                exact h9
              have h8 : Fact (τ ∈ Icc s τ) := ⟨by constructor <;> linarith [hτ.1]⟩
              exact integral_hasDerivWithinAt_right h5 h7 h6
            simpa using h4.neg
          have h4 : HasDerivAt (fun v => Real.exp v) (Real.exp (-∫ σ in s..τ, g σ))
              (-∫ σ in s..τ, g σ) := Real.hasDerivAt_exp (-∫ σ in s..τ, g σ)
          have h5 : HasDerivWithinAt (fun u => Real.exp (-∫ σ in s..u, g σ))
              (Real.exp (-∫ σ in s..τ, g σ) * (-g τ)) (Ici τ) τ := by
            have h6 : (fun u => Real.exp (-∫ σ in s..u, g σ)) = (fun v => Real.exp v) ∘
                (fun u => -∫ σ in s..u, g σ) := by
              funext u
              rfl
            rw [h6]
            exact h4.comp_hasDerivWithinAt τ h3
          convert! h5 using 1
          ring
        have h3 : HasDerivWithinAt ψ
            (y' τ * Real.exp (-∫ σ in s..τ, g σ) + y τ * (-g τ * Real.exp (-∫ σ in s..τ, g σ)))
            (Ici τ) τ := h1.mul h2
        convert! h3 using 1
        ring
      have hψ_ineq : ∀ τ ∈ Ico s t,
          (y' τ - g τ * y τ) * Real.exp (-∫ σ in s..τ, g σ) ≤
          h τ * Real.exp (-∫ σ in s..τ, g σ) := by
        intro τ hτ
        have hτ0 : τ ∈ Ico 0 T := by
          constructor
          · linarith [hs0.1, hτ.1]
          · linarith [hs0.2, hτ.2]
        have h1 : y' τ - g τ * y τ ≤ h τ := by linarith [h_ineq τ hτ0]
        have h2 : 0 ≤ Real.exp (-∫ σ in s..τ, g σ) := exp_nonneg (-∫ σ in s..τ, g σ)
        apply mul_le_mul_of_nonneg_right h1 h2
      -- Apply comparison principle: ψ(t) ≤ ψ(s) + ∫_s^t h(τ) * exp(-∫_s^τ g) dτ
      have hψ_cont : ContinuousOn ψ (Icc s t) := by
        apply ContinuousOn.mul
        · apply hy.mono
          intro x hx
          constructor
          · linarith [hs0.1, hx.1]
          · linarith [hs0.2, hx.2]
        · have hst_le : s ≤ t := by linarith [hs_Ico.1, hs_Ico.2]
          have h1 : ContinuousOn (fun τ => -∫ σ in s..τ, g σ) (Icc s t) := by
            have h2 : ContinuousOn (fun τ => ∫ σ in s..τ, g σ) (Icc s t) := by
              have h3 : ContinuousOn (fun τ => ∫ σ in s..τ, g σ) (uIcc s t) := by
                have hg_int : IntervalIntegrable g volume s t := by
                  apply ContinuousOn.intervalIntegrable_of_Icc
                  · exact hst_le
                  · apply hg.mono
                    intro x hx
                    constructor
                    · linarith [hs0.1, hx.1]
                    · linarith [hs0.2, hx.2, htT]
                have hs_mem : s ∈ uIcc s t := by
                  rw [uIcc_of_le hst_le]
                  constructor <;> linarith
                exact continuousOn_primitive_interval' hg_int hs_mem
              rwa [uIcc_of_le hst_le] at h3
            have h3 : ContinuousOn (fun (x : ℝ) => -x) (univ : Set ℝ) := continuous_neg.continuousOn
            have h4 : MapsTo (fun τ => ∫ σ in s..τ, g σ) (Icc s t) univ := by simp [MapsTo]
            exact ContinuousOn.comp h3 h2 h4
          have h2 : ContinuousOn (fun τ => Real.exp (-∫ σ in s..τ, g σ)) (Icc s t) := by
            apply ContinuousOn.rexp
            exact h1
          exact h2
      have hB_cont : ContinuousOn (fun τ => ψ s + ∫ σ in s..τ, h σ) (Icc s t) := by
        apply ContinuousOn.add
        · exact continuousOn_const
        · have hst_le : s ≤ t := by linarith [hs_Ico.1, hs_Ico.2]
          have h1 : ContinuousOn (fun τ => ∫ σ in s..τ, h σ) (Icc s t) := by
            have h2 : ContinuousOn (fun τ => ∫ σ in s..τ, h σ) (uIcc s t) := by
              have hh_int : IntervalIntegrable h volume s t := by
                apply ContinuousOn.intervalIntegrable_of_Icc
                · exact hst_le
                · apply hh.mono
                  intro x hx
                  constructor
                  · linarith [hs0.1, hx.1]
                  · linarith [hs0.2, hx.2, htT]
              have hs_mem : s ∈ uIcc s t := by
                rw [uIcc_of_le hst_le]
                constructor <;> linarith
              exact continuousOn_primitive_interval' hh_int hs_mem
            rwa [uIcc_of_le hst_le] at h2
          exact h1
      have hB_deriv : ∀ τ ∈ Ico s t, HasDerivWithinAt (fun τ => ψ s + ∫ σ in s..τ, h σ)
          (h τ) (Ici τ) τ := by
        intro τ hτ
        have hτ_Icc : τ ∈ Icc 0 T := hsr τ ⟨by linarith [hs.1, hτ.1], by linarith [hτ.2]⟩
        have hτ_lt : τ < T := by linarith [hs0.2, hτ.2]
        have h1 : HasDerivWithinAt (fun u => ∫ σ in s..u, h σ) (h τ) (Ici τ) τ := by
          have h2 : IntervalIntegrable h volume s τ := by
            apply ContinuousOn.intervalIntegrable_of_Icc
            · linarith [hτ.1]
            · apply hh.mono
              intro x hx
              constructor
              · linarith [hs0.1, hx.1]
              · linarith [hs0.2, hx.2, htT]
          have h3 : StronglyMeasurableAtFilter h (𝓝[Ioi τ] τ) volume := by
            have h4 : StronglyMeasurableAtFilter h (𝓝[Icc 0 T] τ) volume := by
              apply ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin hh measurableSet_Icc τ
            apply h4.filter_mono
            rw [nhdsWithin_le_iff]
            have h5 : Icc 0 T ∈ 𝓝[Ioi τ] τ := by
              rw [mem_nhdsWithin]
              use Iio T
              constructor
              · exact isOpen_Iio
              constructor
              · exact hτ_lt
              · intro x hx
                simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Icc] at hx ⊢
                constructor
                · linarith [hτ_Icc.1, hx.2]
                · linarith [hx.1]
            exact h5
          have h4 : ContinuousWithinAt h (Ioi τ) τ := by
            have h5 : ContinuousWithinAt h (Icc 0 T) τ := hh.continuousWithinAt hτ_Icc
            have h6 : Icc 0 T ∈ 𝓝[Ioi τ] τ := by
              rw [mem_nhdsWithin]
              use Iio T
              constructor
              · exact isOpen_Iio
              constructor
              · exact hτ_lt
              · intro x hx
                simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Icc] at hx ⊢
                constructor
                · linarith [hτ_Icc.1, hx.2]
                · linarith [hx.1]
            exact h5.mono_of_mem_nhdsWithin h6
          have h5 : Fact (τ ∈ Icc s τ) := ⟨by constructor <;> linarith [hτ.1]⟩
          exact integral_hasDerivWithinAt_right h2 h3 h4
        have h4 : HasDerivWithinAt (fun _ => ψ s) 0 (Ici τ) τ := hasDerivWithinAt_const _ _ _
        convert! HasDerivWithinAt.add h4 h1 using 1
        ring
      have hψ_le_B : ∀ τ ∈ Ico s t,
          (y' τ - g τ * y τ) * Real.exp (-∫ σ in s..τ, g σ) ≤ h τ := by
        intro τ hτ
        have h1 : (y' τ - g τ * y τ) * Real.exp (-∫ σ in s..τ, g σ) ≤
            h τ * Real.exp (-∫ σ in s..τ, g σ) := hψ_ineq τ hτ
        have h2 : Real.exp (-∫ σ in s..τ, g σ) ≤ 1 := by
          have h3 : -∫ σ in s..τ, g σ ≤ 0 := by
            have h4 : 0 ≤ ∫ σ in s..τ, g σ := by
              apply intervalIntegral.integral_nonneg
              · linarith [hτ.1, hτ.2]
              · intro x hx
                apply hg_nonneg
                constructor
                · linarith [hs0.1, hx.1]
                · nlinarith [hx.2, hτ.2, htT]
            linarith
          have h4 : Real.exp (-∫ σ in s..τ, g σ) ≤ Real.exp (0 : ℝ) :=
            Real.exp_le_exp_of_le (by linarith)
          rw [show Real.exp (0 : ℝ) = 1 by simp] at h4
          exact h4
        have h3 : h τ * Real.exp (-∫ σ in s..τ, g σ) ≤ h τ := by
          have h4 : h τ * Real.exp (-∫ σ in s..τ, g σ) ≤ h τ * 1 := by
            apply mul_le_mul_of_nonneg_left h2
            apply hh_nonneg
            constructor
            · linarith [hs0.1, hτ.1]
            · linarith [hs0.2, hτ.2]
          have h5 : h τ * 1 = h τ := by ring
          linarith [h4, h5]
        linarith [h1, h3]
      have hcomp : ∀ τ ∈ Icc s t, ψ τ ≤ ψ s + ∫ σ in s..τ, h σ := by
        apply image_le_of_deriv_right_le_deriv_boundary hψ_cont
        · intro τ hτ
          have hτ' : τ ∈ Ico s t := by
            constructor
            · linarith [hτ.1]
            · linarith [hτ.2]
          exact hψ_deriv τ hτ'
        · -- ψ(s) ≤ B(s)
          simp [intervalIntegral.integral_same]
        · exact hB_cont
        · exact hB_deriv
        · exact hψ_le_B
      have hcomp_t : ψ t ≤ ψ s + ∫ σ in s..t, h σ :=
        hcomp t (by constructor <;> linarith [hs_Ico.1, hs_Ico.2])
      have hψ_t : ψ t = y t * Real.exp (-∫ σ in s..t, g σ) := by simp [ψ]
      have hψ_s : ψ s = y s := by
        simp [ψ, intervalIntegral.integral_same]
      rw [hψ_t, hψ_s] at hcomp_t
      have hint_le : ∫ σ in s..t, h σ ≤ a₂ := by
        have h1 : ∫ σ in s..t, h σ ≤ ∫ σ in (t - r)..t, h σ := by
          have hab : IntervalIntegrable h volume (t - r) s := by
            apply ContinuousOn.intervalIntegrable_of_Icc
            · linarith [hs_Ico.1]
            · apply hh.mono
              intro x hx
              constructor
              · have h1 : t - r ≤ x := hx.1
                nlinarith
              · have h2 : x ≤ s := hx.2
                nlinarith [hs0.2, htT]
          have hbc : IntervalIntegrable h volume s t := by
            apply ContinuousOn.intervalIntegrable_of_Icc
            · linarith [hs_Ico.1, hs_Ico.2]
            · apply hh.mono
              intro x hx
              constructor
              · have h1 : s ≤ x := hx.1
                nlinarith [hs0.1]
              · have h2 : x ≤ t := hx.2
                nlinarith [hs0.2, htT]
          have h2 : ∫ σ in (t - r)..t, h σ = (∫ σ in (t - r)..s, h σ) + ∫ σ in s..t, h σ := by
            have h_eq : (∫ (x : ℝ) in (t - r)..s, h x) + ∫ (x : ℝ) in s..t, h x =
                ∫ (x : ℝ) in (t - r)..t, h x := by
              exact intervalIntegral.integral_add_adjacent_intervals hab hbc
            have h_eq' : (∫ (σ : ℝ) in (t - r)..s, h σ) + ∫ (σ : ℝ) in s..t, h σ =
                ∫ (σ : ℝ) in (t - r)..t, h σ := by
              simpa using h_eq
            exact h_eq'.symm
          have h3 : 0 ≤ ∫ σ in (t - r)..s, h σ := by
            apply intervalIntegral.integral_nonneg
            · linarith [hs_Ico.1]
            · intro x hx
              apply hh_nonneg
              constructor
              · have h1 : t - r ≤ x := hx.1
                nlinarith
              · have h2 : x ≤ s := hx.2
                nlinarith [hs0.2, htT]
          have h4 : ∫ σ in s..t, h σ ≤ ∫ σ in (t - r)..t, h σ := by
            have h5 : (∫ σ in (t - r)..t, h σ) - ∫ σ in s..t, h σ = ∫ σ in (t - r)..s, h σ := by
              linarith [h2]
            have h6 : 0 ≤ (∫ σ in (t - r)..t, h σ) - ∫ σ in s..t, h σ := by
              rw [h5]
              exact h3
            linarith
          exact h4
        have h2 : t - r ∈ Icc 0 (T - r) := by
          constructor
          · exact htr0
          · exact htr
        have h3 : ∫ σ in (t - r)..t, h σ ≤ a₂ := by
          have h4 : ∫ σ in (t - r)..(t - r + r), h σ ≤ a₂ := hh_bound (t - r) h2
          have h5 : t - r + r = t := by ring
          rw [h5] at h4
          exact h4
        linarith
      have h1 : y t * Real.exp (-∫ σ in s..t, g σ) ≤ y s + a₂ := by
        linarith [hcomp_t, hint_le]
      have h2 : y t ≤ y s * Real.exp a₁ + a₂ * Real.exp a₁ := by
        have h3 : y t = y t * Real.exp (-∫ σ in s..t, g σ) * Real.exp (∫ σ in s..t, g σ) := by
          have h4 : Real.exp (-∫ σ in s..t, g σ) * Real.exp (∫ σ in s..t, g σ) = 1 := by
            rw [← Real.exp_add]
            simp
          have h5 : y t * Real.exp (-∫ σ in s..t, g σ) * Real.exp (∫ σ in s..t, g σ)
              = y t * (Real.exp (-∫ σ in s..t, g σ) * Real.exp (∫ σ in s..t, g σ)) := by ring
          rw [h5, h4]
          simp
        have h4 : y t * Real.exp (-∫ σ in s..t, g σ) * Real.exp (∫ σ in s..t, g σ) ≤
            (y s + a₂) * Real.exp (∫ σ in s..t, g σ) := by
          apply mul_le_mul_of_nonneg_right h1
          exact exp_nonneg (∫ σ in s..t, g σ)
        have h5 : (y s + a₂) * Real.exp (∫ σ in s..t, g σ) ≤
            (y s + a₂) * Real.exp a₁ := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.exp_monotone
            have h6 : ∫ σ in s..t, g σ ≤ a₁ := by
              have h7 : ∫ σ in s..t, g σ ≤ ∫ σ in (t - r)..t, g σ := by
                have hab : IntervalIntegrable g volume (t - r) s := by
                  apply ContinuousOn.intervalIntegrable_of_Icc
                  · linarith [hs_Ico.1]
                  · apply hg.mono
                    intro x hx
                    constructor
                    · have h1 : t - r ≤ x := hx.1
                      nlinarith
                    · have h2 : x ≤ s := hx.2
                      nlinarith [hs0.2, htT]
                have hbc : IntervalIntegrable g volume s t := by
                  apply ContinuousOn.intervalIntegrable_of_Icc
                  · linarith [hs_Ico.1, hs_Ico.2]
                  · apply hg.mono
                    intro x hx
                    constructor
                    · have h1 : s ≤ x := hx.1
                      nlinarith [hs0.1]
                    · have h2 : x ≤ t := hx.2
                      nlinarith [hs0.2, htT]
                have h2 : ∫ σ in (t - r)..t, g σ =
                    (∫ σ in (t - r)..s, g σ) + ∫ σ in s..t, g σ := by
                  have h_eq : (∫ (x : ℝ) in (t - r)..s, g x) + ∫ (x : ℝ) in s..t, g x =
                      ∫ (x : ℝ) in (t - r)..t, g x := by
                    exact intervalIntegral.integral_add_adjacent_intervals hab hbc
                  have h_eq' : (∫ (σ : ℝ) in (t - r)..s, g σ) + ∫ (σ : ℝ) in s..t, g σ =
                      ∫ (σ : ℝ) in (t - r)..t, g σ := by
                    simpa using h_eq
                  exact h_eq'.symm
                have h3 : 0 ≤ ∫ σ in (t - r)..s, g σ := by
                  apply intervalIntegral.integral_nonneg
                  · linarith [hs_Ico.1]
                  · intro x hx
                    apply hg_nonneg
                    constructor
                    · have h1 : t - r ≤ x := hx.1
                      nlinarith
                    · have h2 : x ≤ s := hx.2
                      nlinarith [hs0.2, htT]
                have h4 : ∫ σ in s..t, g σ ≤ ∫ σ in (t - r)..t, g σ := by
                  have h5 : (∫ σ in (t - r)..t, g σ) - ∫ σ in s..t, g σ =
                      ∫ σ in (t - r)..s, g σ := by
                    linarith [h2]
                  have h6 : 0 ≤ (∫ σ in (t - r)..t, g σ) - ∫ σ in s..t, g σ := by
                    rw [h5]
                    exact h3
                  linarith
                exact h4
              have h7a : ∫ σ in (t - r)..t, g σ ≤ a₁ := by
                have h8 : t - r ∈ Icc 0 (T - r) := by
                  constructor
                  · exact htr0
                  · exact htr
                have h9 : ∫ σ in (t - r)..t, g σ ≤ a₁ := by
                  have h10 : ∫ σ in (t - r)..(t - r + r), g σ ≤ a₁ := hg_bound (t - r) h8
                  have h11 : t - r + r = t := by ring
                  rw [h11] at h10
                  exact h10
                exact h9
              linarith [h7, h7a]
            · linarith [ha₁]
          · apply add_nonneg
            · apply hy_nonneg
              constructor
              · linarith [hs0.1]
              · linarith [hs0.2]
            · exact ha₂
        have h6 : (y s + a₂) * rexp a₁ = y s * rexp a₁ + a₂ * rexp a₁ := by ring
        rw [h3]
        have h7 : y t * rexp (-∫ σ in s..t, g σ) * rexp (∫ σ in s..t, g σ) ≤
            y s * rexp a₁ + a₂ * rexp a₁ := by
          have h8 : y t * rexp (-∫ σ in s..t, g σ) * rexp (∫ σ in s..t, g σ)
              ≤ (y s + a₂) * rexp (∫ σ in s..t, g σ) := h4
          have h9 : (y s + a₂) * rexp (∫ σ in s..t, g σ)
              ≤ (y s + a₂) * rexp a₁ := h5
          have h10 : (y s + a₂) * rexp a₁ = y s * rexp a₁ + a₂ * rexp a₁ := h6
          linarith [h8, h9, h10]
        exact h7
      exact h2
    · -- Case s = t
      rw [hst]
      have h1 : y t * Real.exp a₁ + a₂ * Real.exp a₁ = (y t + a₂) * Real.exp a₁ := by ring
      rw [h1]
      have h2 : 0 ≤ a₂ * Real.exp a₁ := mul_nonneg ha₂ (exp_nonneg a₁)
      have h3 : y t ≤ y t + a₂ := by linarith [ha₂]
      have h4 : y t + a₂ ≤ (y t + a₂) * Real.exp a₁ := by
        have h5 : 1 ≤ Real.exp a₁ := Real.one_le_exp ha₁
        have h6 : y t + a₂ ≤ (y t + a₂) * 1 := by rw [mul_one]
        have h7 : (y t + a₂) * 1 ≤ (y t + a₂) * Real.exp a₁ := by
          apply mul_le_mul_of_nonneg_left h5
          apply add_nonneg
          · apply hy_nonneg
            constructor
            · exact ht0
            · exact htT
          · exact ha₂
        linarith
      linarith
  -- Step 2: y(s) ≥ y(t) * exp(-a₁) - a₂ for all s ∈ [t-r, t]
  have hstep2 : ∀ s ∈ Icc (t - r) t, y s ≥ y t * Real.exp (-a₁) - a₂ := by
    intro s hs
    have h1 : y t ≤ y s * Real.exp a₁ + a₂ * Real.exp a₁ := hstep1 s hs
    have h2 : 0 < Real.exp a₁ := exp_pos a₁
    have h3 : y t * Real.exp (-a₁) ≤ y s + a₂ := by
      have h4 : Real.exp (-a₁) = (Real.exp a₁)⁻¹ := by rw [exp_neg]
      rw [h4]
      have h5 : y t * (Real.exp a₁)⁻¹ ≤
          (y s * Real.exp a₁ + a₂ * Real.exp a₁) * (Real.exp a₁)⁻¹ := by
        apply mul_le_mul_of_nonneg_right h1
        apply inv_nonneg.mpr
        exact (exp_pos a₁).le
      have h6 : (y s * Real.exp a₁ + a₂ * Real.exp a₁) * (Real.exp a₁)⁻¹ = y s + a₂ := by
        field_simp [h2.ne']
      nlinarith [h5, h6]
    linarith
  -- Step 3: Integrate y(s) over [t-r, t]
  have hstep3 : ∫ s in (t - r)..t, y s ≥ r * (y t * Real.exp (-a₁) - a₂) := by
    have h1 : ∀ s ∈ Icc (t - r) t, y s ≥ y t * Real.exp (-a₁) - a₂ := hstep2
    have h2 : ∫ s in (t - r)..t, (y t * Real.exp (-a₁) - a₂) ≤ ∫ s in (t - r)..t, y s := by
      have hab : t - r ≤ t := by linarith [hr]
      have hf : IntervalIntegrable (fun _ => y t * Real.exp (-a₁) - a₂) volume (t - r) t :=
        intervalIntegrable_const
      have hg : IntervalIntegrable y volume (t - r) t := by
        apply ContinuousOn.intervalIntegrable
        apply hy.mono
        intro x hx
        have hx' : x ∈ Icc (t - r) t := by
          have h1 : t - r ≤ t := by linarith [hr]
          rwa [uIcc_of_le h1] at hx
        exact hsr x hx'
      exact intervalIntegral.integral_mono_on hab hf hg (fun s hs => h1 s hs)
    have h3 : ∫ s in (t - r)..t, (y t * Real.exp (-a₁) - a₂) = (y t * Real.exp (-a₁) - a₂) * r := by
      rw [intervalIntegral.integral_const]
      ring
    linarith [h2, h3]
  -- Step 4: Use the bound on ∫_{t-r}^t y(s) ds
  have hstep4 : ∫ s in (t - r)..t, y s ≤ a₃ := by
    have h1 : t - r ∈ Icc 0 (T - r) := by
      constructor
      · exact htr0
      · exact htr
    have h2 : ∫ s in (t - r)..(t - r + r), y s ≤ a₃ := hy_bound (t - r) h1
    have h3 : t - r + r = t := by ring
    rw [h3] at h2
    exact h2
  -- Step 5: Combine to get the final bound
  have hstep5 : r * (y t * Real.exp (-a₁) - a₂) ≤ a₃ := by linarith [hstep3, hstep4]
  have hstep6 : y t * Real.exp (-a₁) - a₂ ≤ a₃ / r := by
    apply (le_div_iff₀ hr).mpr
    linarith
  have hstep7 : y t * Real.exp (-a₁) ≤ a₃ / r + a₂ := by linarith
  have hstep8 : y t ≤ (a₃ / r + a₂) * Real.exp a₁ := by
    have h1 : Real.exp (-a₁) = (Real.exp a₁)⁻¹ := by rw [exp_neg]
    rw [h1] at hstep7
    have h2 : 0 < Real.exp a₁ := exp_pos a₁
    have h3 : y t ≤ (a₃ / r + a₂) * Real.exp a₁ := by
      have h4 : y t * (Real.exp a₁)⁻¹ ≤ a₃ / r + a₂ := hstep7
      have h5 : y t ≤ (a₃ / r + a₂) * Real.exp a₁ := by
        have h6 : y t = y t * (Real.exp a₁)⁻¹ * Real.exp a₁ := by
          field_simp [h2.ne']
        rw [h6]
        apply mul_le_mul_of_nonneg_right h4
        exact (exp_pos a₁).le
      exact h5
    exact h3
  rw [uniformGronwallBound]
  exact hstep8
