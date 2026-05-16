/-
Copyright (c) 2025 Arnav Panjla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnav Panjla
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gaussian as a Schwartz function

We show that the Gaussian function `v ↦ exp (-b * ‖v‖ ^ 2)` for `0 < b` is a Schwartz function
on a finite-dimensional real inner product space.

## Main definitions

* `gaussianSchwartz`: the 1-d Gaussian `x ↦ exp (-b * x ^ 2)` as a Schwartz function, for `0 < b`.
* `gaussianSchwartzIPS`: the Gaussian `v ↦ exp (-b * ‖v‖ ^ 2)` on a finite-dimensional real inner
  product space, as a Schwartz function, for `0 < b`.

## Implementation notes

The decay of the iterated derivatives is proved using the Faà di Bruno bound
(`norm_iteratedFDeriv_comp_le`) which bounds `‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n! * C * D ^ n`
where `C` bounds all iterated derivatives of `g` at `f(x)` and `D ^ i` bounds the `i`-th
derivative of `f`. For the Gaussian, `g = exp` has the property that all its iterated derivatives
equal `exp` itself, so at the point `f(x) ≤ 0` they all have norm `exp(f(x))`. The inner function
`f(x) = -b * ‖x‖ ^ 2` has temperate growth, providing polynomial bounds on `D`.

The resulting bound `‖x‖ ^ k * ‖iteratedFDeriv ℝ n (exp ∘ f) x‖ ≤ C' * poly(‖x‖) * exp(f(x))`
tends to zero at infinity since the Gaussian decay dominates any polynomial growth.
-/

@[expose] public section

noncomputable section

open Real Set MeasureTheory Filter Asymptotics SchwartzMap

open scoped Real Topology NNReal ContDiff

/-! ## The inner product space Gaussian as a Schwartz function -/

section GaussianSchwartz

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable {b : ℝ}

/-- The Gaussian `v ↦ exp (-b * ‖v‖ ^ 2)` is smooth. -/
theorem contDiff_gaussianIPS : ContDiff ℝ ∞ (fun v : V => exp (-b * ‖v‖ ^ 2)) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_norm_sq)

/-- All iterated derivatives of `Real.exp` equal `exp`, so at any point `y` the norm of the
`n`-th iterated derivative equals `exp y`. -/
private theorem norm_iteratedFDeriv_exp (y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ = exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (exp_pos y)]

/-- The decay property of the Gaussian in a finite-dimensional inner product space:
for all `k n : ℕ`, there exists `C` such that
`‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun v ↦ exp (-b * ‖v‖ ^ 2)) v‖ ≤ C` for all `v`. -/
theorem gaussianIPS_decay (hb : 0 < b) (k n : ℕ) :
    ∃ C : ℝ, ∀ v : V,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun v => exp (-b * ‖v‖ ^ 2)) v‖ ≤ C := by
  -- Write the Gaussian as exp ∘ f where f(v) = -b * ‖v‖²
  set f : V → ℝ := fun v => -b * ‖v‖ ^ 2 with hf_def
  have hf_eq : (fun v : V => exp (-b * ‖v‖ ^ 2)) = exp ∘ f := rfl
  have hf_smooth : ContDiff ℝ ∞ f := contDiff_const.mul contDiff_norm_sq
  -- f has temperate growth: ‖iteratedFDeriv ℝ i f v‖ ≤ Cf * (1 + ‖v‖)^kf for all i ≤ n
  have hf_temperate : Function.HasTemperateGrowth f :=
    (Function.HasTemperateGrowth.const (-b)).mul (hasTemperateGrowth_norm_sq V)
  obtain ⟨kf, Cf, hCf_nonneg, hCf⟩ := hf_temperate.norm_iteratedFDeriv_le_uniform n
  -- Set D = max Cf 1 to simplify the Faà di Bruno bound
  set D := max Cf 1
  have hD_pos : 0 < D := lt_max_of_lt_right one_pos
  -- Key bound: max(Cf*(1+‖v‖)^kf, 1) ≤ D * (1+‖v‖)^kf
  have hD_bound : ∀ v : V,
      max (Cf * (1 + ‖v‖) ^ kf) 1 ≤ D * (1 + ‖v‖) ^ kf := by
    intro v
    have h1v : 1 ≤ (1 + ‖v‖) ^ kf :=
      one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg v))
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left Cf 1) (by positivity)
    · calc (1 : ℝ) ≤ D * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ D * (1 + ‖v‖) ^ kf := mul_le_mul_of_nonneg_left h1v hD_pos.le
  -- Faà di Bruno bound with C = exp(f(v)):
  -- ‖iteratedFDeriv ℝ n (exp ∘ f) v‖ ≤ n! * exp(f(v)) * (D * (1+‖v‖)^kf)^n
  have hfdb : ∀ v : V,
      ‖iteratedFDeriv ℝ n (exp ∘ f) v‖ ≤
        ↑(n !) * exp (f v) * (D * (1 + ‖v‖) ^ kf) ^ n := by
    intro v
    calc ‖iteratedFDeriv ℝ n (exp ∘ f) v‖
        ≤ ↑(n !) * exp (f v) * (max (Cf * (1 + ‖v‖) ^ kf) 1) ^ n := by
          apply norm_iteratedFDeriv_comp_le Real.contDiff_exp hf_smooth (mod_cast le_top) v
          · intro i _hi
            exact (norm_iteratedFDeriv_exp (f v) i).le
          · intro i hi hi'
            calc ‖iteratedFDeriv ℝ i f v‖ ≤ Cf * (1 + ‖v‖) ^ kf := hCf i hi' v
              _ ≤ max (Cf * (1 + ‖v‖) ^ kf) 1 := le_max_left _ _
              _ ≤ (max (Cf * (1 + ‖v‖) ^ kf) 1) ^ i :=
                le_self_pow₀ (le_max_right _ _) (by omega)
      _ ≤ ↑(n !) * exp (f v) * (D * (1 + ‖v‖) ^ kf) ^ n := by
          gcongr
          · exact mul_nonneg (Nat.cast_nonneg') (exp_nonneg _)
          · exact hD_bound v
  -- Full pointwise bound on the decay function:
  -- ‖v‖^k * ‖iteratedFDeriv ...‖ ≤ C' * (1+‖v‖)^m * exp(-b*‖v‖²)
  set C' := (↑(n !) : ℝ) * D ^ n
  have hC'_nonneg : 0 ≤ C' := mul_nonneg (Nat.cast_nonneg') (pow_nonneg hD_pos.le _)
  set m := k + kf * n
  have hbound : ∀ v : V,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun v => exp (-b * ‖v‖ ^ 2)) v‖ ≤
        C' * ((1 + ‖v‖) ^ m * exp (-b * ‖v‖ ^ 2)) := by
    intro v
    rw [hf_eq]
    calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (exp ∘ f) v‖
        ≤ ‖v‖ ^ k * (↑(n !) * exp (f v) * (D * (1 + ‖v‖) ^ kf) ^ n) := by
          gcongr; exact hfdb v
      _ = ‖v‖ ^ k * (↑(n !) * exp (-b * ‖v‖ ^ 2) * (D ^ n * (1 + ‖v‖) ^ (kf * n))) := by
          simp only [hf_def, mul_pow, pow_mul]; ring
      _ = C' * (‖v‖ ^ k * (1 + ‖v‖) ^ (kf * n) * exp (-b * ‖v‖ ^ 2)) := by ring
      _ ≤ C' * ((1 + ‖v‖) ^ k * (1 + ‖v‖) ^ (kf * n) * exp (-b * ‖v‖ ^ 2)) := by
          gcongr
          · exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _)
              (pow_nonneg (by linarith [norm_nonneg v]) _)) (exp_nonneg _)
          · exact le_add_of_nonneg_left zero_le_one
      _ = C' * ((1 + ‖v‖) ^ m * exp (-b * ‖v‖ ^ 2)) := by rw [show m = k + kf * n from rfl,
          pow_add]
  -- It remains to show h(v) := (1+‖v‖)^m * exp(-b*‖v‖²) is bounded.
  -- h is continuous and tends to 0 along cocompact (Gaussian beats polynomial).
  set h : V → ℝ := fun v => (1 + ‖v‖) ^ m * exp (-b * ‖v‖ ^ 2)
  have hh_cont : Continuous h := by
    apply Continuous.mul
    · exact (continuous_const.add continuous_norm).pow m
    · exact (contDiff_gaussianIPS (b := b)).continuous
  -- h → 0 along cocompact: factor through ‖v‖ → ∞
  have hh_tendsto : Tendsto h (cocompact V) (𝓝 0) := by
    have : ProperSpace V := FiniteDimensional.proper ℝ V
    -- Compose: h = h₀ ∘ ‖·‖ where h₀(t) = (1+t)^m * exp(-bt²)
    -- and ‖v‖ → ∞ along cocompact V
    suffices hsuff : Tendsto (fun t : ℝ => (1 + t) ^ m * exp (-b * t ^ 2)) atTop (𝓝 0) by
      exact (hsuff.comp tendsto_norm_cocompact_atTop).congr (fun v => by simp [h])
    -- (1+t)^m * exp(-bt²) → 0 as t → +∞
    -- Strategy: (1+t)^m ≤ (2t)^m for t ≥ 1, so it's O(t^m * exp(-bt²)) which → 0.
    have h_oexp : (fun t : ℝ => (1 + t) ^ m * exp (-b * t ^ 2)) =o[atTop]
        (fun t : ℝ => exp (-(1/2) * t)) := by
      calc (fun t : ℝ => (1 + t) ^ m * exp (-b * t ^ 2))
          =O[atTop] (fun t : ℝ => t ^ (m : ℝ) * exp (-b * t ^ 2)) := by
            apply IsBigO.of_bound (2 ^ m)
            filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
            rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (exp_nonneg _)),
              Real.norm_of_nonneg (mul_nonneg (rpow_nonneg (by linarith) _) (exp_nonneg _))]
            calc (1 + t) ^ m * exp (-b * t ^ 2)
                ≤ (2 * t) ^ m * exp (-b * t ^ 2) := by gcongr; linarith
              _ = 2 ^ m * (t ^ (m : ℝ) * exp (-b * t ^ 2)) := by
                  rw [mul_pow, ← rpow_natCast t m, mul_assoc]
        _ =o[atTop] (fun t : ℝ => exp (-(1/2) * t)) :=
            rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb m
    exact h_oexp.tendsto_zero_of_tendsto
      (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/2 : ℝ) < 0)))
  -- h continuous and → 0 implies bounded
  -- Use: continuous + tends to 0 at cocompact on a proper space ⟹ bounded
  have : ProperSpace V := FiniteDimensional.proper ℝ V
  obtain ⟨C_h, hC_h⟩ : ∃ C_h : ℝ, ∀ v : V, h v ≤ C_h := by
    -- Strategy: h → 0 at cocompact, so outside a compact set |h(v)| < 1.
    -- On the compact set, h is bounded by compactness. Take the max.
    obtain ⟨K, hK, hKh⟩ := mem_cocompact.mp (hh_tendsto (Metric.ball_mem_nhds 0 one_pos))
    -- h is bounded on K by hK.isCompact + continuity
    by_cases hKne : K.Nonempty
    · obtain ⟨v₀, _, hv₀⟩ := hK.exists_isMaxOn hKne hh_cont.continuousOn
      refine ⟨max (h v₀) 1, fun v => ?_⟩
      by_cases hv : v ∈ K
      · exact (hv₀ hv).trans (le_max_left _ _)
      · have := hKh (Set.mem_compl hv)
        rw [Metric.mem_ball, Real.dist_eq] at this
        have h_nonneg : 0 ≤ h v :=
          mul_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _) (exp_nonneg _)
        linarith [abs_lt.mp this]
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      -- K is empty, so h is < 1 everywhere
      refine ⟨1, fun v => ?_⟩
      have := hKh (by simp [hKne])
      rw [Metric.mem_ball, Real.dist_eq] at this
      have h_nonneg : 0 ≤ h v :=
        mul_nonneg (pow_nonneg (by linarith [norm_nonneg v]) _) (exp_nonneg _)
      linarith [abs_lt.mp this]
  exact ⟨C' * C_h, fun v => (hbound v).trans (mul_le_mul_of_nonneg_left (hC_h v) hC'_nonneg)⟩

/-- The Gaussian `v ↦ exp (-b * ‖v‖ ^ 2)` on a finite-dimensional real inner product space,
as a Schwartz function. -/
def gaussianSchwartzIPS (hb : 0 < b) : 𝓢(V, ℝ) where
  toFun := fun v => exp (-b * ‖v‖ ^ 2)
  smooth' := contDiff_gaussianIPS
  decay' k n := gaussianIPS_decay hb k n

@[simp]
theorem gaussianSchwartzIPS_apply (hb : 0 < b) (v : V) :
    gaussianSchwartzIPS hb v = exp (-b * ‖v‖ ^ 2) := rfl

end GaussianSchwartz

/-! ## The 1-dimensional Gaussian as a Schwartz function -/

section OneDimensional

variable {b : ℝ}

/-- The 1-d Gaussian `x ↦ exp (-b * x ^ 2)` is smooth. -/
theorem contDiff_gaussian : ContDiff ℝ ∞ (fun x : ℝ => exp (-b * x ^ 2)) := by
  have : (fun x : ℝ => exp (-b * x ^ 2)) = (fun x : ℝ => exp (-b * ‖x‖ ^ 2)) := by
    ext x; simp [sq_abs, norm_eq_abs]
  rw [this]
  exact contDiff_gaussianIPS

/-- The 1-dimensional Gaussian `x ↦ exp (-b * x ^ 2)` as a Schwartz function. -/
def gaussianSchwartz (hb : 0 < b) : 𝓢(ℝ, ℝ) := by
  have heq : (fun x : ℝ => exp (-b * x ^ 2)) = (fun x : ℝ => exp (-b * ‖x‖ ^ 2)) := by
    ext x; simp [sq_abs, norm_eq_abs]
  exact {
    toFun := fun x => exp (-b * x ^ 2)
    smooth' := contDiff_gaussian
    decay' := fun k n => by rw [show (fun x : ℝ => exp (-b * x ^ 2)) =
        (fun x : ℝ => exp (-b * ‖x‖ ^ 2)) from heq]; exact gaussianIPS_decay hb k n }

@[simp]
theorem gaussianSchwartz_apply (hb : 0 < b) (x : ℝ) :
    gaussianSchwartz hb x = exp (-b * x ^ 2) := rfl

end OneDimensional
