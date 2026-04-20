/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Duality of `Lp` spaces: the `L∞ → (L¹)*` isometric embedding

For a finite measure `μ` and a scalar field `𝕜` (either `ℝ` or `ℂ`, i.e., any `RCLike` field),
the pairing `(g, f) ↦ ∫ x, g x * f x ∂μ` defines an isometric `𝕜`-linear embedding
`Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`. Surjectivity (hence the full
`Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)` equivalence) is proved in a follow-up using
Radon–Nikodym.

## Main declarations

* `MeasureTheory.Lp.lInftyL1Pairing`: the bilinear `Lp 𝕜 ∞ μ × Lp 𝕜 1 μ → 𝕜` pairing given by
  pointwise multiplication.
* `MeasureTheory.Lp.lInftyToL1Dualₗᵢ`: the natural pairing `g f ↦ ∫ x, g x * f x ∂μ` packaged
  as an isometric `𝕜`-linear embedding `Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`.

## Implementation notes

The forward pairing `Lp 𝕜 ∞ μ × Lp 𝕜 1 μ → 𝕜` is provided by `ContinuousLinearMap.lpPairing`
(see `Mathlib/MeasureTheory/Function/Holder.lean`) instantiated with the multiplication bilinear
form on `𝕜`. We add only the (Hölder-style) operator norm bound and the matching lower bound
(sign-function test) needed to package it as a `LinearIsometry`.

## References

* Rudin, *Real and Complex Analysis*, Theorem 6.16.
-/

@[expose] public section

open ENNReal MeasureTheory NNReal

noncomputable section

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]

namespace Lp

/-- The bilinear `Lp 𝕜 ∞ μ × Lp 𝕜 1 μ → 𝕜` pairing given by pointwise multiplication. -/
noncomputable abbrev lInftyL1Pairing (μ : Measure α) : Lp 𝕜 ∞ μ →L[𝕜] Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ ∞ 1

/-! ### The isometry lower bound (scalar case) -/

section IsometryLowerBound

variable [IsFiniteMeasure μ]

/-- The lower bound for the L∞-L¹ pairing. -/
lemma norm_le_norm_lpPairing_mul_apply (g : Lp 𝕜 ∞ μ) : ‖g‖ ≤ ‖lInftyL1Pairing μ g‖ := by
  let P := lInftyL1Pairing (𝕜 := 𝕜) μ
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  by_cases hg : ε < ‖g‖
  swap
  · linarith [norm_nonneg (P g), not_lt.mp hg]
  let c : ℝ := ‖g‖ - ε
  have hc_nn : 0 ≤ c := by linarith
  have hc_lt : c < ‖g‖ := by linarith
  have hg_ae : AEStronglyMeasurable (g : α → 𝕜) μ := (Lp.memLp g).1
  let g₀ : α → 𝕜 := hg_ae.mk _
  have hg₀_sm : StronglyMeasurable g₀ := hg_ae.stronglyMeasurable_mk
  have hg_eq : (g : α → 𝕜) =ᵐ[μ] g₀ := hg_ae.ae_eq_mk
  let S : Set α := {x | c < ‖g₀ x‖}
  have hS_meas : MeasurableSet S := measurableSet_lt measurable_const hg₀_sm.measurable.norm
  have hS_pos : μ S ≠ 0 := by
    rw [← measure_congr (hg_eq.mono fun x hx ↦ by
      change (c < ‖(g : α → 𝕜) x‖) = (c < ‖g₀ x‖); rw [hx])]
    exact measure_norm_gt_pos_of_lt_norm hc_nn hc_lt
  set r : ℝ := μ.real S with hr
  have hr_pos : 0 < r := ENNReal.toReal_pos hS_pos (measure_lt_top μ S).ne
  let ψ : α → 𝕜 := S.indicator fun y ↦ star (g₀ y) / (‖g₀ y‖ : 𝕜)
  have hψ_meas : StronglyMeasurable ψ :=
    ((continuous_star.measurable.div (RCLike.continuous_ofReal.comp
      continuous_norm).measurable).comp hg₀_sm.measurable).stronglyMeasurable.indicator hS_meas
  have hψ_bound (x) : ‖ψ x‖ ≤ S.indicator (fun _ ↦ (1 : ℝ)) x := by
    simp only [ψ, Set.indicator]
    split_ifs <;> simp [norm_div, div_self_le_one]
  have hψ_int : Integrable ψ μ := .of_bound hψ_meas.aestronglyMeasurable 1 <| ae_of_all μ fun x ↦
    (hψ_bound x).trans <| Set.indicator_le_self' (fun _ _ ↦ zero_le_one) x
  let ψ_Lp : Lp 𝕜 1 μ := hψ_int.toL1 ψ
  have hψ_Lp_eq : (ψ_Lp : α → 𝕜) =ᵐ[μ] ψ := Integrable.coeFn_toL1 hψ_int
  have hψ_Lp_norm : ‖ψ_Lp‖ ≤ r := by
    rw [hr, L1.norm_of_fun_eq_integral_norm, ← integral_indicator_one hS_meas]
    exact integral_mono_ae hψ_int.norm ((integrable_indicator_iff hS_meas).mpr
      (integrable_const (1 : ℝ)).integrableOn) (ae_of_all μ hψ_bound)
  have hg₀_int_S : IntegrableOn (fun x ↦ ‖g₀ x‖) S μ :=
    ((integrable_const ‖g‖).mono' hg₀_sm.measurable.norm.aestronglyMeasurable
      ((ae_norm_le_norm g).mp (hg_eq.mono fun _ hxg hx ↦ by
        rwa [Real.norm_eq_abs, abs_norm, ← hxg]))).integrableOn
  have h_pairing : P g ψ_Lp = ((∫ x in S, ‖g₀ x‖ ∂μ : ℝ) : 𝕜) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral,
      integral_congr_ae (g := S.indicator (fun y ↦ (‖g₀ y‖ : 𝕜))) ?_,
      integral_indicator hS_meas, integral_ofReal]
    filter_upwards [hg_eq, hψ_Lp_eq] with x hx hψx
    simp only [hx, hψx, ψ, Set.indicator]
    split_ifs <;> simp [ContinuousLinearMap.mul_apply', RCLike.star_def, ← mul_div_assoc,
      RCLike.mul_conj, sq, mul_self_div_self]
  have h_mul : c * r ≤ ‖P g‖ * r :=
    calc c * r
        = ∫ _ in S, c ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, ‖g₀ x‖ ∂μ := setIntegral_mono_on (integrable_const c).integrableOn
          hg₀_int_S hS_meas fun _ hx ↦ hx.le
      _ = ‖P g ψ_Lp‖ := by rw [h_pairing, RCLike.norm_ofReal,
            abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      _ ≤ ‖P g‖ * ‖ψ_Lp‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P g‖ * r := mul_le_mul_of_nonneg_left hψ_Lp_norm (norm_nonneg _)
  linarith [le_of_mul_le_mul_right h_mul hr_pos]

/-- The natural pairing `g f ↦ ∫ x, g x * f x ∂μ` between `Lp 𝕜 ∞ μ` and `Lp 𝕜 1 μ`, packaged
as an isometric `𝕜`-linear embedding into the strong dual of `Lp 𝕜 1 μ` (for finite `μ`). -/
def lInftyToL1Dualₗᵢ : Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) where
  toLinearMap := (lInftyL1Pairing μ).toLinearMap
  norm_map' g := le_antisymm
    ((ContinuousLinearMap.norm_lpPairing_apply_le _ g).trans <|
      mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜))
    (norm_le_norm_lpPairing_mul_apply g)

@[simp]
lemma lInftyToL1Dualₗᵢ_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    lInftyToL1Dualₗᵢ g f = ∫ x, g x * f x ∂μ := by
  simp [lInftyToL1Dualₗᵢ, ContinuousLinearMap.lpPairing_eq_integral]

end IsometryLowerBound

end Lp

end MeasureTheory
