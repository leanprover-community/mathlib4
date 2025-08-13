/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developed in `Mathlib/Analysis/Asymptotics/Asymptotics.lean`.
-/


open Filter Asymptotics

open Topology

section NormedField

/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜}
    {f : 𝕜 → E} (h : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (norm ∘ f)) :
    f =o[𝓝[≠] a] fun x => (x - a)⁻¹ := by
  refine (h.isBigO_const (one_ne_zero' ℝ)).trans_isLittleO (isLittleO_const_left.2 <| Or.inr ?_)
  simp only [Function.comp_def, norm_inv]
  exact (tendsto_norm_sub_self_nhdsNE a).inv_tendsto_nhdsGT_zero

end NormedField

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

theorem pow_div_pow_eventuallyEq_atTop {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_gt_atTop (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne']

theorem pow_div_pow_eventuallyEq_atBot {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atBot] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_lt_atBot (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne]

theorem tendsto_pow_div_pow_atTop_atTop {p q : ℕ} (hpq : q < p) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  omega

theorem tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ}
    (hpq : p < q) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  omega

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type*} [NormedField 𝕜]

theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[atTop] fun x => x ^ q := by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type*} {u v : α → 𝕜} {l : Filter α}
    (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) :
    Tendsto (fun x => ‖v x‖) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀ _ hc.ne.symm]

end NormedLinearOrderedField

section Real

theorem Asymptotics.IsEquivalent.rpow {α : Type*} {u v : α → ℝ} {l : Filter α}
    (hv : 0 ≤ v) (h : u ~[l] v) {r : ℝ} :
    u ^ r ~[l] v ^ r := by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x ↦ x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x ↦ φ x ^ r * v x ^ r
  filter_upwards [Tendsto.eventually_const_lt (zero_lt_one) hφ, huφv] with x hφ_pos huv'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hv x), huv']

open Finset

theorem Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : ℕ → α} {g : ℕ → ℝ}
    (h : f =o[atTop] g) (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => ∑ i ∈ range n, g i := by
  have A : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ‖∑ i ∈ range n, g i‖ = ∑ i ∈ range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [A, eventually_atTop] using isLittleO_iff.mp h (half_pos εpos)
  have : (fun _ : ℕ => ∑ i ∈ range N, f i) =o[atTop] fun n : ℕ => ∑ i ∈ range n, g i := by
    apply isLittleO_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [isLittleO_iff.1 this (half_pos εpos), Ici_mem_atTop N] with n hn Nn
  calc
    ‖∑ i ∈ range n, f i‖ = ‖(∑ i ∈ range N, f i) + ∑ i ∈ Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ ≤ ‖∑ i ∈ range N, f i‖ + ‖∑ i ∈ Ico N n, f i‖ := norm_add_le _ _
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ ↦ mul_nonneg (half_pos εpos).le (hg i)
      · rw [range_eq_Ico]
        exact Ico_subset_Ico (zero_le _) le_rfl
    _ ≤ ε / 2 * ‖∑ i ∈ range n, g i‖ + ε / 2 * ∑ i ∈ range n, g i := by rw [← mul_sum]; gcongr
    _ = ε * ‖∑ i ∈ range n, g i‖ := by
      simp only [B]
      ring

theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α]
    {f : ℕ → α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => (n : ℝ) := by
  have := ((isLittleO_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ nposℝ.ne', one_smul]
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    rw [Algebra.id.smul_eq_mul, inv_mul_cancel₀ nposℝ.ne']

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul

end Real

section NormedLinearOrderedField

variable {R : Type*} [NormedField R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

theorem Asymptotics.isEquivalent_nat_floor :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ tendsto_nat_floor_div_atTop
  filter_upwards with x hx using by rw [hx, Nat.floor_zero, Nat.cast_eq_zero]

theorem Asymptotics.isEquivalent_nat_ceil :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ tendsto_nat_ceil_div_atTop
  filter_upwards with x hx using by rw [hx, Nat.ceil_zero, Nat.cast_eq_zero]

end NormedLinearOrderedField
