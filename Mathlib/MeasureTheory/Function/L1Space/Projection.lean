/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Metric Projections and Birkhoff–James Orthogonality in L₁ Spaces

This file establishes dual and sign-weighted integral characterizations of the null layer
`P_V⁻¹(0)` of the metric projection in normed and `L₁(Ω, μ)` spaces using the Hahn–Banach
extension theorem.

## Main results

* `MeasureTheory.best_approx_zero_iff_exists_annihilator`: via the Hahn–Banach theorem, `0` is a
  best approximation to `u` from `V` if and only if there exists `φ : X →L[ℝ] ℝ` with `‖φ‖ ≤ 1`,
  `∀ v ∈ V, φ v = 0`, and `φ u = ‖u‖`.
* `MeasureTheory.mem_zeroLayer_of_Linfty_annihilator`: sufficiency of an `L∞` witness `g` with
  `|g(ω)| ≤ 1` a.e., `∫ v * g dμ = 0` for all `v ∈ V`, and `g(ω) = sign(u(ω))` a.e. on `{u ≠ 0}`.
* `MeasureTheory.sign_weighted_integral_ineq_of_Linfty_annihilator`: necessity of the
  sign-weighted integral inequality `∫_{u ≠ 0} v * sign(u) dμ + ∫_{u = 0} |v| dμ ≥ 0`.

## References

* E. S. Markov, *On Linear Metric Projections in Non-Reflexive Banach Spaces: Proximinal Lattices,
  Multivalued Boundaries and Linear Selections*, Zenodo (2026),
  [DOI: 10.5281/zenodo.24318041](https://doi.org).
* I. Singer, *Best Approximation in Normed Linear Spaces by Elements of Linear Subspaces*,
  Springer-Verlag, 1970.
-/

@[expose] public section

open Set

namespace MeasureTheory

section HahnBanachDuality

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Hahn–Banach characterization of best approximation:** in any real normed space `X`, `0`
is an element of best approximation to `u` from a submodule `V` (`∀ v ∈ V, ‖u‖ ≤ ‖u - v‖`) if
and only if there exists a norm-one annihilator `φ : X →L[ℝ] ℝ` vanishing on `V` such that
`φ u = ‖u‖`. -/
theorem best_approx_zero_iff_exists_annihilator (V : Submodule ℝ X) (u : X) :
    (∀ v ∈ V, ‖u‖ ≤ ‖u - v‖) ↔
      ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ (∀ v ∈ V, φ v = 0) ∧ φ u = ‖u‖ := by
  refine ⟨fun h_best => ?_, fun ⟨φ, hφ_norm, hφ_V, hφ_u⟩ v hv => ?_⟩
  · by_cases hu : u = 0
    · refine ⟨0, by simp, fun _ _ => rfl, by simp [hu]⟩
    · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hu_not_mem : u ∉ V := by
        intro huV
        have h0 := h_best u huV
        rw [sub_self, norm_zero] at h0
        linarith
      let W : Submodule ℝ X := V ⊔ Submodule.span ℝ {u}
      have h_decomp : ∀ w ∈ W, ∃ p : V × ℝ, w = (p.1 : X) + p.2 • u := by
        intro w hw
        rcases Submodule.mem_sup.mp hw with ⟨v, hv, z, hz, rfl⟩
        rcases Submodule.mem_span_singleton.mp hz with ⟨c, rfl⟩
        exact ⟨(⟨v, hv⟩, c), rfl⟩
      have h_uniq : ∀ {v₁ v₂ : X} {c₁ c₂ : ℝ},
          v₁ ∈ V → v₂ ∈ V → v₁ + c₁ • u = v₂ + c₂ • u → v₁ = v₂ ∧ c₁ = c₂ := by
        intro v₁ v₂ c₁ c₂ hv₁ hv₂ heq
        have hc : c₁ = c₂ := by
          by_contra hne
          have hsub : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
          have h_vec : (c₁ - c₂) • u = v₂ - v₁ := by
            rw [sub_smul, sub_eq_iff_eq_add]
            calc c₁ • u = (v₁ + c₁ • u) - v₁ := by abel
              _ = (v₂ + c₂ • u) - v₁ := by rw [heq]
              _ = v₂ - v₁ + c₂ • u := by abel
          have hu_in : u ∈ V := by
            have := V.smul_mem (c₁ - c₂)⁻¹ (V.sub_mem hv₂ hv₁)
            rwa [← h_vec, inv_smul_smul₀ hsub] at this
          exact hu_not_mem hu_in
        subst hc
        exact ⟨add_right_cancel heq, rfl⟩
      let φ_lin : W →ₗ[ℝ] ℝ :=
        { toFun := fun w => (h_decomp w.1 w.2).choose.2 * ‖u‖
          map_add' := fun w₁ w₂ => by
            set p₁ := (h_decomp w₁.1 w₁.2).choose
            set p₂ := (h_decomp w₂.1 w₂.2).choose
            set p₁₂ := (h_decomp (w₁ + w₂).1 (w₁ + w₂).2).choose
            have heq₁ : w₁.1 = (p₁.1 : X) + p₁.2 • u :=
              (h_decomp w₁.1 w₁.2).choose_spec
            have heq₂ : w₂.1 = (p₂.1 : X) + p₂.2 • u :=
              (h_decomp w₂.1 w₂.2).choose_spec
            have heq₁₂ : w₁.1 + w₂.1 = (p₁₂.1 : X) + p₁₂.2 • u :=
              (h_decomp (w₁ + w₂).1 (w₁ + w₂).2).choose_spec
            have h_sum : ((p₁.1 + p₂.1 : V) : X) + (p₁.2 + p₂.2) • u =
                (p₁₂.1 : X) + p₁₂.2 • u := by
              push_cast
              rw [add_smul, add_add_add_comm, ← heq₁, ← heq₂, heq₁₂]
            have hc_eq := (h_uniq (p₁.1 + p₂.1).2 p₁₂.1.2 h_sum).2
            rw [← hc_eq, add_mul]
          map_smul' := fun r w => by
            set p := (h_decomp w.1 w.2).choose
            set pr := (h_decomp (r • w).1 (r • w).2).choose
            have heq : w.1 = (p.1 : X) + p.2 • u :=
              (h_decomp w.1 w.2).choose_spec
            have heqr : r • w.1 = (pr.1 : X) + pr.2 • u :=
              (h_decomp (r • w).1 (r • w).2).choose_spec
            have h_sc : ((r • p.1 : V) : X) + (r * p.2) • u =
                (pr.1 : X) + pr.2 • u := by
              push_cast
              rw [mul_smul, ← smul_add, ← heq, heqr]
            have hc_eq := (h_uniq (r • p.1).2 pr.1.2 h_sc).2
            simp only [RingHom.id_apply, smul_eq_mul, ← hc_eq, mul_assoc] }
      have hφ_eval : ∀ {v : X} {c : ℝ} (hv : v ∈ V) (hwW : v + c • u ∈ W),
          φ_lin ⟨v + c • u, hwW⟩ = c * ‖u‖ := by
        intro v c hv hwW
        dsimp [φ_lin]
        set p := (h_decomp (v + c • u) hwW).choose
        have heqP : v + c • u = (p.1 : X) + p.2 • u :=
          (h_decomp (v + c • u) hwW).choose_spec
        have hc_eq := (h_uniq hv p.1.2 heqP).2
        rw [← hc_eq]
      have h_bound : ∀ w : W, ‖φ_lin w‖ ≤ 1 * ‖w‖ := by
        rintro ⟨w, hwW⟩
        rw [one_mul]
        rcases h_decomp w hwW with ⟨⟨⟨v, hv⟩, c⟩, rfl⟩
        rw [hφ_eval hv hwW, Real.norm_eq_abs, abs_mul, abs_norm]
        by_cases hc0 : c = 0
        · simp [hc0]
        · have h_best_c := h_best ((-c⁻¹) • v) (V.smul_mem (-c⁻¹) hv)
          have h_norm_eq : ‖(⟨v + c • u, hwW⟩ : W)‖ = |c| * ‖u - (-c⁻¹) • v‖ := by
            change ‖v + c • u‖ = |c| * ‖u - (-c⁻¹) • v‖
            have h_id : v + c • u = c • (u - (-c⁻¹) • v) := by
              rw [smul_sub, ← mul_smul, mul_neg, mul_inv_cancel₀ hc0, neg_one_smul,
                sub_neg_eq_add, add_comm]
            rw [h_id, norm_smul, Real.norm_eq_abs]
          rw [h_norm_eq]
          exact mul_le_mul_of_nonneg_left h_best_c (abs_nonneg c)
      let φ_cont : W →L[ℝ] ℝ := φ_lin.mkContinuous 1 h_bound
      obtain ⟨φ, hφ_ext, hφ_norm⟩ := exists_extension_norm_eq W φ_cont
      refine ⟨φ, ?_, fun v hv => ?_, ?_⟩
      · rw [hφ_norm]
        exact LinearMap.mkContinuous_norm_le _ zero_le_one _
      · have hvW : v + (0 : ℝ) • u ∈ W := by
          rw [zero_smul, add_zero]
          exact Submodule.mem_sup_left hv
        have h1 := hφ_ext ⟨v + (0 : ℝ) • u, hvW⟩
        simp only [zero_smul, add_zero] at h1
        rw [h1]
        have h2 := hφ_eval hv hvW
        simp only [zero_smul, add_zero, zero_mul] at h2
        exact h2
      · have huW : (0 : X) + (1 : ℝ) • u ∈ W := by
          rw [zero_add, one_smul]
          exact Submodule.mem_sup_right (Submodule.subset_span (mem_singleton u))
        have h1 := hφ_ext ⟨(0 : X) + (1 : ℝ) • u, huW⟩
        simp only [zero_add, one_smul] at h1
        rw [h1]
        have h2 := hφ_eval V.zero_mem huW
        simp only [zero_add, one_smul, one_mul] at h2
        exact h2
  · calc ‖u‖ = φ u := hφ_u.symm
      _ = φ (u - v) := by rw [map_sub, hφ_V v hv, sub_zero]
      _ ≤ |φ (u - v)| := le_abs_self _
      _ = ‖φ (u - v)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ‖ * ‖u - v‖ := φ.le_opNorm (u - v)
      _ ≤ 1 * ‖u - v‖ := mul_le_mul_of_nonneg_right hφ_norm (norm_nonneg _)
      _ = ‖u - v‖ := one_mul _

end HahnBanachDuality
section L1IntegralCriteria

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Sufficiency in L₁(Ω) (Theorem 2, part 1):** if `u ∈ L₁(μ)` and there exists an `L∞` witness
`g : Ω → ℝ` bounded by `1` a.e. such that `∫ v * g dμ = 0` for all `v ∈ V` and `g = sign(u)` a.e.
on `{u ≠ 0}`, then `0` is a best `L₁`-approximation to `u` from `V`. -/
theorem mem_zeroLayer_of_Linfty_annihilator (V : Submodule ℝ (Ω → ℝ)) (u : Ω → ℝ)
    (hu_int : Integrable u μ)
    (g : Ω → ℝ)
    (hg_bound : ∀ᵐ ω ∂μ, |g ω| ≤ 1)
    (hg_ann : ∀ v ∈ V, ∫ ω, v ω * g ω ∂μ = 0)
    (hg_sign : ∀ᵐ ω ∂μ, u ω ≠ 0 → g ω = Real.sign (u ω))
    (h_int_uvg : ∀ v ∈ V, Integrable (fun ω => (u ω - v ω) * g ω) μ)
    (h_int_uv : ∀ v ∈ V, Integrable (fun ω => |u ω - v ω|) μ) :
    ∀ v ∈ V, ∫ ω, |u ω| ∂μ ≤ ∫ ω, |u ω - v ω| ∂μ := by
  intro v hv
  have h_ae_eq : (fun ω => u ω * g ω) =ᵐ[μ] (fun ω => |u ω|) := by
    filter_upwards [hg_sign] with ω h_sgn
    by_cases hu0 : u ω = 0
    · simp [hu0]
    · rw [h_sgn hu0]
      rcases lt_trichotomy (u ω) 0 with hlt | h_eq | hgt
      · rw [Real.sign_of_neg hlt, abs_of_neg hlt, mul_neg_one]
      · exact False.elim (hu0 h_eq)
      · rw [Real.sign_of_pos hgt, abs_of_pos hgt, mul_one]
  have h_int_u : ∫ ω, |u ω| ∂μ = ∫ ω, (u ω - v ω) * g ω ∂μ := by
    calc ∫ ω, |u ω| ∂μ = ∫ ω, u ω * g ω ∂μ := integral_congr_ae h_ae_eq.symm
      _ = ∫ ω, u ω * g ω ∂μ - ∫ ω, v ω * g ω ∂μ := by rw [hg_ann v hv, sub_zero]
      _ = ∫ ω, (u ω * g ω - v ω * g ω) ∂μ := by
        have h1 : Integrable (fun ω => u ω * g ω) μ := hu_int.norm.congr h_ae_eq.symm
        have h2 : Integrable (fun ω => v ω * g ω) μ := by
          have h_sub : (fun ω => v ω * g ω) =
              fun ω => u ω * g ω - (u ω - v ω) * g ω := by ext ω; ring
          rw [h_sub]
          exact h1.sub (h_int_uvg v hv)
        exact (integral_sub h1 h2).symm
      _ = ∫ ω, (u ω - v ω) * g ω ∂μ := by
        congr 1; ext ω; ring
  rw [h_int_u]
  apply integral_mono_ae (h_int_uvg v hv) (h_int_uv v hv)
  filter_upwards [hg_bound] with ω hb
  calc (u ω - v ω) * g ω ≤ |(u ω - v ω) * g ω| := le_abs_self _
    _ = |u ω - v ω| * |g ω| := abs_mul _ _
    _ ≤ |u ω - v ω| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = |u ω - v ω| := mul_one _

/-- **Sign-weighted integral inequality in L₁(Ω) (Theorem 2, part 2):** under the existence of a
dual `L∞` annihilator `g`, every `v ∈ V` satisfies the sign-weighted integral balance
`∫_{u ≠ 0} v * sign(u) dμ + ∫_{u = 0} |v| dμ ≥ 0`. -/
theorem sign_weighted_integral_ineq_of_Linfty_annihilator (V : Submodule ℝ (Ω → ℝ)) (u : Ω → ℝ)
    (hu_meas : Measurable u)
    (g : Ω → ℝ)
    (hg_bound : ∀ᵐ ω ∂μ, |g ω| ≤ 1)
    (hg_ann : ∀ v ∈ V, ∫ ω, v ω * g ω ∂μ = 0)
    (hg_sign : ∀ᵐ ω ∂μ, u ω ≠ 0 → g ω = Real.sign (u ω))
    (h_int_sgn : ∀ v ∈ V, Integrable (fun ω => {ω | u ω ≠ 0}.indicator
      (fun t => v t * Real.sign (u t)) ω) μ)
    (h_int_abs : ∀ v ∈ V, Integrable (fun ω => {ω | u ω = 0}.indicator
      (fun t => |v t|) ω) μ)
    (h_int_vg : ∀ v ∈ V, Integrable (fun ω => v ω * g ω) μ) :
    ∀ v ∈ V, 0 ≤ (∫ ω in {ω | u ω ≠ 0}, v ω * Real.sign (u ω) ∂μ) +
      (∫ ω in {ω | u ω = 0}, |v ω| ∂μ) := by
  intro v hv
  have h_decomp_ae : ∀ᵐ ω ∂μ, v ω * g ω ≤
      {ω | u ω ≠ 0}.indicator (fun t => v t * Real.sign (u t)) ω +
      {ω | u ω = 0}.indicator (fun t => |v t|) ω := by
    filter_upwards [hg_bound, hg_sign] with ω hb h_sgn
    by_cases hu0 : u ω = 0
    · simp only [mem_ofPred_eq, hu0, ne_eq, not_true_eq_false, not_false_eq_true,
        indicator_of_notMem, indicator_of_mem, zero_add]
      calc v ω * g ω ≤ |v ω * g ω| := le_abs_self _
        _ = |v ω| * |g ω| := abs_mul _ _
        _ ≤ |v ω| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = |v ω| := mul_one _
    · simp only [mem_ofPred_eq, hu0, ne_eq, not_false_eq_true, indicator_of_mem,
        indicator_of_notMem, add_zero, h_sgn hu0, le_refl]
  have h_int_le := integral_mono_ae (h_int_vg v hv) ((h_int_sgn v hv).add (h_int_abs v hv))
    h_decomp_ae
  have h_meas_ne : MeasurableSet {ω | u ω ≠ 0} := hu_meas (measurableSet_singleton 0).compl
  have h_meas_eq : MeasurableSet {ω | u ω = 0} := hu_meas (measurableSet_singleton 0)
  rw [hg_ann v hv, Pi.add_def, integral_add (h_int_sgn v hv) (h_int_abs v hv),
    integral_indicator h_meas_ne, integral_indicator h_meas_eq] at h_int_le
  exact h_int_le

end L1IntegralCriteria

end MeasureTheory
