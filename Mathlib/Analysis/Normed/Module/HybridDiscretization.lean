/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Hybrid L₁ ⊕ ℓ₁ Spaces, Quantized Linear Selectors, and Combinatorial Complexity

This file formalizes the main results on discretization of continuous linear metric selectors
in non-reflexive Banach spaces with mixed structure `L₁(Ω, Σ, μ) ⊕ ℓ₁(ℕ)`:

* `MeasureTheory.hybrid_sign_weighted_ineq_of_annihilator`: joint sign-weighted integral-discrete
  balance inequality on hybrid spaces `L₁(Ω, μ) ⊕ ℓ₁(ℕ)` (Theorem 1).
* `ContinuousLinearMap.quantized_selector_error_bound`: uniform error bound
  `‖s(x) - s_ε(x_ε)‖ ≤ ‖I - Q‖ * ε + η * (‖x‖ + ε)` for finite-precision quantized selectors
  (Theorem 2).
* `ContinuousLinearMap.quantized_pipeline_stability`: perturbation stability bound
  `‖s_ε(x + δ) - s_ε(x)‖ ≤ ‖I - Q‖ * ε + η * (2 * ‖x‖ + ε)` for computational pipelines.
* `subsetSum_iff_boolean_shifted_hyperplane` & `partition_iff_bipolar_null_layer`: polynomial-time
  reductions establishing NP-hardness of recognizing binary and bipolar vectors in metric
  projection layers of `ℓ₁^m` (Theorem 3).

## References

* E. S. Markov, *On Discretization of Linear Selections in Non-Reflexive Spaces: Hybrid Spaces,
  Operator Stability and Combinatorial Complexity of Null Layers*, Zenodo (2026),
  [DOI: 10.5281/zenodo.24250160](https://doi.org).
-/

@[expose] public section

open MeasureTheory Set

section HybridSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 1 (Hybrid `L₁(Ω) ⊕ ℓ₁(ℕ)` sign-weighted integral-discrete inequality):**
if `(gc, gd) ∈ L∞(Ω) ⊕ ℓ∞(ℕ)` has unit dual norm (`|gc(t)| ≤ 1` a.e., `|gd(n)| ≤ 1`), annihilates
`V`, and matches `sign(uc)` a.e. on `{uc ≠ 0}` and `sign(ud)` on `{ud ≠ 0}`, then every
`v = (vc, vd) ∈ V` satisfies the joint integral-discrete balance inequality. -/
theorem MeasureTheory.hybrid_sign_weighted_ineq_of_annihilator
    (V : Submodule ℝ ((Ω → ℝ) × (ℕ → ℝ)))
    (uc : Ω → ℝ) (ud : ℕ → ℝ) (huc_meas : Measurable uc)
    (gc : Ω → ℝ) (gd : ℕ → ℝ)
    (hgc_bound : ∀ᵐ t ∂μ, |gc t| ≤ 1)
    (hgd_bound : ∀ n : ℕ, |gd n| ≤ 1)
    (hgc_sign : ∀ᵐ t ∂μ, uc t ≠ 0 → gc t = Real.sign (uc t))
    (hgd_sign : ∀ n : ℕ, ud n ≠ 0 → gd n = Real.sign (ud n))
    (h_ann : ∀ v ∈ V, (∫ t, v.1 t * gc t ∂μ) + (∑' n, v.2 n * gd n) = 0)
    (h_int_sgn : ∀ v ∈ V, Integrable (fun t => {t | uc t ≠ 0}.indicator
      (fun s => v.1 s * Real.sign (uc s)) t) μ)
    (h_int_abs : ∀ v ∈ V, Integrable (fun t => {t | uc t = 0}.indicator
      (fun s => |v.1 s|) t) μ)
    (h_int_vcgc : ∀ v ∈ V, Integrable (fun t => v.1 t * gc t) μ)
    (h_sum_vdgd : ∀ v ∈ V, Summable (fun n => v.2 n * gd n))
    (h_sum_sgn : ∀ v ∈ V, Summable (fun n => {n | ud n ≠ 0}.indicator
      (fun k => v.2 k * Real.sign (ud k)) n))
    (h_sum_abs : ∀ v ∈ V, Summable (fun n => {n | ud n = 0}.indicator
      (fun k => |v.2 k|) n)) :
    ∀ v ∈ V, 0 ≤
      (∫ t in {t | uc t ≠ 0}, v.1 t * Real.sign (uc t) ∂μ) +
      (∑' n, {n | ud n ≠ 0}.indicator (fun k => v.2 k * Real.sign (ud k)) n) +
      ((∫ t in {t | uc t = 0}, |v.1 t| ∂μ) +
       (∑' n, {n | ud n = 0}.indicator (fun k => |v.2 k|) n)) := by
  intro v hv
  have h_cont_ae : ∀ᵐ t ∂μ, v.1 t * gc t ≤
      {t | uc t ≠ 0}.indicator (fun s => v.1 s * Real.sign (uc s)) t +
      {t | uc t = 0}.indicator (fun s => |v.1 s|) t := by
    filter_upwards [hgc_bound, hgc_sign] with t hb h_sgn
    by_cases ht0 : uc t = 0
    · simp only [mem_ofPred_eq, ht0, ne_eq, not_true_eq_false, not_false_eq_true,
        indicator_of_notMem, indicator_of_mem, zero_add]
      calc v.1 t * gc t ≤ |v.1 t * gc t| := le_abs_self _
        _ = |v.1 t| * |gc t| := abs_mul _ _
        _ ≤ |v.1 t| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = |v.1 t| := mul_one _
    · simp only [mem_ofPred_eq, ht0, ne_eq, not_false_eq_true, indicator_of_mem,
        indicator_of_notMem, add_zero, h_sgn ht0, le_refl]
  have h_disc_pt : ∀ n : ℕ, v.2 n * gd n ≤
      {n | ud n ≠ 0}.indicator (fun k => v.2 k * Real.sign (ud k)) n +
      {n | ud n = 0}.indicator (fun k => |v.2 k|) n := by
    intro n
    by_cases hn0 : ud n = 0
    · simp only [mem_ofPred_eq, hn0, ne_eq, not_true_eq_false, not_false_eq_true,
        indicator_of_notMem, indicator_of_mem, zero_add]
      calc v.2 n * gd n ≤ |v.2 n * gd n| := le_abs_self _
        _ = |v.2 n| * |gd n| := abs_mul _ _
        _ ≤ |v.2 n| * 1 := mul_le_mul_of_nonneg_left (hgd_bound n) (abs_nonneg _)
        _ = |v.2 n| := mul_one _
    · simp only [mem_ofPred_eq, hn0, ne_eq, not_false_eq_true, indicator_of_mem,
        indicator_of_notMem, add_zero, hgd_sign n hn0, le_refl]
  have h_int_le := integral_mono_ae (h_int_vcgc v hv) ((h_int_sgn v hv).add (h_int_abs v hv))
    h_cont_ae
  have h_meas_ne : MeasurableSet {t | uc t ≠ 0} := huc_meas (measurableSet_singleton 0).compl
  have h_meas_eq : MeasurableSet {t | uc t = 0} := huc_meas (measurableSet_singleton 0)
  rw [Pi.add_def, integral_add (h_int_sgn v hv) (h_int_abs v hv),
    integral_indicator h_meas_ne, integral_indicator h_meas_eq] at h_int_le
  have h_sum_le := (h_sum_vdgd v hv).tsum_le_tsum h_disc_pt
    ((h_sum_sgn v hv).add (h_sum_abs v hv))
  rw [(h_sum_sgn v hv).tsum_add (h_sum_abs v hv)] at h_sum_le
  have h_tot := add_le_add h_int_le h_sum_le
  rw [h_ann v hv] at h_tot
  linarith

end HybridSpace
section QuantizationAndStability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Theorem 2 (Discretization and finite-precision quantization error bound):**
if `s = I - Q` is a continuous linear selector, `x_ε` approximates `x` within `‖x - x_ε‖ ≤ ε`,
and `s_ε` has relative machine rounding error `‖s(z) - s_ε(z)‖ ≤ η * ‖z‖`, then
`‖s(x) - s_ε(x_ε)‖ ≤ ‖I - Q‖ * ε + η * (‖x‖ + ε)`. -/
theorem ContinuousLinearMap.quantized_selector_error_bound
    (Q : X →L[ℝ] X) (s_eps : X → X) (x x_eps : X) (eps eta : ℝ)
    (h_eta : 0 ≤ eta)
    (h_grid : ‖x - x_eps‖ ≤ eps)
    (h_round : ‖(ContinuousLinearMap.id ℝ X - Q) x_eps - s_eps x_eps‖ ≤ eta * ‖x_eps‖) :
    ‖(ContinuousLinearMap.id ℝ X - Q) x - s_eps x_eps‖ ≤
      ‖ContinuousLinearMap.id ℝ X - Q‖ * eps + eta * (‖x‖ + eps) := by
  let s := ContinuousLinearMap.id ℝ X - Q
  have h_tri : ‖s x - s_eps x_eps‖ ≤ ‖s x - s x_eps‖ + ‖s x_eps - s_eps x_eps‖ :=
    norm_sub_le_norm_sub_add_norm_sub (s x) (s x_eps) (s_eps x_eps)
  have h_lip : ‖s x - s x_eps‖ ≤ ‖s‖ * eps := by
    calc ‖s x - s x_eps‖ = ‖s (x - x_eps)‖ := by rw [← map_sub]
      _ ≤ ‖s‖ * ‖x - x_eps‖ := s.le_opNorm (x - x_eps)
      _ ≤ ‖s‖ * eps := mul_le_mul_of_nonneg_left h_grid (norm_nonneg s)
  have h_x_eps : ‖x_eps‖ ≤ ‖x‖ + eps := by
    have h1 := norm_sub_le x (x - x_eps)
    rw [sub_sub_cancel] at h1
    linarith
  have h_mach : ‖s x_eps - s_eps x_eps‖ ≤ eta * (‖x‖ + eps) :=
    h_round.trans (mul_le_mul_of_nonneg_left h_x_eps h_eta)
  exact h_tri.trans (add_le_add h_lip h_mach)

/-- **Pipeline perturbation stability (Section 5):** under an additive input perturbation `δ`
with `‖δ‖ ≤ ε`, the quantized selector `s_ε` satisfies
`‖s_ε(x + δ) - s_ε(x)‖ ≤ ‖I - Q‖ * ε + η * (2 * ‖x‖ + ε)`. -/
theorem ContinuousLinearMap.quantized_pipeline_stability
    (Q : X →L[ℝ] X) (s_eps : X → X) (x delta : X) (eps eta : ℝ)
    (h_eta : 0 ≤ eta)
    (h_delta : ‖delta‖ ≤ eps)
    (h_round_x : ‖(ContinuousLinearMap.id ℝ X - Q) x - s_eps x‖ ≤ eta * ‖x‖)
    (h_round_xd : ‖(ContinuousLinearMap.id ℝ X - Q) (x + delta) - s_eps (x + delta)‖ ≤
      eta * ‖x + delta‖) :
    ‖s_eps (x + delta) - s_eps x‖ ≤
      ‖ContinuousLinearMap.id ℝ X - Q‖ * eps + eta * (2 * ‖x‖ + eps) := by
  let s := ContinuousLinearMap.id ℝ X - Q
  have h_split : s_eps (x + delta) - s_eps x =
      (s (x + delta) - s x) - (s (x + delta) - s_eps (x + delta)) + (s x - s_eps x) := by
    abel
  have h_tri1 : ‖s_eps (x + delta) - s_eps x‖ ≤
      ‖(s (x + delta) - s x) - (s (x + delta) - s_eps (x + delta))‖ + ‖s x - s_eps x‖ := by
    rw [h_split]
    exact norm_add_le _ _
  have h_tri2 : ‖(s (x + delta) - s x) - (s (x + delta) - s_eps (x + delta))‖ ≤
      ‖s (x + delta) - s x‖ + ‖s (x + delta) - s_eps (x + delta)‖ :=
    norm_sub_le _ _
  have h_lip : ‖s (x + delta) - s x‖ ≤ ‖s‖ * eps := by
    calc ‖s (x + delta) - s x‖ = ‖s ((x + delta) - x)‖ := by rw [← map_sub]
      _ = ‖s delta‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖s‖ * ‖delta‖ := s.le_opNorm delta
      _ ≤ ‖s‖ * eps := mul_le_mul_of_nonneg_left h_delta (norm_nonneg s)
  have h_xd_norm : ‖x + delta‖ ≤ ‖x‖ + eps := by
    have h1 := norm_add_le x delta
    linarith
  have h_r1 : ‖s (x + delta) - s_eps (x + delta)‖ ≤ eta * (‖x‖ + eps) :=
    h_round_xd.trans (mul_le_mul_of_nonneg_left h_xd_norm h_eta)
  linarith

end QuantizationAndStability

section CombinatorialReductions

/-- **Theorem 3 (Part 1 — Subset-Sum reduction):** for integer weights `a : Fin m → ℤ` and
nonzero target `T ≠ 0`, solvability of Subset-Sum is equivalent to the existence of a nonzero
Boolean vector `z ∈ {0, 1}^m` on the shifted hyperplane `∑ a_i z_i = T`. -/
theorem subsetSum_iff_boolean_shifted_hyperplane {m : ℕ} (a : Fin m → ℤ) (T : ℤ) (hT : T ≠ 0) :
    (∃ I : Finset (Fin m), ∑ i ∈ I, a i = T) ↔
      ∃ z : Fin m → ℤ, (∀ i, z i = 0 ∨ z i = 1) ∧ z ≠ 0 ∧ ∑ i, a i * z i = T := by
  refine ⟨?_, ?_⟩
  · rintro ⟨I, hI⟩
    refine ⟨fun i => if i ∈ I then 1 else 0, fun i => by dsimp; split_ifs <;> simp, ?_, ?_⟩
    · intro hz0
      have hsum0 : ∑ i : Fin m, a i * (if i ∈ I then (1 : ℤ) else 0) = 0 := by
        simp [congr_fun hz0]
      have h_eq : ∑ i ∈ I, a i = ∑ i : Fin m, a i * (if i ∈ I then (1 : ℤ) else 0) := by
        rw [← Finset.sum_subset (Finset.subset_univ I)]
        · refine Finset.sum_congr rfl fun i hi => ?_
          simp [hi]
        · intro i _ hi
          simp [hi]
      omega
    · rw [← hI, ← Finset.sum_subset (Finset.subset_univ I)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp [hi]
      · intro i _ hi
        simp [hi]
  · rintro ⟨z, hz_bool, _, hz_sum⟩
    refine ⟨Finset.univ.filter (fun i => z i = 1), ?_⟩
    rw [Finset.sum_filter, ← hz_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hz_bool i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- **Theorem 3 (Part 2 — Partition reduction):** for integer weights `a : Fin m → ℤ`,
existence of a balanced two-way partition is equivalent to the existence of a bipolar vector
`u ∈ {-1, 1}^m` satisfying the `ℓ₁^m` Birkhoff–James orthogonality balance `∑ a_i u_i = 0`. -/
theorem partition_iff_bipolar_null_layer {m : ℕ} (a : Fin m → ℤ) :
    (∃ I : Finset (Fin m), ∑ i ∈ I, a i = ∑ i ∈ Finset.univ \ I, a i) ↔
      ∃ u : Fin m → ℤ, (∀ i, u i = 1 ∨ u i = -1) ∧ ∑ i, a i * u i = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨I, hI⟩
    refine ⟨fun i => if i ∈ I then 1 else -1, fun i => by dsimp; split_ifs <;> simp, ?_⟩
    have h_split : ∑ i : Fin m, a i * (if i ∈ I then (1 : ℤ) else -1) =
        (∑ i ∈ Finset.univ \ I, a i * (if i ∈ I then (1 : ℤ) else -1)) +
        (∑ i ∈ I, a i * (if i ∈ I then (1 : ℤ) else -1)) :=
      (Finset.sum_sdiff (Finset.subset_univ I)).symm
    rw [h_split]
    have h1 : ∑ i ∈ I, a i * (if i ∈ I then (1 : ℤ) else -1) = ∑ i ∈ I, a i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [hi]
    have h2 : ∑ i ∈ Finset.univ \ I, a i * (if i ∈ I then (1 : ℤ) else -1) =
        -(∑ i ∈ Finset.univ \ I, a i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hni : i ∉ I := (Finset.mem_sdiff.mp hi).2
      simp [hni]
    rw [h1, h2, hI, neg_add_cancel]
  · rintro ⟨u, hu_bip, hu_sum⟩
    refine ⟨Finset.univ.filter (fun i => u i = 1), ?_⟩
    set I := Finset.univ.filter (fun i => u i = 1)
    have h_split : ∑ i : Fin m, a i * u i =
        (∑ i ∈ Finset.univ \ I, a i * u i) + (∑ i ∈ I, a i * u i) :=
      (Finset.sum_sdiff (Finset.subset_univ I)).symm
    rw [h_split] at hu_sum
    have h1 : ∑ i ∈ I, a i * u i = ∑ i ∈ I, a i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hui : u i = 1 := (Finset.mem_filter.mp hi).2
      simp [hui]
    have h2 : ∑ i ∈ Finset.univ \ I, a i * u i = -(∑ i ∈ Finset.univ \ I, a i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hni : u i ≠ 1 := fun h =>
        (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      rcases hu_bip i with h_pos | h_neg
      · exact False.elim (hni h_pos)
      · simp [h_neg]
    rw [h1, h2] at hu_sum
    omega

end CombinatorialReductions
