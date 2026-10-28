/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Moments.Bernstein

/-!
# Exponential supermartingales

The predictable quadratic variation of a discrete-time real process is the sum of the
conditional second moments of its increments. For a square-integrable martingale with
increments bounded above, the Bernstein conditional exponential bound gives an exponential
supermartingale compensated by this predictable quadratic variation.
-/

@[expose] public section

open Filter Finset
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {M : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}

/-- The predictable quadratic variation of a discrete-time real process, starting at zero. -/
noncomputable def predictableQuadraticVariation (M : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  fun n ↦ ∑ k ∈ range n, μ[fun ω ↦ (M (k + 1) ω - M k ω) ^ 2 | ℱ k]

@[simp]
lemma predictableQuadraticVariation_zero : predictableQuadraticVariation M ℱ μ 0 = 0 := by
  simp [predictableQuadraticVariation]

lemma predictableQuadraticVariation_add_one (n : ℕ) :
    predictableQuadraticVariation M ℱ μ (n + 1) = predictableQuadraticVariation M ℱ μ n +
      μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ 2 | ℱ n] := by
  simp [predictableQuadraticVariation, sum_range_succ]

lemma stronglyAdapted_predictableQuadraticVariation :
    StronglyAdapted ℱ (predictableQuadraticVariation M ℱ μ) :=
  fun _ ↦ Finset.stronglyMeasurable_sum _ fun _ hk ↦
    stronglyMeasurable_condExp.mono (ℱ.mono (mem_range_le hk))

lemma stronglyAdapted_succ_predictableQuadraticVariation :
    StronglyAdapted ℱ (fun n ↦ predictableQuadraticVariation M ℱ μ (n + 1)) :=
  fun _ ↦ Finset.stronglyMeasurable_sum _ fun _ hk ↦
    stronglyMeasurable_condExp.mono (ℱ.mono (mem_range_succ_iff.mp hk))

lemma predictableQuadraticVariation_nonneg (n : ℕ) :
    0 ≤ᵐ[μ] predictableQuadraticVariation M ℱ μ n := by
  filter_upwards [(eventually_all_finset (range n)).2 fun k _ ↦ condExp_nonneg (m := ℱ k)
    (ae_of_all μ fun ω ↦ sq_nonneg (M (k + 1) ω - M k ω))] with ω hω
  simpa [predictableQuadraticVariation, Finset.sum_apply] using Finset.sum_nonneg hω

private lemma ae_le_of_bdd_increments {b : ℝ} (hM0 : M 0 =ᵐ[μ] 0)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ≤ b) (n : ℕ) :
    ∀ᵐ ω ∂μ, M n ω ≤ n * b := by
  filter_upwards [hM0, (eventually_all_finset (range n)).2 fun k _ ↦ hbound k] with ω hzero hω
  have hsum := Finset.sum_le_sum hω
  rw [Finset.sum_range_sub (fun k ↦ M k ω)] at hsum
  simpa [hzero] using hsum

/-- A martingale with square-integrable increments bounded above admits the Bernstein
exponential supermartingale, compensated by its predictable quadratic variation. -/
lemma Martingale.exponential_supermartingale [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0) (hM2 : ∀ n, MemLp (M n) 2 μ)
    {b θ : ℝ} (hbound : ∀ n, ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ≤ b)
    (hb : 0 < b) (hθ : 0 ≤ θ) (hθb : θ * b < 3) :
    Supermartingale (fun n ω ↦ Real.exp (θ * M n ω -
      (θ ^ 2 / (2 * (1 - θ * b / 3))) * predictableQuadraticVariation M ℱ μ n ω)) ℱ μ := by
  let c := θ ^ 2 / (2 * (1 - θ * b / 3))
  have hden : 0 < 1 - θ * b / 3 := by linarith
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hZadp : StronglyAdapted ℱ (fun n ω ↦
      Real.exp (θ * M n ω - c * predictableQuadraticVariation M ℱ μ n ω)) := by
    intro n
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyMeasurable n).const_mul θ).sub
        ((stronglyAdapted_predictableQuadraticVariation n).const_mul c))
  have hZint (n : ℕ) : Integrable (fun ω ↦
      Real.exp (θ * M n ω - c * predictableQuadraticVariation M ℱ μ n ω)) μ := by
    refine (integrable_const (Real.exp (θ * (n * b)))).mono'
      ((hZadp n).mono (ℱ.le n)).aestronglyMeasurable ?_
    filter_upwards [ae_le_of_bdd_increments hM0 hbound n,
      predictableQuadraticVariation_nonneg (M := M) (ℱ := ℱ) (μ := μ) n] with ω hMn hV
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (sub_le_self _ (mul_nonneg hc hV)).trans (mul_le_mul_of_nonneg_left hMn hθ)
  refine supermartingale_nat hZadp hZint fun n ↦ ?_
  let Δ : Ω → ℝ := fun ω ↦ M (n + 1) ω - M n ω
  have hΔ2 : MemLp Δ 2 μ := (hM2 (n + 1)).sub (hM2 n)
  let A : Ω → ℝ := fun ω ↦
    Real.exp (θ * M n ω - c * predictableQuadraticVariation M ℱ μ (n + 1) ω)
  have hA : StronglyMeasurable[ℱ n] A :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyMeasurable n).const_mul θ).sub
        ((stronglyAdapted_succ_predictableQuadraticVariation n).const_mul c))
  have hprod : A * (fun ω ↦ Real.exp (θ * Δ ω)) =
      (fun ω ↦ Real.exp (θ * M (n + 1) ω -
        c * predictableQuadraticVariation M ℱ μ (n + 1) ω)) := by
    ext ω
    dsimp [A, Δ]
    rw [← Real.exp_add]
    congr 1
    ring
  have hΔmean : μ[Δ | ℱ n] =ᵐ[μ] 0 := by
    have heq := (condExp_sub (hM.integrable (n + 1)) (hM.integrable n) (ℱ n)).trans
      ((hM.condExp_ae_eq n.le_succ).sub (hM.condExp_ae_eq (le_refl n)))
    simpa [Δ, Pi.sub_def] using heq
  have hΔint : Integrable (fun ω ↦ Real.exp (θ * Δ ω)) μ :=
    ProbabilityTheory.integrable_exp_mul_of_ae_le hΔ2.aestronglyMeasurable (hbound n) hθ
  have hbern := ProbabilityTheory.condExp_exp_mul_le_exp_mul_condExp_sq (ℱ.le n)
    hΔ2 (hbound n) hΔmean hb hθ hθb
  have hpull := condExp_mul_of_stronglyMeasurable_left hA
    (hprod.symm ▸ hZint (n + 1)) hΔint
  rw [hprod] at hpull
  filter_upwards [hpull, hbern] with ω hp hstep
  rw [hp]
  calc
    A ω * μ[fun ω ↦ Real.exp (θ * Δ ω) | ℱ n] ω ≤
        A ω * Real.exp (c * μ[fun ω ↦ Δ ω ^ 2 | ℱ n] ω) :=
      mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = Real.exp (θ * M n ω - c * predictableQuadraticVariation M ℱ μ n ω) := by
      dsimp [A]
      rw [← Real.exp_add, predictableQuadraticVariation_add_one, Pi.add_apply,
        mul_add, sub_add_eq_sub_sub, sub_add_cancel]

end MeasureTheory
