/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected

/-!
Auxiliary lemmata covering the analytic part of the proof of the Gelfond–Schneider theorem.
Move to appropriate files in Analysis/Complex or Analysis/Analytic and change docstring accordingly.
-/

@[expose] public section

open AnalyticOnNhd AnalyticAt Set

lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero (z₀ : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
    (hzero : f z₀ = 0) : analyticOrderAt (deriv f) z₀ = ⊤ ↔ analyticOrderAt f z₀ = ⊤ := by
  repeat rw [analyticOrderAt_eq_top, Metric.eventually_nhds_iff_ball]
  have ⟨r₁, hr₁, hB⟩ := exists_ball_analyticOnNhd hf
  refine ⟨fun ⟨r₂, hr₂, hball⟩ ↦ ?_, fun ⟨r₂, hr₂, hball⟩ ↦ ?_⟩
  · refine ⟨_, lt_min hr₁ hr₂, Metric.isOpen_ball.eqOn_of_deriv_eq ?_ ?_ ?_ ?_ ?_ hzero⟩
    · exact (Metric.isConnected_ball <| by grind).isPreconnected
    · intro x hx
      exact (hB x <| Metric.ball_subset_ball (min_le_left ..) hx).differentiableWithinAt
    · exact differentiableOn_const 0
    · intro x hx
      simpa using hball x <| Metric.ball_subset_ball (min_le_right r₁ r₂) hx
    · simpa using lt_min hr₁ hr₂
  · refine ⟨_, lt_min hr₁ hr₂, fun x hx ↦ ?_⟩
    rw [← derivWithin_of_mem_nhds <| Metric.isOpen_ball.mem_nhds hx]
    trans derivWithin 0 (Metric.ball z₀ (min r₁ r₂)) x
    · refine Filter.EventuallyEq.derivWithin_eq_of_nhds <| Filter.eventually_iff_exists_mem.mpr ?_
      refine ⟨_, Metric.isOpen_ball.mem_nhds hx, fun z hz ↦ hball z ?_⟩
      exact Metric.ball_subset_ball (min_le_right r₁ r₂) hz
    simp

lemma analyticOrderAt_eq_succ_iff_deriv_order_eq_pred {z₀ : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z₀)
    {n : ℕ} (hzero : f z₀ = 0) (horder : analyticOrderAt (deriv f) z₀ = n) :
    analyticOrderAt f z₀ = n + 1 := by
  cases Hn' : analyticOrderAt f z₀ with
  | top => grind [ENat.coe_ne_top, analyticOrderAt_deriv_eq_top_iff_of_eq_zero]
  | coe n' =>
    cases n' with
    | zero => exact hf.analyticOrderAt_eq_zero.mp Hn' hzero |>.elim
    | succ n'' =>
      have := horder ▸ Complex.analyticOrderAt_deriv_of_pos hf Hn'
      norm_cast at this ⊢
      have hchar : ringChar ℂ = 0 := by aesop
      aesop

lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {z₀ : ℂ} (n : ℕ) :
  ∀ (f : ℂ → ℂ) (_ : AnalyticAt ℂ f z₀),
    ((∀ k < n, deriv^[k] f z₀ = 0) ∧ deriv^[n] f z₀ ≠ 0) ↔ analyticOrderAt f z₀ = n := by
  induction n with
  | zero =>
    simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true, true_and, CharP.cast_eq_zero]
    exact fun f hf ↦ (AnalyticAt.analyticOrderAt_eq_zero hf).symm
  | succ n IH =>
    refine fun f hf ↦ ⟨fun ⟨hz, hnz⟩ ↦ ?_, ?_⟩
    · have IH' := IH (deriv f) (AnalyticAt.deriv hf)
      · exact analyticOrderAt_eq_succ_iff_deriv_order_eq_pred hf (hz 0 (by grind))
          (by simpa using ((IH').1 ⟨fun k hk => hz (k + 1) (Nat.succ_lt_succ hk), hnz⟩))
    · refine fun ho ↦ ⟨fun k hk ↦ (analyticOrderAt_ne_zero.mp ?_).2, ?_⟩
      · grind only [(Complex.analyticOrderAt_iterated_deriv (f:=f) hf k (n := (n + 1))
          ho.symm (by grind) hk.le), Nat.cast_ne_zero]
      · have := Complex.analyticOrderAt_iterated_deriv (f := f) hf (n + 1) (n := n + 1)
          ho.symm (by grind) (by grind)
        grind only [AnalyticAt.analyticOrderAt_eq_zero (hf := iterated_deriv hf (n + 1))]

lemma analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (n : ℕ) : analyticOrderAt f z₀ = n → (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) :=
  fun h ↦ (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero n (f := f) hf).mpr h

lemma le_analyticOrderAt_iff_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (n : ℕ) (ho : analyticOrderAt f z₀ ≠ ⊤) :
    (∀ k < n, (deriv^[k] f) z₀ = 0) → n ≤ analyticOrderAt f z₀ := by
  intro hkn
  obtain ⟨m, Hm⟩ := ENat.ne_top_iff_exists (n := analyticOrderAt f z₀).mp ho
  rw [← Hm, ENat.coe_le_coe]
  by_contra! h
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := m) f hf).mpr (Hm.symm)).2 (hkn m h)
