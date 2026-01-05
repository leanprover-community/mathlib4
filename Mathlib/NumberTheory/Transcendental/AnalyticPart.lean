/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
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

lemma analyticOrderAt_eq_succ_iff_deriv_order_eq_pred (z₀ : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
    (n : ℕ) (hzero : f z₀ = 0) (horder : analyticOrderAt (deriv f) z₀ = (n - 1 : ℕ)) (hn : 0 < n) :
    analyticOrderAt f z₀ = n := by
  cases Hn' : analyticOrderAt f z₀ with
  | top => grind [ENat.coe_ne_top, analyticOrderAt_deriv_eq_top_iff_of_eq_zero]
  | coe n' =>
    cases n' with
    | zero => exact hf.analyticOrderAt_eq_zero.mp Hn' hzero |>.elim
    | succ n'' =>
      have := horder ▸ Complex.analyticOrderAt_deriv_of_pos hf Hn'
      norm_cast at this ⊢
      lia

lemma iterated_deriv_mul_pow_sub_of_analytic (r : ℕ) (z₀ : ℂ) {R R₁ : ℂ → ℂ}
    (hf1 : ∀ z : ℂ, AnalyticAt ℂ R₁ z) (hR₁ : ∀ z, R z = (z - z₀)^r * R₁ z) :
    ∀ k ≤ r, ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧ ∀ z, deriv^[k] R z =
    (z - z₀) ^ (r - k) * (r.factorial / (r - k).factorial * R₁ z + (z - z₀) * R₂ z) := by
  intros k hkr
  induction k generalizing r with
  | zero =>
    refine ⟨0, ?_⟩
    · simp only [Function.iterate_zero, id_eq, tsub_zero, Pi.zero_apply, mul_zero, add_zero]
      refine ⟨fun z ↦ Differentiable.analyticAt (differentiable_zero) z, fun z ↦ ?_⟩
      · rw [hR₁ z, mul_eq_mul_left_iff, pow_eq_zero_iff',
          div_self (h:= mod_cast Nat.factorial_ne_zero r)]
        grind
  | succ k IH =>
    obtain ⟨R₂, hR₂, hR1⟩ := IH r hR₁ (by linarith)
    refine ⟨fun z ↦ (↑(r - k) * R₂ z +
         (↑r.factorial / ↑(r - k).factorial * deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))), ?_⟩
    · refine ⟨fun z ↦ by fun_prop, fun z ↦ ?_⟩
      · calc _ =  deriv (deriv^[k] R) z := ?_
             _ = 1 * ((z - z₀) ^ (r - (k + 1)) *(↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k - 1) * ((z - z₀) ^ (r - (k + 1)) *
                 (↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k) * (z - z₀) ^ (r - (k + 1)) * ((z - z₀) * R₂ z) +
                 (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := ?_
             _ = (z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - (k + 1)).factorial *
                 R₁ z + (z - z₀) *(fun z ↦ ↑(r - k) * R₂ z + (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))) z) := ?_
        · symm
          have : deriv^[k] (deriv R) z = deriv^[k+1] R z := by aesop
          induction k generalizing r with
            | zero => aesop
            | succ k IH =>
              rw [Function.iterate_succ, Function.comp_apply] at IH ⊢
              rw [← iteratedDeriv_eq_iterate] at this ⊢
              rw [← iteratedDeriv_succ, this]
        · conv => enter [1, 1]; ext z; rw [hR1 z]
          have derivOfderivk : ∀ z, deriv (fun z ↦ (z - z₀) ^ (r - k) *
            (r.factorial / (r - k).factorial * R₁ z + (z - z₀) * R₂ z)) z =
            ↑(r - k) * (z - z₀) ^ (r - k - 1) * (↑r.factorial / ↑(r - k).factorial *
            R₁ z + (z - z₀) * R₂ z) + (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
            deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := fun z ↦ by simp (disch := fun_prop)
          rw [derivOfderivk, mul_add,Nat.sub_sub r k 1]
          rw [← add_mul]; simp only [mul_assoc]; congr; norm_cast; grind [mul_assoc]
        · simp only [one_mul, ← mul_assoc]; nth_rw 5 [mul_comm]
          simp only [← add_assoc, mul_assoc]; rw [← mul_add]; simp only [← mul_assoc]
          nth_rw 6 [mul_comm]; nth_rw 7 [mul_comm]; simp only [← mul_assoc]
          nth_rw 7 [mul_comm]
          simp only [mul_assoc, ← mul_add]
          have : (z - z₀) ^ (r - k) = (z - z₀) ^ (r - (k + 1)) * (z - z₀)^1 := by
             rw [← pow_add]; congr; grind
          rw [this]; clear this
          simp only [mul_assoc, ← mul_add, pow_one, mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
          left
          rw [← mul_assoc, ← add_mul]
          nth_rw 1 [← one_mul (a := (r.factorial / (r - k).factorial : ℂ)), ← add_mul]
          rw [add_assoc]; simp only [mul_assoc]; rw [← mul_add]
          nth_rw 2 [add_comm]
          norm_cast
          simp only [← mul_assoc, mul_div]
          have HR : ↑(r - (k + 1) + 1) = ↑(r - k) := by grind
          rw [Nat.sub_sub r k 1, HR]
          simp only [add_assoc]
          congr 1
          simp only [mul_eq_mul_right_iff]
          left
          nth_rw 2 [← Nat.mul_factorial_pred (hn := by grind)]
          rw [Nat.sub_sub r k 1]
          ring_nf
          nth_rw 2 [mul_comm]; nth_rw 3 [mul_comm]
          rw [Nat.cast_mul, mul_inv_rev, ← mul_assoc, mul_eq_mul_right_iff, inv_eq_zero,
            Nat.cast_eq_zero, mul_assoc, mul_inv_cancel₀ (h := by simp; grind)]
          grind

lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (z₀ : ℂ) (n : ℕ) :
  ∀ (f : ℂ → ℂ) (_ : AnalyticAt ℂ f z₀) (_ : analyticOrderAt f z₀ ≠ ⊤),
    (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) ↔ analyticOrderAt f z₀ = n := by
  induction n with
  | zero =>
    simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true, true_and, CharP.cast_eq_zero]
    exact fun f hf ho ↦ (AnalyticAt.analyticOrderAt_eq_zero hf).symm
  | succ n IH =>
    refine fun f hf hfin ↦ ⟨fun ⟨hz, hnz⟩ ↦ ?_, ?_⟩
    · have IH' := IH (deriv f) (AnalyticAt.deriv hf) ?_
      · exact analyticOrderAt_eq_succ_iff_deriv_order_eq_pred z₀ f hf
         (n + 1) (hz 0 (by grind))
         (by simpa using ((IH').1 ⟨fun k hk => hz (k + 1) (Nat.succ_lt_succ hk), hnz⟩)) (by simp)
      · obtain ⟨r, hr⟩ := (WithTop.ne_top_iff_exists).mp hfin
        specialize hz 0 (by grind)
        have r0 : r > 0 := ENat.coe_lt_coe.mp ((lt_of_lt_of_eq
          (pos_of_ne_zero (analyticOrderAt_ne_zero.mpr ⟨hf, hz⟩)) (id (Eq.symm hr))))
        rw [Complex.analyticOrderAt_deriv_of_pos (n := r) hf hr.symm (by grind)]
        exact ENat.coe_ne_top (r - 1)
    · refine fun ho ↦ ⟨fun k hk ↦ (analyticOrderAt_ne_zero.mp ?_).2, ?_⟩
      · grind only [(Complex.analyticOrderAt_iterated_deriv f hf k (n+1)
          ho.symm (by grind) hk.le), @Nat.cast_ne_zero]
      · have := Complex.analyticOrderAt_iterated_deriv f hf (n + 1) (n + 1)
          ho.symm (by grind) (by grind)
        grind only [AnalyticAt.analyticOrderAt_eq_zero (hf := iterated_deriv hf (n + 1))]

lemma analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    z₀ (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) :
  analyticOrderAt f z₀ = n → (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) := fun h ↦
  (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero z₀ n f hf (h.symm ▸ ENat.coe_ne_top n)).mpr h

lemma le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n : ℕ) z₀
  (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) (ho : analyticOrderAt f z₀ ≠ ⊤) :
   (∀ k < n, (deriv^[k] f) z₀ = 0) → n ≤ analyticOrderAt f z₀ := by
    intros hkn
    have notTop (m : ℕ∞) : m ≠ ⊤ → ∃ n : ℕ, m = n :=
      (Option.ne_none_iff_exists'.mp ·)
    obtain ⟨m, Hm⟩ := notTop (analyticOrderAt f z₀) ho
    rw [Hm, ENat.coe_le_coe]
    rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero z₀ m f hf ho] at Hm
    by_contra! h
    exact Hm.2 (hkn m h)

lemma add_mem_emetric_ball_left {x y z : ℂ} (r : ENNReal) :
    x ∈ EMetric.ball y r → z + x ∈ EMetric.ball (z + y) r := by
  simp

lemma hasFPowerSeriesWithinAt_nhds_iff (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (U : Set ℂ) (z : ℂ) (hU : U ∈ nhds z) :
  HasFPowerSeriesWithinAt f p U z ↔ HasFPowerSeriesAt f p z := by
    refine ⟨fun ⟨renn, r_le, r_pos, hs⟩ ↦ ?_,
      fun ⟨r, hr⟩ ↦ ⟨r, HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall hr⟩⟩
    · have hzmem := mem_of_mem_nhds hU
      rw [Metric.mem_nhds_iff] at hU
      obtain ⟨r', hr', hball⟩ := hU
      use min renn (Option.some ⟨r', by linarith⟩)
      refine ⟨by aesop, by aesop, fun hy s ↦ hs (U := s) (y := _) (by aesop) (by aesop)⟩

lemma AnalyticOn.analyticAt (f : ℂ → ℂ) (z : ℂ) (U : Set ℂ) (hU : U ∈ nhds z) :
  AnalyticOn ℂ f U → AnalyticAt ℂ f z := by
  intros HA
  obtain ⟨p, hp⟩ := HA z (mem_of_mem_nhds hU)
  exact ⟨p, hasFPowerSeriesWithinAt_nhds_iff f p U z hU |>.mp hp⟩
