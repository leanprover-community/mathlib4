/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Tactic

/-!
Some auxiliary lemmata covering the analytic part of the proof of the Gelfond–Schneider theorem.
-/

@[expose] public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open Set AnalyticAt AnalyticOnNhd


lemma eq_zero_on_iff_forall_analyticOrderAt_eq_top {s : Set 𝕜} (f : 𝕜 → E) (hs : IsOpen s)
  (_ : AnalyticOn 𝕜 f s) :
  (∀ z ∈ s, f z = 0) ↔ ∀ z ∈ s, analyticOrderAt f z = ⊤ := by
  constructor
  · intro hzero z hz
    have hEv : (fun w => f w) =ᶠ[nhds z] (fun _ => (0)) := by
      have : ∀ᶠ w in nhds z, w ∈ s := hs.mem_nhds hz
      filter_upwards [this] with w hw
      simp [hzero w hw]
    exact (analyticOrderAt_eq_top).2 hEv
  · intro htop z hz
    have hEv : (fun w => f w) =ᶠ[nhds z] (fun _ => (0)) :=
      (analyticOrderAt_eq_top).1 (htop z hz)
    simpa using hEv.eq_of_nhds

lemma zero_iff_order_inf [PreconnectedSpace 𝕜] (f : 𝕜 → E) (z : 𝕜) (hf : ∀ z, AnalyticAt 𝕜 f z) :
  (∀ z, f z = 0) ↔ analyticOrderAt f z = ⊤ := by
  constructor
  · intro H
    refine (analyticOrderAt_eq_top).2 <| (frequently_eq_iff_eventually_eq (hf z) analyticAt_const).1
        (Filter.Frequently.of_forall H)
  · intros hr
    rw [@analyticOrderAt_eq_top 𝕜 _ _ _ _ f z,
        ← frequently_eq_iff_eventually_eq (hf z) (analyticAt_const)] at hr
    intros z
    exact (eqOn_zero_of_preconnected_of_frequently_eq_zero (fun x hx => by aesop)
      (isPreconnected_univ) trivial hr) trivial

lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero : ∀ z₀ (f : ℂ → ℂ)
     (_ : AnalyticAt ℂ f z₀), f z₀ = 0 →
    ((analyticOrderAt (deriv f) z₀) = ⊤ ↔ analyticOrderAt f z₀ = ⊤) := by
  intros z₀ f hf hzero
  simp_rw [analyticOrderAt_eq_top,Metric.eventually_nhds_iff_ball]
  constructor
  · intros H
    obtain ⟨r₁, ⟨hr₁0, hB⟩⟩ := exists_ball_analyticOnNhd hf
    obtain ⟨r₂, hr₂, hball⟩ := H
    let r := min r₁ r₂
    use r
    have hf : DifferentiableOn ℂ f (Metric.ball z₀ r) := fun x hx =>
     (hB x (Metric.ball_subset_ball (min_le_left r₁ r₂) hx)).differentiableAt.differentiableWithinAt
    have hg : DifferentiableOn ℂ (fun _ ↦ (0 : ℂ)) (Metric.ball z₀ r) := differentiableOn_const 0
    have hf' : EqOn (deriv f) (deriv (fun _ ↦ (0 : ℂ))) (Metric.ball z₀ r) := by
      intro x hx
      simpa [deriv_const'] using hball x (Metric.ball_subset_ball (min_le_right r₁ r₂) hx)
    have hx : z₀ ∈ Metric.ball z₀ r := by
      simpa [Metric.mem_ball, dist_self, r] using (lt_min hr₁0 hr₂)
    have := IsOpen.eqOn_of_deriv_eq (Metric.isOpen_ball)
      (IsConnected.isPreconnected <| Metric.isConnected_ball (by grind)) hf hg hf' hx
    grind
  · intros H
    obtain ⟨r₁, ⟨hr₁0, hB⟩⟩ := exists_ball_analyticOnNhd hf
    obtain ⟨r₂, hr₂, hball⟩ := H
    let r := min r₁ r₂
    use r
    constructor
    · simp_all only [Metric.mem_ball, dist_self, gt_iff_lt, lt_inf_iff, and_self, r]
    · intros x hx
      have hf' : EqOn f 0 (Metric.ball z₀ r) :=
        fun x hx ↦ hball x (Metric.ball_subset_ball (min_le_right r₁ r₂) hx)
      unfold EqOn at hf'
      have hf'' : derivWithin (fun _ => (0 : ℂ)) (Metric.ball z₀ r) x =
          derivWithin f (Metric.ball z₀ r) x := by
        apply Filter.EventuallyEq.derivWithin_eq_of_nhds
        unfold Filter.EventuallyEq
        rw [Filter.eventually_iff_exists_mem]
        use Metric.ball z₀ r
        constructor
        · refine IsOpen.mem_nhds Metric.isOpen_ball hx
        · exact fun z a ↦ Eq.symm
            (Complex.ext (congrArg Complex.re (hf' a)) (congrArg Complex.im (hf' a)))
      rw [← derivWithin_of_mem_nhds]
      · rw [← hf'']; simp only [derivWithin_fun_const, Pi.zero_apply, r]
      · rw [IsOpen.mem_nhds_iff]
        · exact hx
        · aesop

lemma analyticOrderAt_eq_succ_iff_deriv_order_eq_pred (f : ℂ → ℂ) z₀ (hf : AnalyticAt ℂ f z₀)
  (n : ℕ) : f z₀ = 0 → analyticOrderAt (deriv f) z₀ = (n - 1 : ℕ) →
      n > 0 → analyticOrderAt f z₀ = n := by
    intros hzero horder hn
    have : ∃ m, analyticOrderAt f z₀ = m := by simp
    obtain ⟨m, Hn'⟩ := this
    cases m
    · exfalso
      have ht : analyticOrderAt (deriv f) z₀ = (⊤ : ℕ∞) :=
        (analyticOrderAt_deriv_eq_top_iff_of_eq_zero z₀ f hf hzero).2 Hn'
      exact (ENat.coe_ne_top (n - 1)) (by grind)
    · rename_i n'
      cases n'
      · exfalso; exact ((AnalyticAt.analyticOrderAt_eq_zero hf).1 Hn') hzero
      · rename_i n''
        have hnn : analyticOrderAt (deriv f) z₀ = ((n'' + 1) - 1 : ℕ) :=
          Complex.analyticOrderAt_deriv_of_pos f z₀ hf (n'' + 1) Hn' (by omega)
        simp only [horder] at hnn
        have : n = n'' + 1 := by
          norm_cast at hnn
          rw [add_tsub_cancel_right] at hnn
          rw [← hnn]
          exact (Nat.sub_eq_iff_eq_add hn).mp rfl
        rw [this]
        exact Hn'

lemma iterated_deriv_mul_pow_sub_of_analytic (r : ℕ) {z₀ : ℂ} {R R₁ : ℂ → ℂ}
   (hf1 : ∀ z : ℂ, AnalyticAt ℂ R₁ z) (hR₁ : ∀ z, R z = (z - z₀)^r * R₁ z) :
  --(hf : ∀ z : ℂ, AnalyticAt ℂ R z) →
  ∀ k ≤ r ,
    ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧ ∀ z, deriv^[k] R z =
   (z - z₀)^(r-k) * (r.factorial/(r-k).factorial * R₁ z + (z-z₀)* R₂ z) := by
    --intros hf k hkr
      intros k hkr
      induction k
      · use 0
        simp only [Function.iterate_zero, id_eq, tsub_zero,
          Pi.zero_apply, mul_zero, add_zero]
        constructor
        · intros z; refine Differentiable.analyticAt (differentiable_zero) z
        · intros z
          rw [hR₁ z]
          simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
          left
          rw [div_self]
          · simp only [one_mul]
          · simp only [ne_eq, Nat.cast_eq_zero]
            exact Nat.factorial_ne_zero r
      · rename_i k IH
        simp only [Function.iterate_succ, Function.comp_apply]
        have change_deriv (R : ℂ → ℂ) (z: ℂ) :
          deriv^[k] (deriv R) z = deriv (deriv^[k] R) z := by
          have : deriv^[k] (deriv R) z = deriv^[k+1] R z := by
           simp only [Function.iterate_succ, Function.comp_apply]
          have : deriv (deriv^[k] R) z = deriv^[k+1] R z := by
            induction k
            · simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one]
            · rename_i k
              simp only [Function.iterate_succ, Function.comp_apply]
              simp only [Function.iterate_succ, Function.comp_apply] at IH
              rw [← iteratedDeriv_eq_iterate] at *
              rw [← iteratedDeriv_succ, this]
              simp only [Function.iterate_succ, Function.comp_apply]
          rw [this, ← this]
          exact id (Eq.symm this)
        simp only [change_deriv R]
        have : k ≤ r := by linarith
        have := IH this; clear IH
        obtain ⟨R₂, hR₂, hR1⟩ := this
        let R2 : ℂ → ℂ := fun z =>
           (↑(r - k) * R₂ z +
         (↑r.factorial / ↑(r - k).factorial * deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)))
        use R2
        constructor
        · intro z; dsimp [R2]; fun_prop
        · intros z
          have derivOfderivk : ∀ z,
              deriv
                (fun z =>
                  (z - z₀) ^ (r - k) *
                  (r.factorial / (r - k).factorial * R₁ z + (z - z₀) * R₂ z))
                z =
                ↑(r - k) * (z - z₀) ^ (r - k - 1) *
                  (↑r.factorial / ↑(r - k).factorial * R₁ z + (z - z₀) * R₂ z) +
                (z - z₀) ^ (r - k) *
                  (↑r.factorial / ↑(r - k).factorial * deriv R₁ z +
                  (R₂ z + (z - z₀) * deriv R₂ z)) := by
            intro z
            simp (disch := fun_prop)
            [deriv_fun_mul, deriv_fun_add, deriv_fun_pow, deriv_fun_sub, deriv_id'', deriv_const',
          mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
          conv => enter [1,1]; ext z; rw [hR1 z]
          rw [derivOfderivk]; clear derivOfderivk
          rw [mul_add]
          have H2 : (r - k - 1) = (r - (k + 1)) := by grind
          rw [H2];
          simp only [add_assoc]
          have H1 :
           ↑(r - k) * (z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - k).factorial * R₁ z)=
           1*((z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - k).factorial * R₁ z)) +
           ↑(r - k - 1) * ((z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - k).factorial * R₁ z))
            := by rw [← add_mul]; simp only [mul_assoc];congr;norm_cast; grind
          rw [H1]; clear H1;
          simp only [one_mul, ← mul_assoc]; nth_rw 5 [mul_comm]
          simp only [← add_assoc, mul_assoc]; rw [← mul_add]; simp only [← mul_assoc]
          nth_rw 6 [mul_comm]; nth_rw 7 [mul_comm]; simp only [← mul_assoc]
          nth_rw 7 [mul_comm]
          simp only [mul_assoc, ← mul_add]
          have : (z - z₀) ^ (r - k) = (z - z₀) ^ (r - (k + 1)) * (z - z₀)^1 := by
            rw [← pow_add]; congr; grind
          rw [this];clear this
          simp only [mul_assoc, ← mul_add, pow_one, mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
          left
          simp only [← mul_assoc]
          rw [← add_mul]
          nth_rw 1 [← one_mul (a:=(r.factorial / (r - k).factorial : ℂ))]
          rw [← add_mul]
          have : ↑(r - (k + 1) + 1)= ↑(r - k) := by grind
          norm_cast
          rw [add_assoc]; simp only [mul_assoc]; rw [← mul_add, Nat.cast_add, Nat.cast_one]
          nth_rw 2 [add_comm]
          norm_cast
          rw [H2, this]
          simp only [← mul_assoc, mul_div]
          have : ((↑(r - k) *r.factorial)/↑(r - k).factorial : ℂ) =
             ↑r.factorial / ↑(r - (k + 1)).factorial := by
            nth_rw 2 [← Nat.mul_factorial_pred]
            · rw [H2]
              ring_nf
              simp only [Nat.cast_mul, _root_.mul_inv_rev]
              nth_rw 2 [mul_comm]; nth_rw 3 [mul_comm]
              simp only [← mul_assoc, mul_eq_mul_right_iff, inv_eq_zero, Nat.cast_eq_zero]
              left
              rw [mul_assoc, mul_inv_cancel₀]
              · simp only [mul_one]
              · simp only [ne_eq, Nat.cast_eq_zero]
                grind
            · grind
          rw [this]
          unfold R2
          simp only [add_assoc]

lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero :
  ∀ z₀ n (f : ℂ → ℂ) (_ : AnalyticAt ℂ f z₀) (_ : analyticOrderAt f z₀ ≠ ⊤),
    (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) ↔ analyticOrderAt f z₀ = n := by
  intros z₀ n
  induction n
  · simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true,
      Function.iterate_zero, id_eq, true_and, CharP.cast_eq_zero]
    exact fun f hf ho ↦ Iff.symm (AnalyticAt.analyticOrderAt_eq_zero hf)
  · rename_i n IH
    intros f hf hfin
    constructor
    · intros H
      obtain ⟨hz, hnz⟩:= H
      have IH' := IH (deriv f) (AnalyticAt.deriv hf) ?_
      · suffices analyticOrderAt (deriv f) z₀ = (n : ℕ) by
          refine analyticOrderAt_eq_succ_iff_deriv_order_eq_pred f z₀ hf
            (n + 1) (hz 0 (by omega)) this (by simp)
        rw[← IH']
        constructor
        · intros k hk; exact hz (k + 1) (by omega)
        · exact hnz
      · have := Complex.analyticOrderAt_deriv_of_pos f  z₀ hf
        specialize hz 0 (by omega)
        obtain ⟨r, hr⟩ := (WithTop.ne_top_iff_exists).mp hfin
        specialize this r hr.symm
        simp only [Function.iterate_zero, id_eq] at hz
        have r0 : r > 0 := by
          suffices analyticOrderAt f z₀ > 0 by
            suffices @WithTop.some ℕ r > 0 by exact ENat.coe_lt_coe.mp this
            rw [hr]
            exact this
          exact pos_of_ne_zero (analyticOrderAt_ne_zero.mpr ⟨hf, hz⟩)
        have Hr : r ≠ 0 := by omega
        specialize this Hr
        rw [this]
        exact ENat.coe_ne_top (r - 1)
    · intros ho
      constructor
      · intros k hk
        have : analyticOrderAt (deriv^[k] f) z₀ ≠ 0 := by
          rw [(Complex.analyticOrderAt_iterated_deriv f hf k (n+1)
            ho.symm (by omega) hk.le), @Nat.cast_ne_zero]
          omega
        rw [analyticOrderAt_ne_zero] at this
        exact this.2
      · have := Complex.analyticOrderAt_iterated_deriv f hf (n+1) (n+1)
          ho.symm (by omega) (by omega)
        simp only [Function.iterate_succ, Function.comp_apply, tsub_self,
          CharP.cast_eq_zero] at this
        rw [AnalyticAt.analyticOrderAt_eq_zero] at this
        · assumption
        · exact iterated_deriv hf (n + 1)

lemma analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    z₀ (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) :
  analyticOrderAt f z₀ = n → (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) := fun h =>
  (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero z₀ n f hf (h.symm ▸ ENat.coe_ne_top n)).mpr h

lemma le_analyticOrderAt_iff_iteratedDeriv_eq_zero : ∀ (n : ℕ) z₀
  (f : ℂ → ℂ) (_ : AnalyticAt ℂ f z₀) (_ : analyticOrderAt f z₀ ≠ ⊤),
  (∀ k < n, (deriv^[k] f) z₀ = 0) → n ≤ analyticOrderAt f z₀ := by
    intros n z₀ f hf ho hkn
    have notTop (m : ℕ∞): m ≠ ⊤ → ∃ n : ℕ, m = ↑n := by
      intro h
      exact Option.ne_none_iff_exists'.mp h
    obtain ⟨m, Hm⟩ := notTop (analyticOrderAt f z₀) ho
    rw [Hm]
    rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero z₀ m f hf ho] at Hm
    rw [ENat.coe_le_coe]
    by_contra h
    push_neg at h
    exact Hm.2 (hkn m h)

lemma hasFPowerSeriesWithinAt_nhds_iff (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (U : Set ℂ) (z : ℂ) (hU : U ∈ nhds z) :
  HasFPowerSeriesWithinAt f p U z ↔ HasFPowerSeriesAt f p z := by
    simp only [HasFPowerSeriesWithinAt, HasFPowerSeriesAt]
    constructor
    · intros H
      have hzmem : z ∈ U := by exact mem_of_mem_nhds hU
      rw [Metric.mem_nhds_iff] at hU
      obtain ⟨r', hr', hball⟩:= hU
      let r'' : ENNReal := Option.some ⟨r', by linarith⟩
      have hball' : EMetric.ball z r'' ⊆ U := by aesop
      obtain ⟨renn, hr⟩:= H
      use min (renn) r''
      obtain ⟨r_le, r_pos, hs⟩ := hr
      constructor
      · aesop
      · aesop
      · intros y a
        apply hs
        · have shift_ball (x y z : ℂ) (renn : ENNReal) :
            x ∈ EMetric.ball y renn → z + x ∈ EMetric.ball (z + y) renn := by
              simp only [EMetric.mem_ball, edist_add_left, imp_self]
          have : z + y ∈ EMetric.ball (z + 0) (min renn r'') := by
            apply shift_ball
            exact a
          have : z + y ∈ EMetric.ball z (min renn r'') := by aesop
          have : z + y ∈ EMetric.ball z r'' := by aesop
          have : z + y ∈ U := by aesop
          aesop
        · aesop
    · intros H
      obtain ⟨renn,hr⟩:= H
      use renn
      exact HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall hr

lemma AnalyticOn.analyticAt (f : ℂ → ℂ) (z : ℂ) (U : Set ℂ) (hU : U ∈ nhds z) :
  AnalyticOn ℂ f U → AnalyticAt ℂ f z := by
  intros HA
  obtain ⟨p, hp⟩ := (HA z (mem_of_mem_nhds hU))
  use p
  exact (hasFPowerSeriesWithinAt_nhds_iff f p U z hU).mp hp
