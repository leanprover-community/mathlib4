/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Results on discretized exponentials

We state several auxiliary results pertaining to sequences of the form `⌊c^n⌋₊`.

* `tendsto_div_of_monotone_of_tendsto_div_floor_pow`: If a monotone sequence `u` is such that
  `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all `c > 1`, then `u n / n` tends to `l`.
* `sum_div_nat_floor_pow_sq_le_div_sq`: The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable
  to `1/j^2`, up to a multiplicative constant.
-/

open Filter Finset

open Topology

/-- If a monotone sequence `u` is such that `u n / n` tends to a limit `l` along subsequences with
exponential growth rate arbitrarily close to `1`, then `u n / n` tends to `l`. -/
theorem tendsto_div_of_monotone_of_exists_subseq_tendsto_div (u : ℕ → ℝ) (l : ℝ)
    (hmono : Monotone u)
    (hlim : ∀ a : ℝ, 1 < a → ∃ c : ℕ → ℕ, (∀ᶠ n in atTop, (c (n + 1) : ℝ) ≤ a * c n) ∧
      Tendsto c atTop atTop ∧ Tendsto (fun n => u (c n) / c n) atTop (𝓝 l)) :
    Tendsto (fun n => u n / n) atTop (𝓝 l) := by
  /- To check the result up to some `ε > 0`, we use a sequence `c` for which the ratio
    `c (N+1) / c N` is bounded by `1 + ε`. Sandwiching a given `n` between two consecutive values of
    `c`, say `c N` and `c (N+1)`, one can then bound `u n / n` from above by `u (c N) / c (N - 1)`
    and from below by `u (c (N - 1)) / c N` (using that `u` is monotone), which are both comparable
    to the limit `l` up to `1 + ε`.
    We give a version of this proof by clearing out denominators first, to avoid discussing the sign
    of different quantities. -/
  have lnonneg : 0 ≤ l := by
    rcases hlim 2 one_lt_two with ⟨c, _, ctop, clim⟩
    have : Tendsto (fun n => u 0 / c n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.2 ctop)
    apply le_of_tendsto_of_tendsto' this clim fun n => ?_
    gcongr
    exact hmono (zero_le _)
  have A : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, u n - n * l ≤ ε * (1 + ε + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n in atTop, u (c n) - c n * l ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ,
        Asymptotics.isLittleO_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_atTop 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc
        u (c n) - c n * l = (u (c n) / c n - l) * c n := by field_simp
        _ ≤ ε * c n := by
          gcongr
          refine (le_abs_self _).trans ?_
          simpa using hn
    obtain ⟨a, ha⟩ :
      ∃ a : ℕ, ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ u (c b) - c b * l ≤ ε * c b :=
      eventually_atTop.1 (cgrowth.and L)
    let M := ((Finset.range (a + 1)).image fun i => c i).max' (by simp)
    filter_upwards [Ici_mem_atTop M] with n hn
    have exN : ∃ N, n < c N := by
      rcases (tendsto_atTop.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact ⟨N, by grind⟩
    let N := Nat.find exN
    have ncN : n < c N := Nat.find_spec exN
    have aN : a + 1 ≤ N := by
      by_contra! h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_le Nat.succ_pos' aN
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_lt Npos.ne'
      simpa only [not_lt] using Nat.find_min exN this
    have IcN : (c N : ℝ) ≤ (1 + ε) * c (N - 1) := by
      have A : a ≤ N - 1 := by
        apply @Nat.le_of_add_le_add_right a 1 (N - 1)
        rw [Nat.sub_add_cancel Npos]
        exact aN
      have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
      have := (ha _ A).1
      rwa [B] at this
    calc
      u n - n * l ≤ u (c N) - c (N - 1) * l := by gcongr; exact hmono ncN.le
      _ = u (c N) - c N * l + (c N - c (N - 1)) * l := by ring
      _ ≤ ε * c N + ε * c (N - 1) * l := by
        gcongr
        · exact (ha N (a.le_succ.trans aN)).2
        · linarith only [IcN]
      _ ≤ ε * ((1 + ε) * c (N - 1)) + ε * c (N - 1) * l := by gcongr
      _ = ε * (1 + ε + l) * c (N - 1) := by ring
      _ ≤ ε * (1 + ε + l) * n := by gcongr
  have B : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) * l - u n ≤ ε * (1 + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n : ℕ in atTop, (c n : ℝ) * l - u (c n) ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ,
        Asymptotics.isLittleO_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_atTop 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc
        (c n : ℝ) * l - u (c n) = -(u (c n) / c n - l) * c n := by field_simp; ring
        _ ≤ ε * c n := by
          gcongr
          refine le_trans (neg_le_abs _) ?_
          simpa using hn
    obtain ⟨a, ha⟩ :
      ∃ a : ℕ,
        ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ (c b : ℝ) * l - u (c b) ≤ ε * c b :=
      eventually_atTop.1 (cgrowth.and L)
    let M := ((Finset.range (a + 1)).image fun i => c i).max' (by simp)
    filter_upwards [Ici_mem_atTop M] with n hn
    have exN : ∃ N, n < c N := by
      rcases (tendsto_atTop.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact ⟨N, by grind⟩
    let N := Nat.find exN
    have ncN : n < c N := Nat.find_spec exN
    have aN : a + 1 ≤ N := by
      by_contra! h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_le Nat.succ_pos' aN
    have aN' : a ≤ N - 1 := by
      apply @Nat.le_of_add_le_add_right a 1 (N - 1)
      rw [Nat.sub_add_cancel Npos]
      exact aN
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_lt Npos.ne'
      simpa only [not_lt] using Nat.find_min exN this
    calc
      (n : ℝ) * l - u n ≤ c N * l - u (c (N - 1)) := by
        gcongr
        exact hmono cNn
      _ ≤ (1 + ε) * c (N - 1) * l - u (c (N - 1)) := by
        gcongr
        have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        simpa [B] using (ha _ aN').1
      _ = c (N - 1) * l - u (c (N - 1)) + ε * c (N - 1) * l := by ring
      _ ≤ ε * c (N - 1) + ε * c (N - 1) * l := add_le_add (ha _ aN').2 le_rfl
      _ = ε * (1 + l) * c (N - 1) := by ring
      _ ≤ ε * (1 + l) * n := by gcongr
  refine tendsto_order.2 ⟨fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, d + ε * (1 + l) < l ∧ 0 < ε := by
      have L : Tendsto (fun ε => d + ε * (1 + l)) (𝓝[>] 0) (𝓝 (d + 0 * (1 + l))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      simp only [zero_mul, add_zero] at L
      exact (((tendsto_order.1 L).2 l hd).and self_mem_nhdsWithin).exists
    filter_upwards [B ε εpos, Ioi_mem_atTop 0] with n hn npos
    simp_rw [div_eq_inv_mul]
    calc
      d < (n : ℝ)⁻¹ * n * (l - ε * (1 + l)) := by
        rw [inv_mul_cancel₀, one_mul]
        · linarith only [hε]
        · exact Nat.cast_ne_zero.2 (ne_of_gt npos)
      _ = (n : ℝ)⁻¹ * (n * l - ε * (1 + l) * n) := by ring
      _ ≤ (n : ℝ)⁻¹ * u n := by gcongr; linarith only [hn]
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, l + ε * (1 + ε + l) < d ∧ 0 < ε := by
      have L : Tendsto (fun ε => l + ε * (1 + ε + l)) (𝓝[>] 0) (𝓝 (l + 0 * (1 + 0 + l))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        exact
          tendsto_const_nhds.add
            (tendsto_id.mul ((tendsto_const_nhds.add tendsto_id).add tendsto_const_nhds))
      simp only [zero_mul, add_zero] at L
      exact (((tendsto_order.1 L).2 d hd).and self_mem_nhdsWithin).exists
    filter_upwards [A ε εpos, Ioi_mem_atTop 0] with n hn (npos : 0 < n)
    calc
      u n / n ≤ (n * l + ε * (1 + ε + l) * n) / n := by gcongr; linarith only [hn]
      _ = (l + ε * (1 + ε + l)) := by field_simp
      _ < d := hε

/-- If a monotone sequence `u` is such that `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all
`c > 1`, then `u n / n` tends to `l`. It is even enough to have the assumption for a sequence of
`c`s converging to `1`. -/
theorem tendsto_div_of_monotone_of_tendsto_div_floor_pow (u : ℕ → ℝ) (l : ℝ) (hmono : Monotone u)
    (c : ℕ → ℝ) (cone : ∀ k, 1 < c k) (clim : Tendsto c atTop (𝓝 1))
    (hc : ∀ k, Tendsto (fun n : ℕ => u ⌊c k ^ n⌋₊ / ⌊c k ^ n⌋₊) atTop (𝓝 l)) :
    Tendsto (fun n => u n / n) atTop (𝓝 l) := by
  apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div u l hmono
  intro a ha
  obtain ⟨k, hk⟩ : ∃ k, c k < a := ((tendsto_order.1 clim).2 a ha).exists
  refine
    ⟨fun n => ⌊c k ^ n⌋₊, ?_,
      (tendsto_nat_floor_atTop (α := ℝ)).comp (tendsto_pow_atTop_atTop_of_one_lt (cone k)), hc k⟩
  have H : ∀ n : ℕ, (0 : ℝ) < ⌊c k ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ (cone k).le]
  have A :
    Tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / c k ^ (n + 1) * c k / (⌊c k ^ n⌋₊ / c k ^ n))
      atTop (𝓝 (1 * c k / 1)) := by
    refine Tendsto.div (Tendsto.mul ?_ tendsto_const_nhds) ?_ one_ne_zero
    · refine tendsto_nat_floor_div_atTop.comp ?_
      exact (tendsto_pow_atTop_atTop_of_one_lt (cone k)).comp (tendsto_add_atTop_nat 1)
    · refine tendsto_nat_floor_div_atTop.comp ?_
      exact tendsto_pow_atTop_atTop_of_one_lt (cone k)
  have B : Tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / ⌊c k ^ n⌋₊) atTop (𝓝 (c k)) := by
    simp only [one_mul, div_one] at A
    convert A using 1
    ext1 n
    field_simp [(zero_lt_one.trans (cone k)).ne']
    ring
  filter_upwards [(tendsto_order.1 B).2 a hk] with n hn
  exact (div_le_iff₀ (H n)).1 hn.le

/-- The sum of `1/(c^i)^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
theorem sum_div_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (c ^ i) ^ 2) ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : (0 : ℝ) < c⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.2 cpos)
  have B : c ^ 2 * ((1 : ℝ) - c⁻¹ ^ 2)⁻¹ ≤ c ^ 3 * (c - 1)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ _ (sub_pos.2 hc)]
    swap
    · exact sub_pos.2 (pow_lt_one₀ (inv_nonneg.2 cpos.le) (inv_lt_one_of_one_lt₀ hc) two_ne_zero)
    have : c ^ 3 = c ^ 2 * c := by ring
    simp only [mul_sub, this, mul_one, inv_pow, sub_le_sub_iff_left]
    rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel₀ (sq_pos_of_pos cpos).ne', one_mul]
    simpa using pow_right_mono₀ hc.le one_le_two
  have C : c⁻¹ ^ 2 < 1 := pow_lt_one₀ (inv_nonneg.2 cpos.le) (inv_lt_one_of_one_lt₀ hc) two_ne_zero
  calc
    (∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (c ^ i) ^ 2) ≤
        ∑ i ∈ Ico ⌊Real.log j / Real.log c⌋₊ N, (1 : ℝ) / (c ^ i) ^ 2 := by
      gcongr
      intro i hi
      simp only [mem_filter, mem_range] at hi
      simp only [hi.1, mem_Ico, and_true]
      apply Nat.floor_le_of_le
      apply le_of_lt
      rw [div_lt_iff₀ (Real.log_pos hc), ← Real.log_pow]
      exact Real.log_lt_log hj hi.2
    _ = ∑ i ∈ Ico ⌊Real.log j / Real.log c⌋₊ N, (c⁻¹ ^ 2) ^ i := by
      simp [← pow_mul, mul_comm]
    _ ≤ (c⁻¹ ^ 2) ^ ⌊Real.log j / Real.log c⌋₊ / ((1 : ℝ) - c⁻¹ ^ 2) :=
      geom_sum_Ico_le_of_lt_one (sq_nonneg _) C
    _ ≤ (c⁻¹ ^ 2) ^ (Real.log j / Real.log c - 1) / ((1 : ℝ) - c⁻¹ ^ 2) := by
      gcongr
      · exact sub_nonneg.2 C.le
      · rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge A C.le (Nat.sub_one_lt_floor _).le
    _ = c ^ 2 * ((1 : ℝ) - c⁻¹ ^ 2)⁻¹ / j ^ 2 := by
      have I : (c⁻¹ ^ 2) ^ (Real.log j / Real.log c) = (1 : ℝ) / j ^ 2 := by
        apply Real.log_injOn_pos (Real.rpow_pos_of_pos A _)
        · rw [Set.mem_Ioi]; positivity
        rw [Real.log_rpow A]
        simp only [one_div, Real.log_inv, Real.log_pow, mul_neg, neg_inj]
        field_simp [(Real.log_pos hc).ne']
      rw [Real.rpow_sub A, I]
      have : c ^ 2 - 1 ≠ 0 := (sub_pos.2 (one_lt_pow₀ hc two_ne_zero)).ne'
      simp
      ring
    _ ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by gcongr

theorem mul_pow_le_nat_floor_pow {c : ℝ} (hc : 1 < c) (i : ℕ) : (1 - c⁻¹) * c ^ i ≤ ⌊c ^ i⌋₊ := by
  have cpos : 0 < c := zero_lt_one.trans hc
  rcases eq_or_ne i 0 with (rfl | hi)
  · simp only [pow_zero, Nat.floor_one, Nat.cast_one, mul_one, sub_le_self_iff, inv_nonneg, cpos.le]
  calc
    (1 - c⁻¹) * c ^ i = c ^ i - c ^ i * c⁻¹ := by ring
    _ ≤ c ^ i - 1 := by
      gcongr
      simpa only [← div_eq_mul_inv, one_le_div cpos, pow_one] using le_self_pow₀ hc.le hi
    _ ≤ ⌊c ^ i⌋₊ := (Nat.sub_one_lt_floor _).le

/-- The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
theorem sum_div_nat_floor_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i ∈ range N with j < ⌊c ^ i⌋₊, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2) ≤
      c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : 0 < 1 - c⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hc)
  calc
    (∑ i ∈ range N with j < ⌊c ^ i⌋₊, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2) ≤
        ∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2 := by
      gcongr
      exact fun k hk ↦ hk.trans_le <| Nat.floor_le (by positivity)
    _ ≤ ∑ i ∈ range N with j < c ^ i, (1 - c⁻¹)⁻¹ ^ 2 * ((1 : ℝ) / (c ^ i) ^ 2) := by
      gcongr with i
      rw [mul_div_assoc', mul_one, div_le_div_iff₀]; rotate_left
      · apply sq_pos_of_pos
        refine zero_lt_one.trans_le ?_
        simp only [Nat.le_floor, one_le_pow₀, hc.le, Nat.one_le_cast, Nat.cast_one]
      · exact sq_pos_of_pos (pow_pos cpos _)
      rw [one_mul, ← mul_pow]
      gcongr
      rw [← div_eq_inv_mul, le_div_iff₀ A, mul_comm]
      exact mul_pow_le_nat_floor_pow hc i
    _ ≤ (1 - c⁻¹)⁻¹ ^ 2 * (c ^ 3 * (c - 1)⁻¹) / j ^ 2 := by
      rw [← mul_sum, ← mul_div_assoc']
      gcongr
      exact sum_div_pow_sq_le_div_sq N hj hc
    _ = c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
      congr 1
      field_simp
