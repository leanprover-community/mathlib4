/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of counting functions

Let `F : α → ℕ` be a function. Assume that there exists a positive real `l` such that
`#{x | F x ≤ n} / n' tends to `l`. In this file, we prove results on the L-series defined by the
function `n ↦ Nat.card {x | F x = n}`.

## Main results.

* `NumberTheory.LSeriesSummable_card_eq`: the L-series defined by `n ↦ Nat.card {x | F x = n}`
  is summable for `s ∈ ℂ` with `1 < s.re`.

* `NumberTheory.LSeries.card_eq_residue` : the L-series defined by
  `n ↦ Nat.card {x | F x = n}` has a simple pole at `s = 1` of residue `l`.

* `NumberTheory.LSeries.abscissaOfAbsConv_card_eq `: the L-series defined by
  `n ↦ Nat.card {x | F x = n}` has abscissa of absolute convergence `1`.
-/

open Filter Topology Complex Metric LSeries

namespace NumberTheory.LSeries.card

variable {α : Type*} {F : α → ℕ} {l : ℝ}
  (hF : Tendsto (fun n ↦ (Nat.card {x | F x ≤ n} : ℝ) / n) atTop (𝓝 l)) (hl : 0 < l)

section card_le

include hF hl

theorem finite_card_le (n : ℕ) :
    {x | F x ≤ n}.Finite := by
  contrapose! hl
  have h_card : ∀ ⦃m⦄, n ≤ m → Nat.card {x | F x ≤ m} = 0 :=
    fun _ h ↦ Set.Nat.card_coe_set_eq _ ▸ (Set.Infinite.mono (fun _ h' ↦ h'.trans h) hl).ncard
  suffices Tendsto (fun n ↦ (Nat.card {x | F x ≤ n} : ℝ) / n) atTop (𝓝 0) by
    rw [tendsto_nhds_unique hF this]
  exact tendsto_atTop_of_eventually_const fun _ h ↦ by rw [h_card h, Nat.cast_zero, zero_div]

theorem finite_card_eq (n : ℕ) :
    {x | F x = n}.Finite :=
  (finite_card_le hF hl n).subset fun _ h ↦ h.le

theorem card_eq_succ_add_card_le (n : ℕ) :
    Nat.card {x | F x = n + 1} + Nat.card {x | F x ≤ n} = Nat.card {x | F x ≤ n + 1} := by
  classical
  have : ∀ n, Fintype {x | F x ≤ n} := fun _ ↦ (finite_card_le hF hl _).fintype
  have : ∀ n, Fintype {x | F x = n} := fun _ ↦ (finite_card_eq hF hl _).fintype
  rw [Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset,
    ← Finset.card_union_of_disjoint]
  · congr with x
    simpa [← Nat.lt_add_one_iff (n := n)] using le_iff_eq_or_lt.symm
  · exact Finset.disjoint_left.mpr fun _ h ↦ by simp_all

theorem card_le_not_bounded (N : ℕ) :
    ∃ n, N ≤ Nat.card {x | F x ≤ n} := by
  contrapose! hl
  refine tendsto_le_of_eventuallyLE hF (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)) ?_
  filter_upwards with n using div_le_div_of_nonneg_right (Nat.cast_le.mpr (hl n).le) n.cast_nonneg

theorem mono_card_le :
    Monotone (Nat.card {x | F x ≤ ·}) :=
  fun _ _ h₁ ↦ Nat.card_mono (finite_card_le hF hl _) fun _ h₂ ↦ h₂.trans h₁

end card_le

noncomputable section val

variable (F) in
/-- The sequence of values taken by `F` sorted by increasing order, see `card_val_eq_succ` and
`monotone_val`. -/
def val (k : ℕ) : ℕ := sInf {n : ℕ | k ≤ Nat.card {x | F x ≤ n}}

include hl hF

theorem val_eq_succ_iff {k n : ℕ} :
    val F k = n + 1 ↔ Nat.card {x | F x ≤ n} < k ∧ k ≤ Nat.card {x | F x ≤ n + 1} := by
  rw [val, Nat.sInf_upward_closed_eq_succ_iff, Set.mem_setOf_eq, Set.mem_setOf_eq, not_le, and_comm]
  exact fun _ _ h₁ h₂ ↦ h₂.trans (mono_card_le hF hl h₁)

/-- For `0 < n`, there are as many `k : ℕ` such that `val k = n` than elements `x : α` such
that `F x = n`.-/
theorem card_val_eq_succ (n : ℕ) : Nat.card {k | val F k = n + 1} = Nat.card {x | F x = n + 1} := by
  simp_rw [val_eq_succ_iff hF hl, ← Finset.mem_Ioc, Finset.setOf_mem, Nat.card_eq_card_toFinset,
    Finset.toFinset_coe, Nat.card_Ioc, (Nat.eq_sub_of_add_eq (card_eq_succ_add_card_le hF hl n))]

theorem val_not_bounded (n : ℕ) :
    ∃ k, n ≤ val F k :=
  ⟨Nat.card {x | F x ≤ n} + 1,
    le_csInf (card_le_not_bounded hF hl _) fun _ h ↦  ((mono_card_le hF hl).reflect_lt h).le⟩

theorem mono_val : Monotone (val F) :=
  fun _ _ h ↦ le_csInf (card_le_not_bounded hF hl _)
    fun _ h' ↦ csInf_le (OrderBot.bddBelow _) (h.trans h')

theorem tendsto_atTop_val : Tendsto (val F) atTop atTop :=
  Monotone.tendsto_atTop_atTop (mono_val hF hl) (val_not_bounded hF hl)

theorem finite_val_eq (n : ℕ) :
    {k | val F k = n}.Finite := by
  rw [← compl_mem_cofinite, show {k | val F k = n} = val F ⁻¹' {n} by rfl, ← Set.preimage_compl]
  exact (Nat.cofinite_eq_atTop ▸ tendsto_atTop_val hF hl) (by simp)

/-- A consequence of `card_val_eq_succ` that is useful later on. -/
theorem card_eq_div_pow_eq_tsum_fiber (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    (Nat.card {x | F x = n}) / (n : ℝ) ^ s = ∑' (k : ↑(val F ⁻¹' {n})), 1 / (val F k : ℝ) ^ s := by
  have : Fintype {x | val F x = n} := (finite_val_eq hF hl n).fintype
  have : Fintype {x | F x = n} := (finite_card_eq hF hl n).fintype
  rw [← Equiv.tsum_eq (Equiv.setCongr (by rfl : {k | val F k = n} = val F ⁻¹' {n})), tsum_fintype,
    Finset.sum_congr rfl (fun x _ ↦ by rw [Equiv.setCongr_apply, x.prop]), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one_div]
  cases n with
  | zero => simp only [Nat.cast_zero, Real.zero_rpow hs, div_zero]
  | succ n => rw [← card_val_eq_succ hF hl n, ← Nat.card_eq_fintype_card]

private theorem tendsto_atTop_div_val_aux₁ :
    ∀ᶠ k in atTop, (Nat.card {x | F x ≤ val F k - 1} : ℝ) / (val F k - 1) * (1 - 1 / val F k) ≤
      (k : ℝ) / (val F k) := by
  filter_upwards [(tendsto_atTop.mp (tendsto_atTop_val hF hl)) 2] with k hk
  rw [one_sub_div (by positivity), ← mul_div_assoc, div_mul_cancel₀]
  · refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_of_lt ?_)) (by positivity)
    simpa only [Set.coe_setOf, Set.mem_setOf_eq, not_le] using
      Nat.not_mem_of_lt_sInf (Nat.sub_one_lt_of_lt hk)
  · rw [sub_ne_zero, Nat.cast_ne_one]
    linarith

private theorem tendsto_atTop_div_val_aux₂ :
  ∀ᶠ k : ℕ in atTop, (k : ℝ) / (val F k) ≤
    (Nat.card {x | F x ≤ val F k + 1} : ℝ) / (val F k + 1) * (1 + 1 / val F k) := by
  filter_upwards [(tendsto_atTop.mp (tendsto_atTop_val hF hl)) 2] with k hk
  rw [one_add_div (by positivity), ← mul_div_assoc, div_mul_cancel₀ _ (by positivity)]
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _)
  refine le_trans ?_ (mono_card_le hF hl (Nat.le_succ _))
  exact Nat.sInf_mem (card_le_not_bounded hF hl k)

/-- The sequence `k ↦ k / val k` also tends to `l` at top. -/
theorem tendsto_atTop_div_val : Tendsto (fun k : ℕ ↦ (k : ℝ) / (val F k)) atTop (𝓝 l) := by
  have h : Tendsto (fun k ↦ 1 / (val F k : ℝ)) atTop (𝓝 0) := by
    simp_rw [one_div]
    exact Tendsto.inv_tendsto_atTop <| tendsto_natCast_atTop_iff.mpr (tendsto_atTop_val hF hl)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (tendsto_atTop_div_val_aux₁ hF hl) (tendsto_atTop_div_val_aux₂ hF hl)
  · rw [show 𝓝 l = 𝓝 (l * (1 - 0)) by rw [sub_zero, mul_one]]
    refine Tendsto.mul ?_ (h.const_sub 1)
    refine (hF.comp <| (tendsto_sub_atTop_nat 1).comp (tendsto_atTop_val hF hl)).congr' ?_
    filter_upwards [(tendsto_atTop.mp (tendsto_atTop_val hF hl)) 1] with k hk
    simp_rw [Function.comp_apply, Nat.cast_pred hk]
  · rw [show 𝓝 l = 𝓝 (l * (1 + 0)) by rw [add_zero, mul_one]]
    refine Tendsto.mul ?_ (h.const_add 1)
    exact (hF.comp ((tendsto_add_atTop_nat 1).comp (tendsto_atTop_val hF hl))).congr fun _ ↦ by simp

theorem eventually_lt_one_div_val_rpow_lt {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℝ, 0 < s → (l - ε) ^ s / (k : ℝ) ^ s < 1 / val F k ^ s ∧
      1 / val F k ^ s < (l + ε) ^ s / (k : ℝ) ^ s := by
  rw [← sub_nonneg] at hε₂ -- To help positivity
  filter_upwards [eventually_gt_atTop 0, tendsto_nhds.mp (tendsto_atTop_div_val hF hl) ε hε₁]
    with n hn h s hs
  rwa [div_lt_iff₀', lt_div_iff₀', mul_one_div, ← Real.div_rpow, Real.rpow_lt_rpow_iff,
    Real.rpow_lt_rpow_iff, ← neg_add_lt_iff_lt_add, sub_eq_add_neg, ← lt_neg_add_iff_add_lt,
    neg_add_eq_sub, ← abs_lt]
  all_goals positivity

theorem summable_one_div_val_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n ↦ 1 / (val F n : ℝ) ^ s) := by
  refine summable_of_isBigO_nat' (Real.summable_one_div_nat_rpow.mpr hs)
    (Asymptotics.isBigO_iff.mpr ⟨(l + l) ^ s, ?_⟩)
  filter_upwards [eventually_lt_one_div_val_rpow_lt hF hl hl le_rfl] with k hk
  convert (hk s (zero_lt_one.trans hs)).2.le using 1
  · rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
  · rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity), mul_one_div]

theorem card_eq_div_pow_eq_tsum (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    (Nat.card {x | F x = n}) / (n : ℝ) ^ s = ∑' (k : ↑(val F ⁻¹' {n})), 1 / (val F k : ℝ) ^ s := by
  have : Fintype {x | val F x = n} := (finite_val_eq hF hl n).fintype
  have : Fintype {x | F x = n} := (finite_card_eq hF hl n).fintype
  rw [← Equiv.tsum_eq (Equiv.setCongr (by rfl : {k | val F k = n} = val F ⁻¹' {n})), tsum_fintype,
    Finset.sum_congr rfl (fun x _ ↦ by rw [Equiv.setCongr_apply, x.prop]), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one_div]
  cases n with
  | zero => simp only [Nat.cast_zero, Real.zero_rpow hs, div_zero]
  | succ n => rw [← card_val_eq_succ hF hl n, ← Nat.card_eq_fintype_card]

theorem tsum_card_eq_div_rpow_eq_tsum :
    (fun s : ℝ ↦ ∑' n, Nat.card {x | F x = n} / (n : ℝ) ^ s) =ᶠ[𝓝[>] 1]
    (fun s ↦ ∑' k, 1 / (val F k : ℝ) ^ s) := by
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  convert HasSum.tsum_eq (HasSum.tsum_fiberwise
    (Summable.hasSum (summable_one_div_val_rpow hF hl hs)) (val F)) with n
  exact card_eq_div_pow_eq_tsum hF hl n (zero_lt_one.trans hs).ne'

end val

section tendsto

theorem tendsto_sub_mul_sum_one_div_rpow (T : Finset ℕ) (v : ℕ → ℕ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑ n ∈ T, 1 / (v n : ℝ) ^ s) (𝓝 1) (𝓝 0) := by
  simp_rw [Finset.mul_sum, one_div, show 𝓝 (0 : ℝ) = 𝓝 (∑ n ∈ T, 0 * 1 / (v n : ℝ) ^ (1 : ℝ)) by
    simp_rw [zero_mul, zero_div, Finset.sum_const, smul_zero]]
  refine tendsto_finset_sum _ fun n _ ↦ ?_
  by_cases hv : v n = 0
  · simp_rw [hv, Nat.cast_zero, zero_mul, zero_div]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_nhds one_ne_zero] with s hs
    rw [Real.zero_rpow hs, inv_zero, mul_zero]
  · refine Tendsto.mul ?_ ?_
    · convert (continuous_sub_right (1 : ℝ)).tendsto 1 using 2
      rw [zero_mul, sub_self]
    · convert (Real.continuousAt_const_rpow (Nat.cast_ne_zero.mpr hv)).tendsto.inv₀ ?_
      rwa [Real.rpow_one, Nat.cast_ne_zero]

theorem tendsto_rpow_mul_sub_mul_tsum_one_div_rpow {c : ℝ} (hc : c ≠ 0) (T : Finset ℕ) :
    Tendsto (fun s ↦ c ^ s * (s - 1) *
      ∑' n : ↑((T : Set ℕ)ᶜ), 1 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 c) := by
  simp_rw [mul_assoc, show 𝓝 c = 𝓝 (c * (1 - 0)) by rw [sub_zero, mul_one]]
  refine Tendsto.mul (tendsto_nhdsWithin_of_tendsto_nhds ?_) ?_
  · refine Continuous.tendsto' ?_ 1 c (by rw [Real.rpow_one])
    exact continuous_const.rpow continuous_id fun _ ↦ Or.inl hc
  · refine (tendsto_sub_mul_tsum_nat_rpow.sub (tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_sub_mul_sum_one_div_rpow T (fun n ↦ n)))).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    rw [sub_eq_iff_eq_add', ← mul_add, sum_add_tsum_compl (Real.summable_one_div_nat_rpow.mpr hs)]

include hl hF

theorem exist_finset_lt_sub_mul_tsum_one_div_val_rpow_lt {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε ≤ l) :
    ∃ T : Finset ℕ, ∀ s, 1 < s →
      (s - 1) * ∑ n ∈ T, 1 / (val F n : ℝ) ^ s +
        (l - ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), 1 / (n : ℝ) ^ s <
          (s - 1) * ∑' n, 1 / (val F n : ℝ) ^ s ∧
      (s - 1) * ∑' n, 1/ (val F n : ℝ) ^ s <
        (s - 1) * ∑ n ∈ T, 1 / (val F n : ℝ) ^ s +
          (l + ε) ^ s * (s - 1) * ∑' n : ↑((T : Set ℕ)ᶜ), 1 / (n : ℝ) ^ s := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp <| eventually_lt_one_div_val_rpow_lt hF hl hε₁ hε₂
  refine ⟨Finset.range N, fun s hs ↦ ?_⟩
  simp_rw [← sum_add_tsum_compl (s := Finset.range N) (summable_one_div_val_rpow hF hl hs), mul_add,
    add_lt_add_iff_left, mul_assoc, mul_left_comm _ (s- 1), mul_lt_mul_left (sub_pos.mpr hs),
    ← tsum_mul_left, mul_one_div]
  have h₁ : ∀ {S : Set ℕ} {c : ℝ}, Summable fun n : S ↦ c / (n : ℝ) ^ s :=
    ((Real.summable_nat_rpow_inv.mpr hs).mul_left _).subtype _
  have h₂ : ∀ {S : Set ℕ}, Summable fun n : S ↦ 1 / (val F n : ℝ) ^ s :=
    (summable_one_div_val_rpow hF hl hs).subtype _
  refine ⟨tsum_lt_tsum (i := ⟨N+1, by simp⟩) ?_ ?_ h₁ h₂,
    tsum_lt_tsum (i := ⟨N+1, by simp⟩) ?_ ?_ h₂ h₁ ⟩
  · rintro ⟨i, hi⟩
    simp only [Finset.coe_range, Set.compl_Iio, Set.mem_Ici] at hi
    exact (hN i hi s (zero_lt_one.trans hs)).1.le
  · exact (hN (N + 1) (Nat.le_add_right N 1) s (zero_lt_one.trans hs)).1
  · rintro ⟨i, hi⟩
    simp only [Finset.coe_range, Set.compl_Iio, Set.mem_Ici] at hi
    exact (hN i hi s (zero_lt_one.trans hs)).2.le
  · exact (hN (N + 1) (Nat.le_add_right N 1) s (zero_lt_one.trans hs)).2

theorem tendsto_sub_mul_tsum_one_div_val_rpow :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, 1 / (val F n : ℝ) ^ s) (𝓝[>] 1) (𝓝 l) := by
  refine tendsto_nhdsWithin_nhds.mpr fun ε' hε' ↦ ?_
  let ε := min l ε'
  have h₁ : 0 < ε := by aesop
  have h₂ : 0 < ε / 3 := by positivity
  have h₃ : ε / 3 < l := lt_of_lt_of_le (div_lt_self h₁ (by norm_num)) (min_le_left l ε')
  have h₄ : 0 < l - ε / 3 := sub_pos.mpr h₃
  have h₅ : 0 < l + ε / 3 := by positivity
  obtain ⟨T, hT⟩ := exist_finset_lt_sub_mul_tsum_one_div_val_rpow_lt hF hl h₂ h₃.le
  obtain ⟨δ₁, _, hδ₁⟩ := tendsto_nhds_nhds.mp
    (tendsto_sub_mul_sum_one_div_rpow T (val F)) (ε / 3) h₂
  obtain ⟨δ₂, _, hδ₂⟩ := tendsto_nhdsWithin_nhds.mp
    (tendsto_rpow_mul_sub_mul_tsum_one_div_rpow h₄.ne' T) (ε / 3) h₂
  obtain ⟨δ₃, _, hδ₃⟩ := tendsto_nhdsWithin_nhds.mp
    (tendsto_rpow_mul_sub_mul_tsum_one_div_rpow h₅.ne' T) (ε / 3) h₂
  let δ := min δ₁ (min δ₂ δ₃)
  refine ⟨δ, ?_, ?_⟩
  · simp_all only [lt_min_iff, and_self, Set.mem_Ioi, δ]
  · intro s hs hsδ
    specialize hδ₁ (lt_of_lt_of_le hsδ (by simp [δ]))
    specialize hδ₂ hs (lt_of_lt_of_le hsδ (by simp [δ]))
    specialize hδ₃ hs (lt_of_lt_of_le hsδ (by simp [δ]))
    simp_rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_lt] at hδ₁ hδ₂ hδ₃ ⊢
    constructor
    · refine lt_of_le_of_lt (neg_le_neg (min_le_right l ε'))
        (lt_trans ?_.trans (sub_lt_sub_right (hT s hs).1 l))
      rw [← add_thirds (min l ε'), neg_add', sub_lt_iff_lt_add, neg_add, sub_add, add_sub_assoc]
      exact add_lt_add hδ₁.1 hδ₂.1
    · refine lt_of_lt_of_le ((sub_lt_sub_right (hT s hs).2 l).trans ?_) (min_le_right l ε')
      rw [← add_thirds (min l ε'), ← sub_lt_iff_lt_add, sub_sub, add_sub_assoc]
      exact add_lt_add hδ₁.2 hδ₃.2

end tendsto

section main_results

open LSeries.notation

include hl hF

theorem _root_.NumberTheory.LSeriesSummable_card_eq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (↗(Nat.card {x | F x = ·})) s := by
  have h : ∀ᶠ n in atTop, (((Nat.card {x | F x = n} : ℝ) / (n : ℝ) ^ (s.re) : ℝ) : ℂ) =
      term (fun n ↦ (Nat.card ↑{x | F x = n})) s.re n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [term_def, if_neg hn.ne', ← ofReal_natCast n, ← ofReal_cpow (by positivity), ofReal_div,
      ofReal_natCast, div_eq_mul_inv]
  refine (LSeriesSummable_iff_of_re_eq_re (by rfl : s.re = (s.re : ℂ).re)).mpr <|
    Summable.congr_atTop ?_ h
  convert summable_ofReal.mpr ((summable_one_div_val_rpow hF hl hs).comp_injective
    (Equiv.sigmaFiberEquiv (val F)).injective).sigma with n
  exact card_eq_div_pow_eq_tsum hF hl n (by linarith)

theorem _root_.NumberTheory.LSeries.card_eq_residue :
    Tendsto (fun s : ℝ ↦ (s - 1) * L ↗(Nat.card {x | F x = ·}) s) (𝓝[>] 1) (𝓝 l) := by
  suffices Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, Nat.card {x | F x = n} / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 l) by
    rw [← tendsto_ofReal_iff] at this
    refine this.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    change 1 < (s : ℂ).re at hs
    simp_rw [LSeries_eq_tsum _ (ne_zero_of_one_lt_re hs), ofReal_mul, ofReal_sub, ofReal_one,
      ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
  exact (tendsto_sub_mul_tsum_one_div_val_rpow hF hl).congr' <| EventuallyEq.rfl.mul
    (tsum_card_eq_div_rpow_eq_tsum hF hl).symm

theorem _root_.NumberTheory.LSeries.abscissaOfAbsConv_card_eq :
    LSeries.abscissaOfAbsConv ↗(Nat.card {x | F x = ·}) = 1 := by
  refine le_antisymm ?_ ?_
  · exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs ↦
      LSeriesSummable_card_eq hF hl (EReal.coe_lt_coe_iff.mp hs)
  · have h_lim := LSeries.card_eq_residue hF hl
    contrapose! hl
    suffices Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ Nat.card {x | F x = n}) s)
        (𝓝[>] 1) (𝓝 0) by rw [ofReal_eq_zero.mp (tendsto_nhds_unique h_lim this)]
    rw [show 𝓝 0 = 𝓝 (0 * (LSeries (fun n ↦ ↑(Nat.card {x | F x = n})) 1)) by rw [zero_mul]]
    refine Tendsto.mul ?_ ?_
    · exact tendsto_sub_nhds_zero_iff.mpr continuous_ofReal.continuousWithinAt.tendsto
    · suffices ContinuousWithinAt (fun s : ℂ ↦ L ↗(Nat.card {x | F x = ·}) s)
          {s | 1 < s.re} 1 by
        convert Tendsto.comp this.tendsto
          (continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ x ↦ x)
      refine ((AnalyticOnNhd.continuousOn (LSeries_analyticOnNhd _)).continuousWithinAt ?_).mono ?_
      · simpa using hl
      · intro s hs
        exact hl.trans (EReal.coe_lt_coe_iff.mpr hs)

end main_results

end NumberTheory.LSeries.card
