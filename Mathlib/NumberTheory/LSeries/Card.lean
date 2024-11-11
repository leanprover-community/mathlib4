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
`Nat.card {x | F x ≤ n} / n' tends to `l`. In this file, we prove results on the L-series with
coefficients `Nat.card {x | F x = n}`.

## Main results.

* `NumberTheory.LSeriesSummable_card_eq`: the L-series with coefficients `Nat.card {x | F x = n}`
  is summable for `s ∈ ℂ` with `1 < s.re`.

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

end val

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

end main_results

end NumberTheory.LSeries.card
