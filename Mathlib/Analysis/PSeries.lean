/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

#align_import analysis.p_series from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open Filter

open BigOperators ENNReal NNReal Topology

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/


namespace Finset

variable {M : Type*} [OrderedAddCommMonoid M] {f : ℕ → M}

theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in Ico 1 (2 ^ n), f k) ≤ ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  induction' n with n ihn
  -- ⊢ ∑ k in Ico 1 (2 ^ Nat.zero), f k ≤ ∑ k in range Nat.zero, 2 ^ k • f (2 ^ k)
  · simp
    -- 🎉 no goals
  suffices (∑ k in Ico (2 ^ n) (2 ^ (n + 1)), f k) ≤ 2 ^ n • f (2 ^ n) by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts [n.one_le_two_pow, Nat.pow_le_pow_of_le_right zero_lt_two n.le_succ]
  have : ∀ k ∈ Ico (2 ^ n) (2 ^ (n + 1)), f k ≤ f (2 ^ n) := fun k hk =>
    hf (pow_pos zero_lt_two _) (mem_Ico.mp hk).1
  convert sum_le_sum this
  -- ⊢ 2 ^ n • f (2 ^ n) = ∑ i in Ico (2 ^ n) (2 ^ (n + 1)), f (2 ^ n)
  simp [pow_succ, two_mul]
  -- 🎉 no goals
#align finset.le_sum_condensed' Finset.le_sum_condensed'

theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (2 ^ n), f k) ≤ f 0 + ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  convert add_le_add_left (le_sum_condensed' hf n) (f 0)
  -- ⊢ ∑ k in range (2 ^ n), f k = f 0 + ∑ k in Ico 1 (2 ^ n), f k
  rw [← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ, sum_range_zero, zero_add]
  -- 🎉 no goals
#align finset.le_sum_condensed Finset.le_sum_condensed

theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k in Ico 2 (2 ^ n + 1), f k := by
  induction' n with n ihn
  -- ⊢ ∑ k in range Nat.zero, 2 ^ k • f (2 ^ (k + 1)) ≤ ∑ k in Ico 2 (2 ^ Nat.zero  …
  · simp
    -- 🎉 no goals
  suffices 2 ^ n • f (2 ^ (n + 1)) ≤ ∑ k in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f k by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exacts [add_le_add ihn this,
      (add_le_add_right n.one_le_two_pow _ : 1 + 1 ≤ 2 ^ n + 1),
      add_le_add_right (Nat.pow_le_pow_of_le_right zero_lt_two n.le_succ) _]
  have : ∀ k ∈ Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ (n + 1)) ≤ f k := fun k hk =>
    hf (n.one_le_two_pow.trans_lt <| (Nat.lt_succ_of_le le_rfl).trans_le (mem_Ico.mp hk).1)
      (Nat.le_of_lt_succ <| (mem_Ico.mp hk).2)
  convert sum_le_sum this
  -- ⊢ 2 ^ n • f (2 ^ (n + 1)) = ∑ i in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ ( …
  simp [pow_succ, two_mul]
  -- 🎉 no goals
#align finset.sum_condensed_le' Finset.sum_condensed_le'

theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k in Ico 2 (2 ^ n + 1), f k := by
  convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1)
  -- ⊢ ∑ k in range (n + 1), 2 ^ k • f (2 ^ k) = f 1 + 2 • ∑ k in range n, 2 ^ k •  …
  simp [sum_range_succ', add_comm, pow_succ, mul_nsmul', sum_nsmul]
  -- 🎉 no goals
#align finset.sum_condensed_le Finset.sum_condensed_le

end Finset

namespace ENNReal

variable {f : ℕ → ℝ≥0∞}

theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    ∑' k, f k ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (Nat.tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  -- ⊢ ⨆ (i : ℕ), ∑ a in Finset.range (2 ^ i), f a ≤ f 0 + ∑' (k : ℕ), ↑(2 ^ k) * f …
  refine' iSup_le fun n => (Finset.le_sum_condensed hf n).trans (add_le_add_left _ _)
  -- ⊢ ∑ k in Finset.range n, 2 ^ k • f (2 ^ k) ≤ ∑' (k : ℕ), ↑(2 ^ k) * f (2 ^ k)
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  -- ⊢ ∑ x in Finset.range n, 2 ^ x * f (2 ^ x) ≤ ∑' (k : ℕ), 2 ^ k * f (2 ^ k)
  apply ENNReal.sum_le_tsum
  -- 🎉 no goals
#align ennreal.le_tsum_condensed ENNReal.le_tsum_condensed

theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id), two_mul, ← two_nsmul]
  -- ⊢ ⨆ (i : ℕ), ∑ a in Finset.range (Nat.succ i), ↑(2 ^ a) * f (2 ^ a) ≤ f 1 + 2  …
  refine'
    iSup_le fun n =>
      le_trans _
        (add_le_add_left
          (nsmul_le_nsmul_of_le_right (ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)) _) _)
  simpa using Finset.sum_condensed_le hf n
  -- 🎉 no goals
#align ennreal.tsum_condensed_le ENNReal.tsum_condensed_le

end ENNReal

namespace NNReal

/-- Cauchy condensation test for a series of `NNReal` version. -/
theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ≥0) ^ k * f (2 ^ k)) ↔ Summable f := by
  simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Ne.def, not_iff_not, ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_two]
  constructor <;> intro h
  -- ⊢ ∑' (b : ℕ), 2 ^ b * ↑(f (2 ^ b)) = ⊤ → ∑' (b : ℕ), ↑(f b) = ⊤
                  -- ⊢ ∑' (b : ℕ), ↑(f b) = ⊤
                  -- ⊢ ∑' (b : ℕ), 2 ^ b * ↑(f (2 ^ b)) = ⊤
  · replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    simpa [h, ENNReal.add_eq_top, ENNReal.mul_eq_top] using ENNReal.tsum_condensed_le hf
    -- 🎉 no goals
  · replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf hm hmn)
    simpa [h, ENNReal.add_eq_top] using ENNReal.le_tsum_condensed hf
    -- 🎉 no goals
#align nnreal.summable_condensed_iff NNReal.summable_condensed_iff

end NNReal

/-- Cauchy condensation test for series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  lift f to ℕ → ℝ≥0 using h_nonneg
  -- ⊢ (Summable fun k => 2 ^ k * (fun i => ↑(f i)) (2 ^ k)) ↔ Summable fun i => ↑( …
  simp only [NNReal.coe_le_coe] at *
  -- ⊢ (Summable fun k => 2 ^ k * ↑(f (2 ^ k))) ↔ Summable fun i => ↑(f i)
  exact_mod_cast NNReal.summable_condensed_iff h_mono
  -- 🎉 no goals
#align summable_condensed_iff_of_nonneg summable_condensed_iff_of_nonneg

open Real

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/


/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  cases' le_or_lt 0 p with hp hp
  -- ⊢ (Summable fun n => (↑n ^ p)⁻¹) ↔ 1 < p
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow, ← mul_pow,
        summable_geometric_iff_norm_lt_1]
      nth_rw 1 [← rpow_one 2]
      -- ⊢ ‖2 ^ 1 * (2 ^ p)⁻¹‖ < 1 ↔ 1 < p
      rw [← division_def, ← rpow_sub zero_lt_two, norm_eq_abs,
        abs_of_pos (rpow_pos_of_pos zero_lt_two _), rpow_lt_one_iff zero_lt_two.le]
      norm_num
      -- 🎉 no goals
    · intro n
      -- ⊢ 0 ≤ (↑n ^ p)⁻¹
      exact inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _)
      -- 🎉 no goals
    · intro m n hm hmn
      -- ⊢ (↑n ^ p)⁻¹ ≤ (↑m ^ p)⁻¹
      exact
        inv_le_inv_of_le (rpow_pos_of_pos (Nat.cast_pos.2 hm) _)
          (rpow_le_rpow m.cast_nonneg (Nat.cast_le.2 hmn) hp)
  -- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges.
  · suffices ¬Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) by
      have : ¬1 < p := fun hp₁ => hp.not_le (zero_le_one.trans hp₁.le)
      simpa only [this, iff_false]
    · intro h
      -- ⊢ False
      obtain ⟨k : ℕ, hk₁ : ((k : ℝ) ^ p)⁻¹ < 1, hk₀ : k ≠ 0⟩ :=
        ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
            (eventually_cofinite_ne 0)).exists
      apply hk₀
      -- ⊢ k = 0
      rw [← pos_iff_ne_zero, ← @Nat.cast_pos ℝ] at hk₀
      -- ⊢ k = 0
      simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
        hp.not_lt, hk₀] using hk₁
#align real.summable_nat_rpow_inv Real.summable_nat_rpow_inv

@[simp]
theorem Real.summable_nat_rpow {p : ℝ} : Summable (fun n => (n : ℝ) ^ p : ℕ → ℝ) ↔ p < -1 := by
  rcases neg_surjective p with ⟨p, rfl⟩
  -- ⊢ (Summable fun n => ↑n ^ (-p)) ↔ -p < -1
  simp [rpow_neg]
  -- 🎉 no goals
#align real.summable_nat_rpow Real.summable_nat_rpow

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp
  -- 🎉 no goals
#align real.summable_one_div_nat_rpow Real.summable_one_div_nat_rpow

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
-- porting note: temporarily remove `@[simp]` because of a problem with `simp`
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/looping.20in.20.60simp.60.20set/near/361134234
theorem Real.summable_nat_pow_inv {p : ℕ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  simp only [← rpow_nat_cast, Real.summable_nat_rpow_inv, Nat.one_lt_cast]
  -- 🎉 no goals
#align real.summable_nat_pow_inv Real.summable_nat_pow_inv

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_pow {p : ℕ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  -- Porting note: was `simp`
  simp only [one_div, Real.summable_nat_pow_inv]
  -- 🎉 no goals
#align real.summable_one_div_nat_pow Real.summable_one_div_nat_pow

/-- Summability of the `p`-series over `ℤ`. -/
theorem Real.summable_one_div_int_pow {p : ℕ} :
    (Summable fun n : ℤ => 1 / (n : ℝ) ^ p) ↔ 1 < p := by
  refine'
    ⟨fun h => Real.summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective), fun h =>
      summable_int_of_summable_nat (Real.summable_one_div_nat_pow.mpr h)
        (((Real.summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1 : ℝ) ^ p).congr fun n => _)⟩
  conv_rhs =>
    rw [Int.cast_neg, neg_eq_neg_one_mul, mul_pow, ← div_div]
  conv_lhs => rw [mul_div, mul_one]
  -- 🎉 no goals
#align real.summable_one_div_int_pow Real.summable_one_div_int_pow

theorem Real.summable_abs_int_rpow {b : ℝ} (hb : 1 < b) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (-b) := by
  -- Porting note: was
  -- refine'
  --   summable_int_of_summable_nat (_ : Summable fun n : ℕ => |(n : ℝ)| ^ _)
  --     (_ : Summable fun n : ℕ => |((-n : ℤ) : ℝ)| ^ _)
  -- on_goal 2 => simp_rw [Int.cast_neg, Int.cast_ofNat, abs_neg]
  -- all_goals
  --   simp_rw [fun n : ℕ => abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))]
  --   rwa [Real.summable_nat_rpow, neg_lt_neg_iff]
  apply summable_int_of_summable_nat
  -- ⊢ Summable fun n => |↑↑n| ^ (-b)
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  -- ⊢ Summable fun n => |↑↑n| ^ (-b)
  -- ⊢ Summable fun n => |↑↑n| ^ (-b)
  all_goals
    simp_rw [Int.cast_ofNat, fun n : ℕ => abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))]
    rwa [Real.summable_nat_rpow, neg_lt_neg_iff]
#align real.summable_abs_int_rpow Real.summable_abs_int_rpow

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_nat_cast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) := by
  have : ¬Summable (fun n => ((n : ℝ) ^ 1)⁻¹ : ℕ → ℝ) :=
    mt (Real.summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa
  -- 🎉 no goals
#align real.not_summable_nat_cast_inv Real.not_summable_nat_cast_inv

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_one_div_nat_cast : ¬Summable (fun n => 1 / n : ℕ → ℝ) := by
  simpa only [inv_eq_one_div] using Real.not_summable_nat_cast_inv
  -- 🎉 no goals
#align real.not_summable_one_div_nat_cast Real.not_summable_one_div_nat_cast

/-- **Divergence of the Harmonic Series** -/
theorem Real.tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i in Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 Real.not_summable_one_div_nat_cast
    -- 🎉 no goals
  · exact fun i => div_nonneg zero_le_one i.cast_add_one_pos.le
    -- 🎉 no goals
#align real.tendsto_sum_range_one_div_nat_succ_at_top Real.tendsto_sum_range_one_div_nat_succ_atTop

@[simp]
theorem NNReal.summable_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ≥0) ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p := by
  simp [← NNReal.summable_coe]
  -- 🎉 no goals
#align nnreal.summable_rpow_inv NNReal.summable_rpow_inv

@[simp]
theorem NNReal.summable_rpow {p : ℝ} : Summable (fun n => (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ p < -1 := by
  simp [← NNReal.summable_coe]
  -- 🎉 no goals
#align nnreal.summable_rpow NNReal.summable_rpow

theorem NNReal.summable_one_div_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ 1 < p := by
  simp
  -- 🎉 no goals
#align nnreal.summable_one_div_rpow NNReal.summable_one_div_rpow

section

open Finset

variable {α : Type*} [LinearOrderedField α]

theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (∑ i in Ioc k n, ((i : α) ^ 2)⁻¹) ≤ (k : α)⁻¹ - (n : α)⁻¹ := by
  refine' Nat.le_induction _ _ n h
  -- ⊢ ∑ i in Ioc k k, (↑i ^ 2)⁻¹ ≤ (↑k)⁻¹ - (↑k)⁻¹
  · simp only [Ioc_self, sum_empty, sub_self, le_refl]
    -- 🎉 no goals
  intro n hn IH
  -- ⊢ ∑ i in Ioc k (n + 1), (↑i ^ 2)⁻¹ ≤ (↑k)⁻¹ - (↑(n + 1))⁻¹
  rw [sum_Ioc_succ_top hn]
  -- ⊢ ∑ k in Ioc k n, (↑k ^ 2)⁻¹ + (↑(n + 1) ^ 2)⁻¹ ≤ (↑k)⁻¹ - (↑(n + 1))⁻¹
  apply (add_le_add IH le_rfl).trans
  -- ⊢ (↑k)⁻¹ - (↑n)⁻¹ + (↑(n + 1) ^ 2)⁻¹ ≤ (↑k)⁻¹ - (↑(n + 1))⁻¹
  simp only [sub_eq_add_neg, add_assoc, Nat.cast_add, Nat.cast_one, le_add_neg_iff_add_le,
    add_le_iff_nonpos_right, neg_add_le_iff_le_add, add_zero]
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  -- ⊢ ((↑n + 1) ^ 2)⁻¹ + (↑n + 1)⁻¹ ≤ (↑n)⁻¹
  have B : 0 < (n : α) + 1 := by linarith
  -- ⊢ ((↑n + 1) ^ 2)⁻¹ + (↑n + 1)⁻¹ ≤ (↑n)⁻¹
  field_simp
  -- ⊢ (↑n + 1 + (↑n + 1) ^ 2) / ((↑n + 1) ^ 2 * (↑n + 1)) ≤ 1 / ↑n
  rw [div_le_div_iff _ A, ← sub_nonneg]
  -- ⊢ 0 ≤ 1 * ((↑n + 1) ^ 2 * (↑n + 1)) - (↑n + 1 + (↑n + 1) ^ 2) * ↑n
  · ring_nf
    -- ⊢ 0 ≤ 1 + ↑n
    rw [add_comm]
    -- ⊢ 0 ≤ ↑n + 1
    exact B.le
    -- 🎉 no goals
  · -- Porting note: was `nlinarith`
    positivity
    -- 🎉 no goals
#align sum_Ioc_inv_sq_le_sub sum_Ioc_inv_sq_le_sub

theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) ≤ 2 / (k + 1) :=
  calc
    (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) ≤ ∑ i in Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      -- ⊢ Ioo k n ⊆ Ioc k (max (k + 1) n)
      · intro x hx
        -- ⊢ x ∈ Ioc k (max (k + 1) n)
        simp only [mem_Ioo] at hx
        -- ⊢ x ∈ Ioc k (max (k + 1) n)
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true_iff, and_self_iff]
        -- 🎉 no goals
      · intro i _hi _hident
        -- ⊢ 0 ≤ (↑i ^ 2)⁻¹
        positivity
        -- 🎉 no goals
    _ ≤ ((k + 1 : α) ^ 2)⁻¹ + ∑ i in Ioc k.succ (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      rw [← Nat.Icc_succ_left, ← Nat.Ico_succ_right, sum_eq_sum_Ico_succ_bot]
      -- ⊢ (↑(Nat.succ k) ^ 2)⁻¹ + ∑ k in Ico (Nat.succ k + 1) (Nat.succ (max (k + 1) n …
      swap; · exact Nat.succ_lt_succ ((Nat.lt_succ_self k).trans_le (le_max_left _ _))
      -- ⊢ Nat.succ k < Nat.succ (max (k + 1) n)
              -- 🎉 no goals
      rw [Nat.Ico_succ_right, Nat.Icc_succ_left, Nat.cast_succ]
      -- 🎉 no goals
    _ ≤ ((k + 1 : α) ^ 2)⁻¹ + (k + 1 : α)⁻¹ := by
      refine' add_le_add le_rfl ((sum_Ioc_inv_sq_le_sub _ (le_max_left _ _)).trans _)
      -- ⊢ Nat.succ k ≠ 0
      · simp only [Ne.def, Nat.succ_ne_zero, not_false_iff]
        -- 🎉 no goals
      · simp only [Nat.cast_succ, one_div, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
        -- 🎉 no goals
    _ ≤ 1 / (k + 1) + 1 / (k + 1) := by
      have A : (1 : α) ≤ k + 1 := by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      -- ⊢ ((↑k + 1) ^ 2)⁻¹ + (↑k + 1)⁻¹ ≤ 1 / (↑k + 1) + 1 / (↑k + 1)
      simp_rw [← one_div]
      -- ⊢ 1 / (↑k + 1) ^ 2 + 1 / (↑k + 1) ≤ 1 / (↑k + 1) + 1 / (↑k + 1)
      apply add_le_add_right
      -- ⊢ 1 / (↑k + 1) ^ 2 ≤ 1 / (↑k + 1)
      refine' div_le_div zero_le_one le_rfl (zero_lt_one.trans_le A) _
      -- ⊢ ↑k + 1 ≤ (↑k + 1) ^ 2
      simpa using pow_le_pow A one_le_two
      -- 🎉 no goals
    _ = 2 / (k + 1) := by ring
                          -- 🎉 no goals

#align sum_Ioo_inv_sq_le sum_Ioo_inv_sq_le

end
