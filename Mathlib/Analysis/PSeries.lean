/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SumOverResidueClass

#align_import analysis.p_series from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## Tags

p-series, Cauchy condensation test
-/

/-!
### Schlömilch's generalization of the Cauchy condensation test

In this section we prove the Schlömilch's generalization of the Cauchy condensation test:
for a strictly increasing `u : ℕ → ℕ` with ratio of successive differences bounded and an
antitone `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`, `∑ k, f k` converges if and only if
so does `∑ k, (u (k + 1) - u k) * f (u k)`. Instead of giving a monolithic proof, we split it
into a series of lemmas with explicit estimates of partial sums of each series in terms of the
partial sums of the other series.
-/

/--
A sequence `u` has the property that its ratio of successive differences is bounded
when there is a positive real number `C` such that, for all n ∈ ℕ,
(u (n + 2) - u (n + 1)) ≤ C * (u (n + 1) - u n)
-/
def SuccDiffBounded (C : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, u (n + 2) - u (n + 1) ≤ C • (u (n + 1) - u n)

namespace Finset

open BigOperators

variable {M : Type*} [OrderedAddCommMonoid M] {f : ℕ → M} {u : ℕ → ℕ}

theorem le_sum_schlomilch' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k in Ico (u 0) (u n), f k) ≤ ∑ k in range n, (u (k + 1) - u k) • f (u k) := by
  induction' n with n ihn
  · simp
  suffices (∑ k in Ico (u n) (u (n + 1)), f k) ≤ (u (n + 1) - u n) • f (u n) by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts [hu n.zero_le, hu n.le_succ]
  have : ∀ k ∈ Ico (u n) (u (n + 1)), f k ≤ f (u n) := fun k hk =>
    hf (Nat.succ_le_of_lt (h_pos n)) (mem_Ico.mp hk).1
  convert sum_le_sum this
  simp [pow_succ, mul_two]

theorem le_sum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) : (∑ k in range (u n), f k) ≤ ∑ k in range (u 0), f k +
    ∑ k in range n, (u (k + 1) - u k) • f (u k) := by
  convert add_le_add_left (le_sum_schlomilch' hf h_pos hu n) (∑ k in range (u 0), f k)
  rw [← sum_range_add_sum_Ico _ (hu n.zero_le)]

theorem sum_schlomilch_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) : (∑ k in range n, (u (k + 1) - u k) • f (u (k + 1))) ≤
    ∑ k in Ico (u 0 + 1) (u n + 1), f k := by
  induction' n with n ihn
  · simp
  suffices (u (n + 1) - u n) • f (u (n + 1)) ≤ ∑ k in Ico (u n + 1) (u (n + 1) + 1), f k by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exacts [add_le_add ihn this,
      (add_le_add_right (hu n.zero_le) _ : u 0 + 1 ≤ u n + 1),
      add_le_add_right (hu n.le_succ) _]
  have : ∀ k ∈ Ico (u n + 1) (u (n + 1) + 1), f (u (n + 1)) ≤ f k := fun k hk =>
    hf (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (h_pos n)) <| (Nat.lt_succ_of_le le_rfl).trans_le
      (mem_Ico.mp hk).1) (Nat.le_of_lt_succ <| (mem_Ico.mp hk).2)
  convert sum_le_sum this
  simp [pow_succ, mul_two]

theorem sum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) (n : ℕ) :
    ∑ k in range (n + 1), (u (k + 1) - u k) • f (u k) ≤
    (u 1 - u 0) • f (u 0) + C • ∑ k in Ico (u 0 + 1) (u n + 1), f k := by
  rw [sum_range_succ', add_comm]
  gcongr
  suffices ∑ k in range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
  C • ∑ k in range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : ∀ k ∈ range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
    C • ((u (k + 1) - u k) • f (u (k + 1))) := by
    intro k _
    rw [smul_smul]
    gcongr
    · exact h_nonneg (u (k + 1))
    exact mod_cast h_succ_diff k
  convert sum_le_sum this
  simp [smul_sum]
end Finset

namespace ENNReal

open Filter BigOperators Finset

variable {u : ℕ → ℕ} {f : ℕ → ℝ≥0∞}

open NNReal in
theorem le_tsum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) :
    ∑' k , f k ≤ ∑ k in range (u 0), f k + ∑' k : ℕ, (u (k + 1) - u k) * f (u k) := by
  have hu : Monotone u := by
    apply StrictMono.monotone hu_strict
  rw [ENNReal.tsum_eq_iSup_nat' (StrictMono.tendsto_atTop hu_strict)]
  refine iSup_le fun n => (Finset.le_sum_schlomilch hf h_pos hu n).trans (add_le_add_left ?_ _)
  have (k : ℕ) : ((u (k + 1) : ℝ≥0∞) - (u k : ℝ≥0∞) : ℝ≥0∞) = (u (k + 1) - (u k : ℕ) : ℕ) := by
    simp [NNReal.coe_sub (Nat.cast_le (α := ℝ≥0).mpr <| (hu_strict k.lt_succ_self).le)]
  simp only [nsmul_eq_mul, this]
  apply ENNReal.sum_le_tsum

theorem tsum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 <= f n) (hu_strict : StrictMono u) (h_succ_diff : SuccDiffBounded C u) :
    ∑' k : ℕ, (u (k + 1) - u k) * f (u k) ≤ (u 1 - u 0) * f (u 0) + C * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine
    iSup_le fun n =>
      le_trans ?_
        (add_le_add_left
          (mul_le_mul_of_nonneg_left (ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)) ?_) _)
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu_strict.monotone h_succ_diff n
  exact zero_le _
end ENNReal

namespace NNReal

open BigOperators Finset

open ENNReal in
/-- for a series of `NNReal` version. -/
theorem summable_schlomilch_iff {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ≥0}
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m)
    (h_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ≥0)) * f (u k)) ↔ Summable f := by
  simp only [← tsum_coe_ne_top_iff_summable, Ne.def, not_iff_not, ENNReal.coe_mul]
  constructor <;> intro h
  · replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    have h_nonneg : ∀ n, 0 ≤ (f n : ℝ≥0∞) := fun n =>
      ENNReal.coe_le_coe.2 (f n).2
    obtain hC := tsum_schlomilch_le hf h_pos h_nonneg hu_strict h_succ_diff
    have : (↑(u 1) - ↑(u 0)) * ↑(f (u 0)) + ↑C * ∑' (k : ℕ), ↑(f k) = ∞ := eq_top_mono hC h
    simpa [add_eq_top, mul_ne_top, mul_eq_top, hC_nonzero]
  · replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf hm hmn)
    have : ∑ k in range (u 0), ↑(f k) ≠ ∞ := ne_top_of_lt (sum_lt_top fun a _ => coe_ne_top)
    simpa [h, add_eq_top, this] using le_tsum_schlomilch hf h_pos hu_strict

open ENNReal in
theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ≥0) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_pos (n : ℕ) : 0 < 2 ^ n := pow_pos zero_lt_two n
  have hu_strict : StrictMono (2 ^ ·) := fun m n hm =>
      pow_lt_pow_right (Nat.lt_succ_self 1) hm
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  have hC_nonzero : 2 ≠ 0 := by norm_num
  convert summable_schlomilch_iff hf h_pos hu_strict hC_nonzero h_succ_diff
  simp [pow_succ, mul_two, two_mul]
end NNReal
#align nnreal.summable_condensed_iff NNReal.summable_condensed_iff

open NNReal in
/-- for series of nonnegative real numbers. -/
theorem summable_schlomilch_iff_of_nonneg {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ)) * f (u k)) ↔ Summable f := by
  lift f to ℕ → ℝ≥0
  exact h_nonneg
  simp only [NNReal.coe_le_coe] at *
  have (k : ℕ) : (u (k + 1) - (u k : ℝ)) = ((u (k + 1) : ℝ≥0) - (u k : ℝ≥0) : ℝ≥0) := by
    have := Nat.cast_le (α := ℝ≥0).mpr <| (hu_strict k.lt_succ_self).le
    simp [NNReal.coe_sub this]
  simp_rw [this]
  exact_mod_cast NNReal.summable_schlomilch_iff hf h_pos hu_strict hC_nonzero h_succ_diff

theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_pos (n : ℕ) : 0 < 2 ^ n := pow_pos zero_lt_two n
  have hu_strict : StrictMono (2 ^ ·) := fun m n hm =>
      pow_lt_pow_right (Nat.lt_succ_self 1) hm
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  have hC_nonzero : 2 ≠ 0 := by norm_num
  convert summable_schlomilch_iff_of_nonneg h_nonneg h_mono h_pos hu_strict hC_nonzero h_succ_diff
  simp [pow_succ, mul_two, two_mul]
#align summable_condensed_iff_of_nonneg summable_condensed_iff_of_nonneg

section p_series

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

namespace Real

open Filter BigOperators

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem summable_nat_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  rcases le_or_lt 0 p with hp | hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow, ← mul_pow,
        summable_geometric_iff_norm_lt_one]
      nth_rw 1 [← rpow_one 2]
      rw [← division_def, ← rpow_sub zero_lt_two, norm_eq_abs,
        abs_of_pos (rpow_pos_of_pos zero_lt_two _), rpow_lt_one_iff zero_lt_two.le]
      norm_num
    · intro n
      positivity
    · intro m n hm hmn
      gcongr
  -- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges.
  · suffices ¬Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) by
      have : ¬1 < p := fun hp₁ => hp.not_le (zero_le_one.trans hp₁.le)
      simpa only [this, iff_false]
    · intro h
      obtain ⟨k : ℕ, hk₁ : ((k : ℝ) ^ p)⁻¹ < 1, hk₀ : k ≠ 0⟩ :=
        ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
            (eventually_cofinite_ne 0)).exists
      apply hk₀
      rw [← pos_iff_ne_zero, ← @Nat.cast_pos ℝ] at hk₀
      simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
        hp.not_lt, hk₀] using hk₁
#align real.summable_nat_rpow_inv Real.summable_nat_rpow_inv

@[simp]
theorem summable_nat_rpow {p : ℝ} : Summable (fun n => (n : ℝ) ^ p : ℕ → ℝ) ↔ p < -1 := by
  rcases neg_surjective p with ⟨p, rfl⟩
  simp [rpow_neg]
#align real.summable_nat_rpow Real.summable_nat_rpow

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem summable_one_div_nat_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp
#align real.summable_one_div_nat_rpow Real.summable_one_div_nat_rpow

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
-- Porting note: temporarily remove `@[simp]` because of a problem with `simp`
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/looping.20in.20.60simp.60.20set/near/361134234
theorem summable_nat_pow_inv {p : ℕ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  simp only [← rpow_nat_cast, summable_nat_rpow_inv, Nat.one_lt_cast]
#align real.summable_nat_pow_inv Real.summable_nat_pow_inv

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem summable_one_div_nat_pow {p : ℕ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  -- porting note (#10745): was `simp`
  simp only [one_div, Real.summable_nat_pow_inv]
#align real.summable_one_div_nat_pow Real.summable_one_div_nat_pow

/-- Summability of the `p`-series over `ℤ`. -/
theorem summable_one_div_int_pow {p : ℕ} :
    (Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ p) ↔ 1 < p := by
  refine ⟨fun h ↦ summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective),
    fun h ↦ .of_nat_of_neg (summable_one_div_nat_pow.mpr h)
      (((summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1 : ℝ) ^ p).congr fun n ↦ ?_)⟩
  rw [Int.cast_neg, Int.cast_ofNat, neg_eq_neg_one_mul (n : ℝ), mul_pow, mul_one_div, div_div]
#align real.summable_one_div_int_pow Real.summable_one_div_int_pow

theorem summable_abs_int_rpow {b : ℝ} (hb : 1 < b) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (-b) := by
  apply Summable.of_nat_of_neg
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  all_goals
    simp_rw [Int.cast_ofNat, fun n : ℕ => abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))]
    rwa [summable_nat_rpow, neg_lt_neg_iff]
#align real.summable_abs_int_rpow Real.summable_abs_int_rpow

/-- Harmonic series is not unconditionally summable. -/
theorem not_summable_nat_cast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) := by
  have : ¬Summable (fun n => ((n : ℝ) ^ 1)⁻¹ : ℕ → ℝ) :=
    mt (summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa
#align real.not_summable_nat_cast_inv Real.not_summable_nat_cast_inv

/-- Harmonic series is not unconditionally summable. -/
theorem not_summable_one_div_nat_cast : ¬Summable (fun n => 1 / n : ℕ → ℝ) := by
  simpa only [inv_eq_one_div] using not_summable_nat_cast_inv
#align real.not_summable_one_div_nat_cast Real.not_summable_one_div_nat_cast

/-- **Divergence of the Harmonic Series** -/
theorem tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i in Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_nat_cast
  · exact fun i => by positivity
#align real.tendsto_sum_range_one_div_nat_succ_at_top Real.tendsto_sum_range_one_div_nat_succ_atTop

end Real

namespace NNReal

@[simp]
theorem summable_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ≥0) ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p := by
  simp [← NNReal.summable_coe]
#align nnreal.summable_rpow_inv NNReal.summable_rpow_inv

@[simp]
theorem summable_rpow {p : ℝ} : Summable (fun n => (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ p < -1 := by
  simp [← NNReal.summable_coe]
#align nnreal.summable_rpow NNReal.summable_rpow

theorem summable_one_div_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ 1 < p := by
  simp
#align nnreal.summable_one_div_rpow NNReal.summable_one_div_rpow

end NNReal

end p_series

section

open Finset BigOperators

variable {α : Type*} [LinearOrderedField α]

set_option tactic.skipAssignedInstances false in
theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (∑ i in Ioc k n, ((i : α) ^ 2)⁻¹) ≤ (k : α)⁻¹ - (n : α)⁻¹ := by
  refine' Nat.le_induction _ _ n h
  · simp only [Ioc_self, sum_empty, sub_self, le_refl]
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  apply (add_le_add IH le_rfl).trans
  simp only [sub_eq_add_neg, add_assoc, Nat.cast_add, Nat.cast_one, le_add_neg_iff_add_le,
    add_le_iff_nonpos_right, neg_add_le_iff_le_add, add_zero]
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  have B : 0 < (n : α) + 1 := by linarith
  field_simp
  rw [div_le_div_iff _ A, ← sub_nonneg]
  · ring_nf
    rw [add_comm]
    exact B.le
  · -- Porting note: was `nlinarith`
    positivity
#align sum_Ioc_inv_sq_le_sub sum_Ioc_inv_sq_le_sub

theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i in Ioo k n, (i ^ 2 : α)⁻¹) ≤ 2 / (k + 1) :=
  calc
    (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) ≤ ∑ i in Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true_iff, and_self_iff]
      · intro i _hi _hident
        positivity
    _ ≤ ((k + 1 : α) ^ 2)⁻¹ + ∑ i in Ioc k.succ (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      rw [← Nat.Icc_succ_left, ← Nat.Ico_succ_right, sum_eq_sum_Ico_succ_bot]
      swap; · exact Nat.succ_lt_succ ((Nat.lt_succ_self k).trans_le (le_max_left _ _))
      rw [Nat.Ico_succ_right, Nat.Icc_succ_left, Nat.cast_succ]
    _ ≤ ((k + 1 : α) ^ 2)⁻¹ + (k + 1 : α)⁻¹ := by
      refine' add_le_add le_rfl ((sum_Ioc_inv_sq_le_sub _ (le_max_left _ _)).trans _)
      · simp only [Ne.def, Nat.succ_ne_zero, not_false_iff]
      · simp only [Nat.cast_succ, one_div, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
    _ ≤ 1 / (k + 1) + 1 / (k + 1) := by
      have A : (1 : α) ≤ k + 1 := by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      simp_rw [← one_div]
      gcongr
      simpa using pow_le_pow_right A one_le_two
    _ = 2 / (k + 1) := by ring
#align sum_Ioo_inv_sq_le sum_Ioo_inv_sq_le

end

open Set Nat in
/-- The harmonic series restricted to a residue class is not summable. -/
lemma Real.not_summable_indicator_one_div_natCast {m : ℕ} (hm : m ≠ 0) (k : ZMod m) :
    ¬ Summable ({n : ℕ | (n : ZMod m) = k}.indicator fun n : ℕ ↦ (1 / n : ℝ)) := by
  have : NeZero m := ⟨hm⟩ -- instance is needed below
  rw [← summable_nat_add_iff 1] -- shift by one to avoid non-monotonicity at zero
  have h (n : ℕ) : {n : ℕ | (n : ZMod m) = k - 1}.indicator (fun n : ℕ ↦ (1 / (n + 1 :) : ℝ)) n =
      if (n : ZMod m) = k - 1 then (1 / (n + 1) : ℝ) else (0 : ℝ) := by
    simp only [indicator_apply, mem_setOf_eq, cast_add, cast_one]
  simp_rw [indicator_apply, mem_setOf, cast_add, cast_one, ← eq_sub_iff_add_eq, ← h]
  rw [summable_indicator_mod_iff (fun n₁ n₂ h ↦ by gcongr) (k - 1)]
  exact mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp not_summable_one_div_nat_cast

/-!
## Translating the `p`-series by a real number
-/
section shifted

open Filter Asymptotics Topology

lemma Real.summable_one_div_nat_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℕ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by
  suffices ∀ (b c : ℝ), Summable (fun n : ℕ ↦ 1 / |n + b| ^ s) →
      Summable (fun n : ℕ ↦ 1 / |n + c| ^ s) by
    simp_rw [← summable_one_div_nat_rpow, Iff.intro (this a 0) (this 0 a), add_zero, Nat.abs_cast]
  refine fun b c h ↦ summable_of_isBigO_nat h (isBigO_of_div_tendsto_nhds ?_ 1 ?_)
  · filter_upwards [eventually_gt_atTop (Nat.ceil |b|)] with n hn hx
    have hna : 0 < n + b := by linarith [lt_of_abs_lt ((abs_neg b).symm ▸ Nat.lt_of_ceil_lt hn)]
    exfalso
    revert hx
    positivity
  · simp_rw [Pi.div_def, div_div, mul_one_div, one_div_div]
    refine (?_ : Tendsto (fun x : ℝ ↦ |x + b| ^ s / |x + c| ^ s) atTop (𝓝 1)).comp
      tendsto_nat_cast_atTop_atTop
    have : Tendsto (fun x : ℝ ↦ 1 + (b - c) / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add ((tendsto_const_nhds (X := ℝ)).div_atTop tendsto_id)
    have : Tendsto (fun x ↦ (x + b) / (x + c)) atTop (𝓝 1) := by
      refine (this.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := c)))).congr' ?_
      filter_upwards [eventually_gt_atTop (-c)] with x hx
      field_simp [(by linarith : 0 < x + c).ne']
    apply (one_rpow s ▸ (continuousAt_rpow_const _ s (by simp)).tendsto.comp this).congr'
    filter_upwards [eventually_gt_atTop (-b), eventually_gt_atTop (-c)] with x hb hc
    rw [neg_lt_iff_pos_add] at hb hc
    rw [Function.comp_apply, div_rpow hb.le hc.le, abs_of_pos hb, abs_of_pos hc]

lemma Real.summable_one_div_int_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℤ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by
  simp_rw [summable_int_iff_summable_nat_and_neg, ← abs_neg (↑(-_ : ℤ) + a), neg_add,
    Int.cast_neg, neg_neg, Int.cast_ofNat, summable_one_div_nat_add_rpow, and_self]

end shifted
