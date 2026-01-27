/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# Representation of reals in positional system

This file defines `Real.ofDigits` and `Real.digits` functions which allows to work with the
representations of reals as sequences of digits in positional system.

## Main Definitions

* `ofDigits`: takes a sequence of digits `(d₀, d₁, ...)` (as an `ℕ → Fin b`),
  and returns the real number `0.d₀d₁d₂...`.
* `digits`: takes a real number in [0,1) and returns the sequence of its digits.

## Main Statements

* `ofDigits_digits` states that `ofDigits (digits x b) = x`.
-/

@[expose] public section

namespace Real

/-- `ofDigits` takes a sequence of digits `(d₀, d₁, ...)` in base `b` and returns the
  real number `0.d₀d₁d₂... = ∑ᵢ(dᵢ/bⁱ)`. This auxiliary definition `ofDigitsTerm` sends the
  sequence to the function sending `i` to `dᵢ/bⁱ`. -/
noncomputable def ofDigitsTerm {b : ℕ} (digits : ℕ → Fin b) : ℕ → ℝ :=
  fun i ↦ (digits i) * ((b : ℝ) ^ (i + 1))⁻¹

theorem ofDigitsTerm_nonneg {b : ℕ} {digits : ℕ → Fin b} {n : ℕ} :
    0 ≤ ofDigitsTerm digits n := by
  simp only [ofDigitsTerm]
  positivity

private lemma b_pos {b : ℕ} (digits : ℕ → Fin b) : 0 < b := Fin.pos (digits 0)

theorem ofDigitsTerm_le {b : ℕ} {digits : ℕ → Fin b} {n : ℕ} :
    ofDigitsTerm digits n ≤ (b - 1) * ((b : ℝ) ^ (n + 1))⁻¹ := by
  obtain ⟨c, rfl⟩ := Nat.exists_add_one_eq.mpr (b_pos digits)
  unfold ofDigitsTerm
  gcongr
  simp
  grind

theorem summable_ofDigitsTerm {b : ℕ} {digits : ℕ → Fin b} :
    Summable (ofDigitsTerm digits) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ ofDigitsTerm_nonneg) (fun _ ↦ ofDigitsTerm_le) ?_
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simpa using summable_zero
  simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  simp [inv_lt_one_iff₀, hb]

/-- `ofDigits d` is the real number `0.d₀d₁d₂...` in base `b`.
We allow repeating representations like `0.999...` here. -/
noncomputable def ofDigits {b : ℕ} (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} (digits : ℕ → Fin b) : 0 ≤ ofDigits digits := by
  simp only [ofDigits]
  exact tsum_nonneg fun _ ↦ ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} (digits : ℕ → Fin b) : ofDigits digits ≤ 1 := by
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb
  convert Summable.tsum_mono summable_ofDigitsTerm _ (fun _ ↦ ofDigitsTerm_le)
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, hb])]
    have := sub_pos.mpr hb
    field
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
    simp [inv_lt_one_iff₀, hb]

theorem ofDigits_eq_sum_add_ofDigits {b : ℕ} (a : ℕ → Fin b) (n : ℕ) :
    ofDigits a = (∑ i ∈ Finset.range n, ofDigitsTerm a i) +
      ((b : ℝ) ^ n)⁻¹ * ofDigits (fun i ↦ a (i + n)) := by
  simp only [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n summable_ofDigitsTerm,
    ← Summable.tsum_mul_left _ summable_ofDigitsTerm]
  congr
  ext i
  simp only [ofDigitsTerm]
  ring

theorem abs_ofDigits_sub_ofDigits_le {b : ℕ} {x y : ℕ → Fin b} {n : ℕ}
    (hxy : ∀ i < n, x i = y i) :
    |ofDigits x - ofDigits y| ≤ ((b : ℝ) ^ n)⁻¹ := by
  rw [ofDigits_eq_sum_add_ofDigits x n, ofDigits_eq_sum_add_ofDigits y n]
  have : ∑ i ∈ Finset.range n, ofDigitsTerm x i = ∑ i ∈ Finset.range n, ofDigitsTerm y i :=
    Finset.sum_congr rfl fun i hi ↦ by simp [ofDigitsTerm, hxy i (Finset.mem_range.mp hi)]
  rw [this, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  convert abs_sub_le_of_le_of_le (ofDigits_nonneg _) (ofDigits_le_one _)
    (ofDigits_nonneg _) (ofDigits_le_one _)
  simp

/-- Converts a real number `x` from the interval `[0, 1)` into sequence of
its digits in base `b`. -/
noncomputable def digits (x : ℝ) (b : ℕ) [NeZero b] : ℕ → Fin b :=
  fun i ↦ Fin.ofNat _ <| ⌊x * b ^ (i + 1)⌋₊

theorem ofDigits_digits_sum_eq {x : ℝ} {b : ℕ} [NeZero b] (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
    b ^ n * ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i = ⌊b ^ n * x⌋₊ := by
  have := NeZero.ne b
  induction n with
  | zero => simp [Nat.floor_eq_zero.mpr hx.right]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ', mul_assoc, ih, ofDigitsTerm, digits, ← pow_succ',
      mul_left_comm, mul_inv_cancel₀ (by positivity), mul_one, mul_comm x, pow_succ', mul_assoc]
    set y := (b : ℝ) ^ n * x
    norm_cast
    rw [← Nat.cast_mul_floor_div_cancel (a := y) (show b ≠ 0 by lia),
      Fin.val_ofNat, Nat.div_add_mod]

theorem le_sum_ofDigitsTerm_digits {x : ℝ} {b : ℕ} [NeZero b]
    (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
    x - (b⁻¹ : ℝ) ^ n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i := by
  have := NeZero.pos b
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.lt_floor_add_one (b ^ n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_iff_right₀ (show 0 < (b : ℝ) ^ n by positivity),
    mul_sub, inv_pow, mul_inv_cancel₀ (by positivity)]
  linarith

theorem sum_ofDigitsTerm_digits_le {x : ℝ} {b : ℕ} [NeZero b]
    (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i ≤ x := by
  have := ofDigits_digits_sum_eq (b := b) hx n
  have h_le := Nat.floor_le (a := b ^ n * x) (by have := hx.left; positivity)
  have hb := NeZero.ne b
  rw [← this, mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

theorem hasSum_ofDigitsTerm_digits (x : ℝ) {b : ℕ} [NeZero b] (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    HasSum (ofDigitsTerm (digits x b)) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm (by exact summable_ofDigitsTerm.abs)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (le_sum_ofDigitsTerm_digits hx) (sum_ofDigitsTerm_digits_le hx)
  convert tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one _)
  · simp
  · simp [abs_of_nonneg, inv_lt_one_iff₀, hb]

theorem ofDigits_digits {b : ℕ} [NeZero b] {x : ℝ} (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    ofDigits (digits x b) = x := by
  simp only [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact hasSum_ofDigitsTerm_digits x hb hx
  · exact summable_ofDigitsTerm

/-- A generalization of the identity `0.(9) = 1` to arbitrary positional numeral systems. -/
theorem ofDigits_const_last_eq_one (b : ℕ) [NeZero b] :
    ofDigits (fun _ ↦ Fin.last b) = 1 := by
  have : 1 < |(b + 1 : ℝ)| := by
    rw [← Nat.cast_add_one, abs_of_nonneg (Nat.cast_nonneg _)]
    simp [NeZero.pos b]
  simp only [ofDigits, ofDigitsTerm, ← inv_pow]
  rw [Summable.tsum_mul_left]
  · rw [geom_series_succ _ (by simp [inv_lt_one_iff₀, this]),
      tsum_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, NeZero.pos b])]
    push_cast
    have : (b : ℝ) ≠ 0 := mod_cast NeZero.ne b
    field [*]
  · rw [summable_nat_add_iff (f := fun n ↦ ((b + 1 : ℕ) : ℝ)⁻¹ ^ n) 1]
    apply summable_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, NeZero.pos b])

/-- A generalization of the identity `0.(9) = 1` to arbitrary positional numeral systems. -/
theorem ofDigits_const_last_eq_one' {b : ℕ} (hb : 1 < b) :
    ofDigits (fun _ ↦ (⟨b - 1, Nat.sub_one_lt_of_lt hb⟩ : Fin b)) = 1 := by
  convert ofDigits_const_last_eq_one (b - 1)
  · grind
  · constructor
    grind

theorem ofDigits_SurjOn {b : ℕ} (hb : 1 < b) :
    Set.SurjOn (ofDigits (b := b)) Set.univ (Set.Icc 0 1) := by
  have : NeZero b := ⟨by grind⟩
  intro y hy
  by_cases hy' : y ∈ Set.Ico 0 1
  · use digits y b
    simp [ofDigits_digits hb hy']
  · simp only [Set.image_univ, show y = 1 by grind, Set.mem_range]
    exact ⟨_, ofDigits_const_last_eq_one' hb⟩

theorem continuous_ofDigits {b : ℕ} : Continuous (@ofDigits b) := by
  match b with
  | 0 => fun_prop
  | 1 => fun_prop
  | n + 2 =>
    obtain ⟨hb0, hb⟩ : 0 < n + 2 ∧ 1 < n + 2 := by grind
    generalize n + 2 = b at hb
    rify at hb0 hb
    refine continuous_tsum (u := fun i ↦ (b : ℝ)⁻¹ ^ i) ?_ ?_ fun n x ↦ ?_
    · simp only [ofDigitsTerm]
      fun_prop
    · exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb)
    · simp only [norm_eq_abs, abs_of_nonneg ofDigitsTerm_nonneg, inv_pow]
      apply ofDigitsTerm_le.trans
      calc
        _ ≤ b * ((b : ℝ) ^ (n + 1))⁻¹ := by
          gcongr
          linarith
        _ = _ := by
          grind

end Real
