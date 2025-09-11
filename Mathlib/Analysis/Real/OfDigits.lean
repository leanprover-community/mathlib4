/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.MoveAdd
import Mathlib.Tactic.Rify

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

namespace Real

/-- `ofDigits` takes a sequence of digits `(d₀, d₁, ...)` in base `b` and returns the
  real numnber `0.d₀d₁d₂... = ∑ᵢ(dᵢ/bⁱ)`. This auxiliary definition `ofDigitsTerm` sends the
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
  have hb : 0 < b := b_pos digits
  obtain rfl | hb := (Nat.one_le_of_lt hb).eq_or_lt
  · have : ofDigitsTerm digits = 0 := by
      ext i
      simp [ofDigitsTerm]
    simp only [this]
    exact summable_zero
  have h := summable_geometric_of_lt_one (r := (b⁻¹ : ℝ)) (by simp)
    (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  apply Summable.mul_left (a := (b : ℝ)) at h
  replace h : Summable fun i ↦ b * (b : ℝ)⁻¹ ^ (i + 1) := by
    simp_rw [pow_succ', ← mul_assoc, mul_comm (b : ℝ), mul_assoc, Summable.mul_left _ h]
  apply Summable.of_nonneg_of_le (fun _ ↦ ofDigitsTerm_nonneg) _ h
  intro i
  apply le_trans ofDigitsTerm_le
  gcongr
  · simp
  · rw [inv_pow]

/-- `ofDigits d` is the real number `0.d₀d₁d₂...` in base `b`.
We allow repeating representations like `0.999...` here. -/
noncomputable def ofDigits {b : ℕ} (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} (digits : ℕ → Fin b) : 0 ≤ ofDigits digits := by
  simp only [ofDigits]
  exact tsum_nonneg fun _ ↦ ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} (digits : ℕ → Fin b) : ofDigits digits ≤ 1 := by
  have hb : 0 < b := b_pos digits
  obtain rfl | hb' := (Nat.one_le_of_lt hb).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb'
  have hb_inv_nonneg : 0 ≤ (b⁻¹ : ℝ) := by simp
  have hb_inv_lt_one : (b⁻¹ : ℝ) < 1 := by bound
  simp only [ofDigits]
  let g (i : ℕ) : ℝ := (1 - (b⁻¹ : ℝ)) * (b⁻¹ : ℝ) ^ i
  have hg_summable : Summable g :=
    (summable_geometric_of_lt_one (by simp) (inv_lt_one_of_one_lt₀ hb')).mul_left _
  convert Summable.tsum_mono (summable_ofDigitsTerm) hg_summable _
  · simp only [tsum_mul_left, g]
    rw [tsum_geometric_of_lt_one hb_inv_nonneg hb_inv_lt_one, mul_inv_cancel₀ (by linarith)]
  · intro i
    simp only [inv_pow, g]
    convert ofDigitsTerm_le using 1
    field_simp
    ring

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
  have : ∑ i ∈ Finset.range n, ofDigitsTerm x i = ∑ i ∈ Finset.range n, ofDigitsTerm y i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [ofDigitsTerm, hxy i hi]
  simp only [this, add_sub_add_left_eq_sub, ge_iff_le]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  rw [abs_le']
  constructor <;> linarith [ofDigits_nonneg (fun i ↦ x (i + n)),
    ofDigits_nonneg (fun i ↦ y (i + n)), ofDigits_le_one (fun i ↦ x (i + n)),
    ofDigits_le_one (fun i ↦ y (i + n))]

/-- Converts a real number `x` from the interval `[0, 1)` into sequence of
its digits in base `b`. -/
noncomputable def digits (x : ℝ) (b : ℕ) [NeZero b] : ℕ → Fin b :=
  fun i ↦ Fin.ofNat _ <| ⌊x * b ^ (i + 1)⌋₊

theorem ofDigits_digits_sum_eq {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b)
    (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
    b ^ n * ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i = ⌊b ^ n * x⌋₊ := by
  induction n with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, one_mul]
    rw [Set.mem_Ico] at hx
    norm_cast
    symm
    rw [Nat.floor_eq_zero]
    exact hx.right
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ', mul_assoc, ih]
    simp only [ofDigitsTerm, digits]
    rw [show x * (b : ℝ) ^ (n + 1) = b * (b ^ n * x) by ring]
    conv => rhs; rw [mul_assoc]
    set y := (b : ℝ) ^ n * x
    ring_nf
    move_mul [← (b : ℝ)⁻¹]
    have hb_zero : (b : ℝ) ≠ 0 := by
      simpa using NeZero.ne b
    simp only [inv_mul_cancel₀ hb_zero, one_mul, Fin.ofNat_eq_cast, Fin.val_natCast, inv_pow]
    move_mul [← ((b : ℝ) ^ n)⁻¹]
    rw [inv_mul_cancel₀ (by positivity), one_mul]
    norm_cast
    rw [← Nat.cast_mul_floor_div_cancel (a := y) (show b ≠ 0 by omega), Nat.mod_add_div]

theorem sum_ofDigitsTerm_digits_ge {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b)
    (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
    x - (b⁻¹ : ℝ) ^ n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i := by
  have := ofDigits_digits_sum_eq hb hx n
  have h_le := Nat.lt_floor_add_one (b ^ n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_iff_right₀ (show 0 < (b : ℝ) ^ n by positivity),
    mul_sub, inv_pow, mul_inv_cancel₀ (by positivity)]
  linarith

theorem sum_ofDigitsTerm_digits_le {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) {n : ℕ}
    (hx : x ∈ Set.Ico 0 1) :
    ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i ≤ x := by
  have := ofDigits_digits_sum_eq hb hx n
  have h_le := Nat.floor_le (a := b ^ n * x) (by have := hx.left; positivity)
  rw [← this, mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

theorem hasSum_ofDigitsTerm_digits (x : ℝ) {b : ℕ} [NeZero b] (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    HasSum (ofDigitsTerm (digits x b)) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; rw [norm_eq_abs, abs_of_nonneg (by simp [ofDigitsTerm]; positivity)]
    exact summable_ofDigitsTerm
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ -(b⁻¹ : ℝ) ^ n) (h := 0)
  · rw [show (0 : ℝ) = -0 by simp]
    apply Filter.Tendsto.neg
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_of_nonneg (by positivity)]
    rify at hb
    exact inv_lt_one_of_one_lt₀ hb
  · apply tendsto_const_nhds
  · intro n
    simp only [inv_pow, neg_le_sub_iff_le_add]
    have := sum_ofDigitsTerm_digits_ge hb hx n
    simp only [inv_pow, tsub_le_iff_right] at this
    linarith
  · intro n
    simp [sum_ofDigitsTerm_digits_le hb hx]

theorem ofDigits_digits {b : ℕ} [NeZero b] {x : ℝ} (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    ofDigits (digits x b) = x := by
  simp only [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact hasSum_ofDigitsTerm_digits x hb hx
  · exact summable_ofDigitsTerm

end Real
