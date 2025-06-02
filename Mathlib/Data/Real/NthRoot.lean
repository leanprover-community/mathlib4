import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# nth root operations

This file provides `Real.nthRoot n` to compute `ⁿ√`,
which operates as expected on negative values when `n` is odd.
The trap this avoids is that using `rpow`, `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.

-/

noncomputable section

namespace Real

def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)

theorem nthRoot_of_even {n : ℕ} (hn : Even n) (r : ℝ) : nthRoot n r = r ^ (n⁻¹ : ℝ) :=
  if_pos hn

theorem nthRoot_of_odd {n : ℕ} (hn : Odd n) (r : ℝ) :
    nthRoot n r = SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ) :=
  if_neg <| Nat.not_even_iff_odd.mpr hn

theorem nthRoot_of_odd_of_nonpos {n : ℕ} (hn : Odd n) {r : ℝ} (hr : r ≤ 0) :
    nthRoot n r = (-1) ^ n * (-r) ^ (n⁻¹ : ℝ) := by
  rw [nthRoot_of_odd hn]
  obtain rfl | hr := hr.eq_or_lt
  · simp
    have hn0 : n ≠ 0 := Nat.ne_of_odd_add hn
    rw [zero_pow hn0, zero_rpow (inv_ne_zero <| mod_cast hn0)]
    right
    rfl
  · rw [abs_of_neg hr, _root_.sign_neg hr]
    simp

theorem nthRoot_of_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    nthRoot n r = r ^ (n⁻¹ : ℝ) := by
  cases Nat.even_or_odd n with
  | inl he =>
    rw [nthRoot_of_even he]
  | inr ho =>
    have hn0 : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, abs_of_nonneg hr]
    obtain rfl | hr := hr.eq_or_lt
    · simp [hn0]
    rw [_root_.sign_pos hr]
    simp

@[simp]
theorem nthRoot_neg_of_odd {n : ℕ} (hn : Odd n) {r : ℝ} :
    nthRoot n (-r) = -nthRoot n r := by
  obtain hr | hr := le_total r 0
  · rw [nthRoot_of_odd_of_nonpos hn hr, hn.neg_one_pow, neg_one_mul, neg_neg,
      nthRoot_of_nonneg (neg_nonneg.mpr hr)]
  · rw [nthRoot_of_odd_of_nonpos hn (neg_nonpos.mpr hr), hn.neg_one_pow, neg_one_mul, neg_neg,
      nthRoot_of_nonneg hr]

theorem pow_nthRoot {n : ℕ} (r : ℝ) (h : (n ≠ 0 ∧ 0 ≤ r) ∨ Odd n) : nthRoot n r ^ n = r := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [nthRoot_of_even he, rpow_inv_natCast_pow hr hn]
  | inr ho =>
    have hn : n ≠ 0 := by exact Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, mul_pow, ←pow_mul, rpow_inv_natCast_pow (abs_nonneg _) hn,
      ←SignType.coe_pow, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

theorem nthRoot_pow {n : ℕ} (r : ℝ) (h : (n ≠ 0 ∧ 0 ≤ r) ∨ Odd n) : nthRoot n (r ^ n) = r := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [nthRoot_of_even he, pow_rpow_inv_natCast hr hn]
  | inr ho =>
    have hn : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, abs_pow, pow_rpow_inv_natCast (abs_nonneg _) hn,
      ←SignType.coe_pow, sign_pow, ← pow_mul, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

theorem nthRoot_mul_of_even_of_nonneg {n : ℕ} {a b : ℝ} (hn : Even n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.nthRoot n (a * b) = Real.nthRoot n a * Real.nthRoot n b := by
  simp only [Real.nthRoot_of_even hn, Real.mul_rpow ha hb]

theorem nthRoot_mul_of_odd {n : ℕ} {a b : ℝ} (hn : Odd n) :
    Real.nthRoot n (a * b) = Real.nthRoot n a * Real.nthRoot n b := by
  simp only [Real.nthRoot_of_odd hn, sign_mul, SignType.coe_mul, abs_mul,
    Real.mul_rpow (Real.nnabs.proof_1 a) (Real.nnabs.proof_1 b)]
  ring

end Real
