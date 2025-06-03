import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# nth root operations

This file provides `Real.nthRoot n` to compute `ⁿ√`,
which operates as expected on negative values when `n` is odd.
The trap this avoids is that using `rpow`, `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.

-/

noncomputable section

namespace Real

section qpow

instance instQPow : Pow ℝ ℚ where
  pow r q :=
    if Even q.den then r ^ (q : ℝ) else SignType.sign r ^ (q.den * q.num) * abs r ^ (q : ℝ)

theorem qpow_of_even (r : ℝ) {q : ℚ} (hn : Even q.den) : r ^ q = r ^ (q : ℝ) :=
  if_pos hn

theorem qpow_of_den_eq_one (r : ℝ) {q : ℚ} (hq : q.den = 1) : r ^ q = r ^ q.num := by
  refine if_neg (by simp [hq]) |>.trans ?_
  rw [hq, Nat.cast_one, one_mul]
  conv_lhs => enter [2]; rw [← Rat.coe_int_num_of_den_eq_one hq, Rat.cast_intCast, rpow_intCast]
  rw [← mul_zpow, sign_mul_abs]

theorem qpow_of_odd (r : ℝ) {q : ℚ} (hn : Odd q.den) :
    r ^ q = SignType.sign r ^ (q.den * q.num) * abs r ^ (q : ℝ) :=
  if_neg <| Nat.not_even_iff_odd.mpr hn

@[simp, norm_cast]
theorem qpow_intCast (r : ℝ) (z : ℤ) : r ^ (z : ℚ) = r ^ z :=
  qpow_of_den_eq_one _ <| Rat.den_intCast _

@[simp, norm_cast]
theorem qpow_natCast (r : ℝ) (n : ℕ) : r ^ (n : ℚ) = r ^ n :=
  qpow_intCast _ _

@[simp]
theorem qpow_ofNat (r : ℝ) (n : ℕ) : r ^ (ofNat(n) : ℚ) = r ^ ofNat(n) :=
  qpow_natCast _ _

theorem qpow_zero (r : ℝ) : r ^ (0 : ℚ) = 1 := by
  rw [qpow_ofNat, pow_zero]

theorem qpow_one (r : ℝ) : r ^ (1 : ℚ) = r := by
  rw [qpow_ofNat, pow_one]

theorem qpow_of_odd_of_nonpos {q : ℚ} (hn : Odd q.den) {r : ℝ} (hr : r ≤ 0) :
    r ^ q = (-1) ^ (q.den * q.num) * (-r) ^ (q : ℝ) := by
  rw [qpow_of_odd _ hn]
  obtain rfl | hr := hr.eq_or_lt
  · simp
    obtain rfl | hq := eq_or_ne q 0
    · simp
    have hn0 : q ≠ 0 := sorry
    rw [zero_rpow (mod_cast hn0)]
  · rw [abs_of_neg hr, _root_.sign_neg hr]
    simp

theorem qpow_of_nonneg {q : ℚ} {r : ℝ} (hr : 0 ≤ r) :
    r ^ q = r ^ (q : ℝ) := by
  cases Nat.even_or_odd q.den with
  | inl he =>
    rw [qpow_of_even he]
  | inr ho =>
    obtain rfl | hq := eq_or_ne q 0
    · simp_rw [qpow_of_odd ho, Rat.den_ofNat, pow_one, Rat.cast_zero, rpow_zero, mul_one,
        SignType.cast_eq]
    have hn0 : q.den ≠ 0 := Nat.ne_of_odd_add ho
    rw [qpow_of_odd ho, abs_of_nonneg hr]
    obtain rfl | hr := hr.eq_or_lt
    · simp [qpow_of_odd ho]
      rw [zero_rpow]
    rw [_root_.sign_pos hr]
    simp

@[simp]
theorem qpow_neg_of_odd {q : ℚ} (hn : Odd q.den) {r : ℝ} :
    (-r) ^ q = -r ^ q := by
  obtain hr | hr := le_total r 0
  · rw [qpow_of_odd_of_nonpos hn hr, hn.neg_one_pow, neg_one_mul, neg_neg,
      qpow_of_nonneg (neg_nonneg.mpr hr)]
  · rw [qpow_of_odd_of_nonpos hn (neg_nonpos.mpr hr), hn.neg_one_pow, neg_one_mul, neg_neg,
      qpow_of_nonneg hr]

theorem qpow_inv_qpow {q : ℚ} (r : ℝ) (h : (q.den ≠ 0 ∧ 0 ≤ r) ∨ Odd q.den) : (r ^ q⁻¹) ^ q = r := by
  cases Nat.even_or_odd q.den with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [qpow_of_even he, rpow_inv_natCast_pow hr hn]
  | inr ho =>
    have hn : n ≠ 0 := by exact Nat.ne_of_odd_add ho
    rw [qpow_of_odd ho, mul_pow, ←pow_mul, rpow_inv_natCast_pow (abs_nonneg _) hn,
      ←SignType.coe_pow, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

theorem qpow_pow {q : ℚ} (r : ℝ) (h : (n ≠ 0 ∧ 0 ≤ r) ∨ Odd n) : qpow n (r ^ n) = r := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [qpow_of_even he, pow_rpow_inv_natCast hr hn]
  | inr ho =>
    have hn : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [qpow_of_odd ho, abs_pow, pow_rpow_inv_natCast (abs_nonneg _) hn,
      ←SignType.coe_pow, sign_pow, ← pow_mul, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho

theorem qpow_mul_of_even_of_nonneg {q : ℚ} {a b : ℝ} (hn : Even q.den) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ q = a ^ q * b ^ q := by
  simp only [Real.qpow_of_even hn, Real.mul_rpow ha hb]

theorem qpow_mul_of_odd {q : ℚ} {a b : ℝ} (hn : Odd q.den) :
    (a * b) ^ q = a ^ q * b ^ q := by
  simp only [Real.qpow_of_odd hn, sign_mul, SignType.coe_mul, abs_mul,
    Real.mul_rpow (Real.nnabs.proof_1 a) (Real.nnabs.proof_1 b)]
  ring


end qpow

abbrev nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (n⁻¹ : ℚ)

theorem nthRoot_of_even {n : ℕ} (hn : Even n) (r : ℝ) : r ^ q = r ^ (n⁻¹ : ℝ) :=
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
