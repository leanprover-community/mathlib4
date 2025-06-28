import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Field.Power

/-!
# nth root operations

This file provides `nthRoot n` to compute `ⁿ√`,
which operates as expected on negative values when `n` is odd.
The trap this avoids is that using `rpow`, `(-8 : ℝ) ^ (1/3 : ℝ) = 1`.

-/

noncomputable section

theorem Rat.den_inv_of_ne_zero (q : ℚ) (hq : q ≠ 0) : (q⁻¹).den = q.num.natAbs := by
  have hq' : q.num ≠ 0 := by simpa using hq
  rw [Rat.inv_def', Rat.divInt_eq_div, div_eq_mul_inv, Rat.mul_den, Rat.inv_intCast_den, if_neg hq']
  norm_cast
  rw [one_mul, inv_intCast_num, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hq', mul_one,
    Int.natAbs_cast, q.reduced.symm, Nat.div_one]

theorem Rat.num_inv (q : ℚ) : (q⁻¹).num = q.num.sign * q.den := by
  rw [Rat.inv_def', Rat.divInt_eq_div, div_eq_mul_inv, Rat.mul_num, Rat.inv_intCast_num]
  norm_cast
  rw [one_mul, inv_intCast_den, Int.natAbs_mul, Int.natAbs_cast]
  split <;> simp_all [Int.natAbs_sign_of_ne_zero, q.reduced.symm, mul_comm]


namespace Real

section qpow

instance instQPow : Pow ℝ ℚ where
  pow r q :=
    if Even q.den then r ^ (q : ℝ) else SignType.sign r ^ q.num * abs r ^ (q : ℝ)

theorem qpow_eq_of_even_den (r : ℝ) {q : ℚ} (hn : Even q.den) : r ^ q = r ^ (q : ℝ) :=
  if_pos hn

theorem qpow_eq_of_odd_den (r : ℝ) {q : ℚ} (hn : Odd q.den) :
    r ^ q = SignType.sign r ^ q.num * abs r ^ (q : ℝ) :=
  if_neg <| Nat.not_even_iff_odd.mpr hn

#eval (-1)^5

theorem qpow_eq_of_den_eq_one (r : ℝ) {q : ℚ} (hq : q.den = 1) : r ^ q = r ^ q.num := by
  rw [qpow_eq_of_odd_den _ (by simp [hq])]
  conv_lhs => enter [2]; rw [← Rat.coe_int_num_of_den_eq_one hq, Rat.cast_intCast, rpow_intCast]
  rw [← mul_zpow, sign_mul_abs]

theorem qpow_eq_rpow_iff {r : ℝ} {q : ℚ} :
    r ^ q = r ^ (q : ℝ) ↔ 0 ≤ r ∨ Even q.den ∨ q.den = 1 := by
  obtain he | ho := Nat.even_or_odd q.den
  · simp [qpow_eq_of_even_den _ he, he]
  simp_rw [Nat.not_even_iff_odd.2 ho, false_or]
  rw [qpow_eq_of_odd_den _ ho]
  obtain rfl | hq := eq_or_ne q 0
  · simp
  have hn0 : q.den ≠ 0 := Nat.ne_of_odd_add ho
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp only [_root_.sign_neg hr, abs_of_neg hr, SignType.coe_neg, SignType.coe_one, hr.not_le,
      false_or]
    rw [Real.rpow_def_of_neg hr, rpow_def_of_pos (neg_pos.2 hr), log_neg_eq_log, mul_comm,
      mul_right_inj' (Real.exp_ne_zero _), eq_comm]
    obtain he | ho := Int.even_or_odd q.num
    · rw [he.neg_one_zpow, cos_eq_one_iff]
      sorry
    · rw [ho.neg_one_zpow, cos_eq_neg_one_iff]
      sorry
  · simp [hq, qpow_eq_of_odd_den _ ho]
  · rw [_root_.sign_pos hr, abs_of_pos hr, SignType.coe_one, one_zpow, one_mul]
    simp_rw [hr.le, true_or]

@[simp, norm_cast]
theorem qpow_intCast (r : ℝ) (z : ℤ) : r ^ (z : ℚ) = r ^ z :=
  qpow_eq_of_den_eq_one _ <| Rat.den_intCast _

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

theorem qpow_eq_of_nonneg {q : ℚ} {r : ℝ} (hr : 0 ≤ r) : r ^ q = r ^ (q : ℝ) :=
  qpow_eq_rpow_iff.2 <| .inl hr

@[simp]
theorem one_qpow (q : ℚ) : (1 : ℝ) ^ q = 1 := by
  simp [qpow_eq_of_nonneg <| zero_le_one]

@[simp]
theorem zero_qpow {q : ℚ} (hq : q ≠ 0) : (0 : ℝ) ^ q = 0 := by
  simp [qpow_eq_of_nonneg le_rfl, hq]

theorem qpow_eq_of_odd_of_nonpos {q : ℚ} (hn : Odd q.den) {r : ℝ} (hr : r ≤ 0) :
    r ^ q = (-1) ^ q.num * (-r) ^ (q : ℝ) := by
  rw [qpow_eq_of_odd_den _ hn]
  obtain rfl | hr := hr.eq_or_lt
  · obtain rfl | hq := eq_or_ne q 0
    · simp
    simp
    right
    simp [hq, zero_rpow]
  · rw [abs_of_neg hr, _root_.sign_neg hr]
    simp [zpow_mul', hn.neg_one_pow]

@[simp]
theorem qpow_neg_of_odd {q : ℚ} (hn : Odd q.num) (hn' : Odd q.den) {r : ℝ} :
    (-r) ^ q = -r ^ q := by
  obtain hr | hr := le_total r 0
  · rw [qpow_eq_of_odd_of_nonpos hn' hr, hn.neg_one_zpow, neg_one_mul, neg_neg,
      qpow_eq_of_nonneg (neg_nonneg.mpr hr)]
  · rw [qpow_eq_of_odd_of_nonpos hn' (neg_nonpos.mpr hr), hn.neg_one_zpow, neg_one_mul, neg_neg,
      qpow_eq_of_nonneg hr]

@[simp]
theorem neg_qpow_eq_of_even_of_odd {q : ℚ} (hn : Even q.num) (hn' : Odd q.den) {r : ℝ} :
    (-r) ^ q = r ^ q := by
  obtain hr | hr := le_total r 0
  · rw [qpow_eq_of_odd_of_nonpos hn' hr, hn.neg_one_zpow, one_mul,
      qpow_eq_of_nonneg (neg_nonneg.mpr hr)]
  · rw [qpow_eq_of_odd_of_nonpos hn' (neg_nonpos.mpr hr), hn.neg_one_zpow, neg_neg,
      qpow_eq_of_nonneg hr, one_mul]

theorem qpow_inv_qpow {q : ℚ} (r : ℝ) (hq : q ≠ 0) (h : 0 ≤ r ∨ Odd q.den) : (r ^ q⁻¹) ^ q = r := by
  obtain he | ho := Nat.even_or_odd q.den
  · obtain hr := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [qpow_eq_of_even_den _ he, qpow_eq_of_nonneg hr, Rat.cast_inv, rpow_inv_rpow hr]
    assumption_mod_cast
  · rw [qpow_eq_of_odd_den _ ho]
    obtain he | ho := Int.even_or_odd q.num
    · by_cases hr : r = 0
      · rw [hr, zero_qpow]
        · simp [hr, zero_qpow hq]
          rw [zero_rpow]
          · simp
          · assumption_mod_cast
        simpa
      · rw [← SignType.coe_zpow, SignType.zpow_even, SignType.coe_one, one_mul]
        · sorry
        · sorry
        · rw [sign_ne_zero]
          sorry
    rw [←SignType.coe_zpow, SignType.zpow_odd _ _ ho]
    sorry

theorem qpow_mul_of_even_of_nonneg {q : ℚ} {a b : ℝ} (hn : Even q.den) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ q = a ^ q * b ^ q := by
  simp only [Real.qpow_eq_of_even_den _ hn, Real.mul_rpow ha hb]

theorem qpow_mul_of_odd {q : ℚ} {a b : ℝ} (hn : Odd q.den) :
    (a * b) ^ q = a ^ q * b ^ q := by
  simp only [Real.qpow_eq_of_odd_den _ hn, sign_mul, SignType.coe_mul, abs_mul,
    Real.mul_rpow (abs_nonneg a) (abs_nonneg b)]
  rw [mul_mul_mul_comm, mul_zpow]

theorem qpow_qpow_inv {q : ℚ} (r : ℝ) (h : (q.den ≠ 0 ∧ 0 ≤ r) ∨ Odd q.den) :
    (r ^ q) ^ q⁻¹ = r := by
  obtain he | ho := Nat.even_or_odd q.den
  · obtain ⟨hn, hr⟩ := h.resolve_right (Nat.not_odd_iff_even.mpr he)
    rw [qpow_eq_of_even_den _ he, qpow_eq_of_even_den]
    · sorry
    · sorry -- rw [Rat.den_inv_of_ne_zero]
  · have hn : q.den ≠ 0 := Nat.ne_of_odd_add ho
    sorry
    /-
    rw [qpow_eq_of_odd_den _ ho, qpow_mul_of_odd, abs_pow, pow_rpow_inv_natCast (abs_nonneg _) hn,
      ←SignType.coe_pow, sign_pow, ← pow_mul, SignType.pow_odd, sign_mul_abs]
    exact ho.mul ho -/


end qpow

abbrev nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (n⁻¹ : ℚ)

theorem nthRoot_of_even {n : ℕ} (hn : Even n) (r : ℝ) : nthRoot n r = r ^ (n⁻¹ : ℝ) := by
  obtain rfl | hn' := eq_or_ne n 0
  · simp [nthRoot]
  · exact (qpow_eq_of_even_den _ (by simp [hn', hn])).trans (by simp)

theorem nthRoot_of_odd {n : ℕ} (hn : Odd n) (r : ℝ) :
    nthRoot n r = SignType.sign r ^ n * |r| ^ (n⁻¹ : ℝ) := by
  rw [nthRoot, qpow_eq_of_odd_den _ (by aesop)]
  cases n
  · simp
  rw [Rat.inv_natCast_num_of_pos (Nat.succ_pos _)]
  simp [Rat.inv_natCast_num_of_pos, ← SignType.coe_pow, SignType.pow_odd _ _ hn]

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
    nthRoot n (a * b) = nthRoot n a * nthRoot n b := by
  simp only [Real.nthRoot_of_even hn, Real.mul_rpow ha hb]

theorem nthRoot_mul_of_odd {n : ℕ} {a b : ℝ} (hn : Odd n) :
    nthRoot n (a * b) = nthRoot n a * nthRoot n b := by
  rw [Real.nthRoot, qpow_mul_of_odd]
  aesop

end Real
