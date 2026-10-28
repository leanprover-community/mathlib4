/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Int.Log
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# doc

## References

* <http://numbers.computation.free.fr/Constants/Algorithms/splitting.html>

-/

-- TODO: REMOVE ALL THE `toReal`

@[expose] public section

namespace Dyadic

@[simp]
lemma toReal_zero : toReal 0 = 0 := by
  simp [Dyadic.toReal]

@[simp]
lemma toRat_one : toRat 1 = 1 := rfl

@[simp]
lemma toRat_ofNat {n : ℕ} [n.AtLeastTwo] : toRat ofNat(n) = ofNat(n) := toRat_natCast n

@[simp]
lemma toRat_abs (x : Dyadic) : |x|.toRat = |x.toRat| := by
  rcases abs_choice x with h | h
  · grind [toRat_le_toRat_iff.mpr (sup_eq_left.mp h), toRat_neg x]
  · grind [toRat_le_toRat_iff.mpr (sup_eq_right.mp h), toRat_neg x]

@[simp]
lemma step_pos (prec : ℤ) : 0 < step prec := rfl

-- change name
lemma step_add_one (prec : ℤ) : step (prec + 1) + step (prec + 1) = step prec := by
  rw [← toRat_inj]
  simp [step, toRat_ofOdd_eq_mul_two_pow, -neg_add_rev]
  field_simp
  norm_num [zpow_add_one₀, _root_.mul_comm]

@[simp]
lemma toRat_pos (x : Dyadic) : 0 < x.toRat ↔ 0 < x := by
  rw [← toRat_zero, toRat_lt_toRat_iff]

section «#44548»

@[simp] theorem zero_shiftLeft (n : ℤ) : (0 : Dyadic) <<< n = 0 := rfl

@[simp] theorem zero_shiftRight (n : ℤ) : (0 : Dyadic) >>> n = 0 := rfl

@[simp] theorem ofOdd_shiftLeft {d k : ℤ} {hd : d % 2 = 1} {n : ℤ} :
    ofOdd d k hd <<< n = ofOdd d (k - n) hd := rfl

@[simp] theorem ofOdd_shiftRight {d k : ℤ} {hd : d % 2 = 1} {n : ℤ} :
    ofOdd d k hd >>> n = ofOdd d (k + n) hd := rfl

theorem toRat_shiftLeft (d : Dyadic) (n : ℤ) : (d <<< n).toRat = d.toRat * 2 ^ n := by
  rcases d with _ | ⟨d, k, hd⟩
  · simp
  · norm_num [toRat_ofOdd_eq_mul_two_pow, sub_eq_add_neg, zpow_add₀]
    ac_rfl

theorem toRat_shiftRight (d : Dyadic) (n : ℤ) : (d >>> n).toRat = d.toRat * 2 ^ (-n) := by
  rcases d with _ | ⟨d, k, hd⟩
  · simp
  · norm_num [toRat_ofOdd_eq_mul_two_pow, zpow_add₀]
    ac_rfl

theorem toRat_shiftRight' (d : Dyadic) (n : ℤ) : (d >>> n).toRat = d.toRat / 2 ^ n := by
  rw [toRat_shiftRight, zpow_neg, div_eq_mul_inv]

theorem toRat_shiftLeft_nat (d : Dyadic) (n : ℕ) : (d <<< n).toRat = d.toRat * 2 ^ n :=
  toRat_shiftLeft d n

theorem toRat_shiftRight_nat (d : Dyadic) (n : ℕ) : (d >>> n).toRat = d.toRat / 2 ^ n :=
  toRat_shiftRight' d n

end «#44548»

open Real

section SmallArtanh

theorem toReal_step (prec : ℤ) : (step prec).toReal = (1 / 2 : ℝ) ^ prec := by
  rw [← ofIntWithPrec_one, toReal, toRat_ofIntWithPrec_eq_mul_two_pow]
  simp

--  wait for <https://github.com/DavidLedvinka/mathlib4/tree/inclusion-division>?
/-- TODO doc -/
def ofIntFdivWithPrec (num den prec : ℤ) : Dyadic :=
  match prec with
  | .ofNat p => .ofIntWithPrec ((num <<< p).fdiv den) prec
  | .negSucc p => .ofIntWithPrec (num.fdiv (den <<< (p + 1))) prec

theorem _root_.Int.fdiv_eq_floor (num den : ℤ) : num.fdiv den = ⌊(num / den : ℚ)⌋ := by
  rcases lt_trichotomy den 0 with hden | rfl | hden
  · rw [← neg_div_neg_eq, ← Int.neg_fdiv_neg num den, Int.fdiv_eq_ediv,
      ite_eq_left (by omega), sub_zero, ← Int.cast_neg, ← Int.cast_neg]
    lift -den to ℕ using le_of_lt <| neg_pos.mpr hden with den
    rw [Int.cast_natCast, Rat.floor_intCast_div_natCast (-num) den]
  · simp
  · rw [Int.fdiv_eq_ediv, ite_eq_left (by omega), sub_zero]
    lift den to ℕ using hden.le
    rw [Int.cast_natCast, Rat.floor_intCast_div_natCast num den]

private theorem ofIntFdivWithPrec_spec (num den prec : ℤ) :
    (ofIntFdivWithPrec num den prec).toRat ≤ num / den ∧
      num / den < (ofIntFdivWithPrec num den prec + step prec).toRat := by
  rw [toRat_add, ← ofIntWithPrec_one]
  fun_cases ofIntFdivWithPrec with
  | case1 p =>
    simp only [toRat_ofIntWithPrec_eq_mul_two_pow, Int.ofNat_eq_natCast, ← _root_.add_mul]
    rw [zpow_neg, ← div_eq_mul_inv, div_le_iff₀ (by positivity),
      ← div_eq_mul_inv, lt_div_iff₀ (by positivity),
      Int.fdiv_eq_floor, Int.shiftLeft_eq, div_mul_eq_mul_div]
    push_cast
    exact Int.floor_eq_iff.mp rfl
  | case2 p =>
    simp only [toRat_ofIntWithPrec_eq_mul_two_pow, zpow_neg, zpow_negSucc, ← _root_.add_mul]
    rw [inv_inv, ← le_div_iff₀ (by positivity), ← div_lt_iff₀ (by positivity),
      Int.fdiv_eq_floor, Int.shiftLeft_eq, div_div]
    push_cast
    exact Int.floor_eq_iff.mp rfl

theorem ofIntFdivWithPrec_le (num den prec : ℤ) :
    (ofIntFdivWithPrec num den prec).toRat ≤ num / den :=
  ofIntFdivWithPrec_spec _ _ _ |>.left

theorem lt_ofIntFdivWithPrec (num den prec : ℤ) :
    num / den < (ofIntFdivWithPrec num den prec + step prec).toRat :=
  ofIntFdivWithPrec_spec _ _ _ |>.right

theorem abs_ofIntFdivWithPrec_le (num den prec : ℤ) :
    |num / den - (ofIntFdivWithPrec num den prec).toRat| ≤ (step prec).toRat := by
  rw [abs_le]
  constructor
  · grw [neg_le_sub_iff_le_add, ofIntFdivWithPrec_le num den prec, le_add_iff_nonneg_right]
    rw [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]
    norm_num [Rat.zpow_nonneg]
  · rw [tsub_le_iff_right, _root_.add_comm, ← toRat_add]
    exact lt_ofIntFdivWithPrec num den prec |>.le

theorem abs_ofIntFdivWithPrec_le_pow (num den prec : ℤ) :
    |num / den - (ofIntFdivWithPrec num den prec).toReal| ≤ (1 / 2 : ℝ) ^ prec := by
  rw [← toReal_step prec]
  unfold toReal
  exact_mod_cast abs_ofIntFdivWithPrec_le num den prec

/-- TODO doc -/
protected def smallArtanh (num den : ℕ) (n : ℕ) : ℕ × ℕ :=
  let (_, Q, R) := go 0 n
  (num * R, den * Q)
where
  go : ℕ -> ℕ -> ℕ × ℕ × ℕ := fun a b =>
    match h : b - a with
    | 0 => (1, 1, 0)
    | 1 => ((2 * a + 1) * num ^ 2, (2 * a + 3) * den ^ 2, (2 * a + 3) * den ^ 2)
    | _ + 2 =>
      let m : ℕ := (a + b) / 2
      let (Pl, Ql, Rl) : ℕ × ℕ × ℕ := go a m
      let (Pr, Qr, Rr) : ℕ × ℕ × ℕ := go m b
      (Pl * Pr, Ql * Qr, Qr * Rl + Pl * Rr)
  termination_by a b => b - a
  decreasing_by all_goals omega

theorem smallArtanh.go_spec (num den a b : ℕ) :
    let (P, Q, R) : ℕ × ℕ × ℕ := go num den a b
    P = ∏ i ∈ Finset.Ico a b, (2 * i + 1) * num ^ 2 ∧
    Q = ∏ i ∈ Finset.Ico a b, (2 * i + 3) * den ^ 2 ∧
    R = ∑ i ∈ Finset.Ico a b, (∏ j ∈ Finset.Ico a i, (2 * j + 1) * num ^ 2) *
      ∏ j ∈ Finset.Ico i b, (2 * j + 3) * den ^ 2 := by
  induction hm : b - a using Nat.strong_induction_on generalizing a b with | h m ih
  match m with
  | 0 =>
    rw [go, hm, Finset.Ico_eq_empty <| Nat.le_lt_asymm <| Nat.le_of_sub_eq_zero hm]
    simp
  | 1 =>
    replace hm : b = a + 1 := by omega
    subst b
    rw [go, Nat.add_sub_cancel_left]
    simp
  | m + 2 =>
    rw [go, hm]
    set m := (a + b) / 2
    have ih1 := ih (m - a) (by omega) a m rfl
    have ih2 := ih (b - m) (by omega) m b rfl
    simp only at ih1 ih2 ⊢
    simp only [ih1, ih2]
    split_ands
    · apply Finset.prod_Ico_consecutive <;> omega
    · apply Finset.prod_Ico_consecutive <;> omega
    · rw [Finset.mul_sum, Finset.mul_sum]
      conv_lhs =>
        congr
        · apply Finset.sum_congr rfl
          tactic =>
            intro i hi
            rw [← _root_.mul_assoc, mul_rotate, _root_.mul_assoc,
              Finset.prod_Ico_consecutive _ (by grind) (by omega)]
        · apply Finset.sum_congr rfl
          tactic =>
            intro i hi
            rw [← _root_.mul_assoc, Finset.prod_Ico_consecutive _ (by omega) (by grind)]
      apply Finset.sum_Ico_consecutive <;> omega

theorem smallArtanh.go_spec' {num den : ℕ} (hden : den ≠ 0) (a b : ℕ) :
    let (_, Q, R) : ℕ × ℕ × ℕ := go num den a b
    R / Q = ∑ i ∈ Finset.Ico a b, ∏ j ∈ Finset.Ico a i,
      (((2 * j + 1) * num ^ 2) / ((2 * j + 3) * den ^ 2) : ℚ) := by
  simp only [go_spec num den a b]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  conv_lhs =>
    apply Finset.sum_congr rfl
    tactic =>
      intro i hi
      rw [← div_eq_mul_inv,
        ← Finset.prod_Ico_consecutive (m := a) (n := i) (k := b) _ (by grind) (by grind),
        mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.mpr fun j _ => by positivity),
        ← Finset.prod_div_distrib]

theorem smallArtanh.den_nonzero (num den n : ℕ) (hden : den ≠ 0) :
    (Dyadic.smallArtanh num den n).2 ≠ 0 := by
  unfold Dyadic.smallArtanh
  simp only [go_spec num den 0 n]
  simpa [hden] using Finset.prod_ne_zero_iff.mpr fun j _ => by positivity

theorem smallArtanh.def_aux (num den n : ℕ) :
    let (P, Q) : ℕ × ℕ := Dyadic.smallArtanh num den n
    P / Q = ∑ k ∈ Finset.range n, (num / den : ℚ) ^ (2 * k + 1) / (2 * k + 1) := by
  unfold Dyadic.smallArtanh
  by_cases hden : den = 0
  · simp [hden]
  push_cast
  rw [mul_div_mul_comm, go_spec' hden, Finset.mul_sum]
  simp only [Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl fun i hi => ?_
  induction i with
  | zero => simp
  | succ i ih =>
    specialize ih (by grind)
    rw [Finset.prod_range_succ, ← _root_.mul_assoc, ih]
    simp [div_pow]
    field_simp
    ring

theorem smallArtanh_def_aux_real (num den n : ℕ) :
    let (P, Q) : ℕ × ℕ := Dyadic.smallArtanh num den n
    P / Q = ∑ k ∈ Finset.range n, (num / den : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  have := congrArg ((↑) : ℚ -> ℝ) <| smallArtanh.def_aux num den n
  push_cast at this ⊢
  exact_mod_cast this

private theorem sum_lt_of_pos {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * k + 1) < artanh x := by
  have h : ∀ k : ℕ, 0 < x ^ (2 * k + 1) / (2 * k + 1) :=
    fun k => div_pos (pow_succ_pos hx.left (2 * k)) (by grind)
  suffices HasSum (fun k : ℕ => x ^ (2 * k + 1) / (2 * k + 1)) (artanh x) by
    rw [← this.tsum_eq, ← this.summable.sum_add_tsum_nat_add n, lt_add_iff_pos_right]
    exact summable_nat_add_iff n |>.mpr this.summable |>.tsum_pos
      (fun k => h (k + n) |>.le) 0 (h (0 + n))
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => h k |>.le) (artanh x)).mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_eq_abs, abs_sub_comm]
  have := sum_range_sub_log_div_le (by grind : |x| < 1)
  rw [← artanh_eq_half_log (by grind)] at this
  refine squeeze_zero (fun k => abs_nonneg _) this ?_
  simp only [pow_succ |x|]
  simp only [mul_div_assoc, pow_mul]
  rw [← zero_mul (|x| / (1 - x ^ 2))]
  refine tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_ |>.mul_const _
  grind [sq_lt_one_iff_abs_lt_one]

private theorem abs_artanh_sub_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    |artanh x - ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * ↑k + 1)| ≤
      |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  have := sum_range_sub_log_div_le (x := x) (abs_lt.mpr (mod_cast hx)) n
  rw [artanh_eq_half_log <| Set.Ioo_subset_Icc_self (by simpa using mod_cast hx)]
  simpa [Dyadic.smallArtanh] using this

/-- Computes the lower bound `l : Dyadic` for `log 2` with precision `prec`,
that is, `l < log 2` and `log 2 - l` < `ulp`. -/
protected def log_two (prec : ℕ) : Dyadic :=
  -- use `prec / 8 + 1` instead of `(prec + 7) / 8` to make sure `k ≠ 0`
  let (P1, Q1) : ℕ × ℕ := Dyadic.smallArtanh 1 17 (prec / 8 + 1)
  let (P2, Q2) : ℕ × ℕ := Dyadic.smallArtanh 1 19 (prec / 8 + 1)
  let (P3, Q3) : ℕ × ℕ := Dyadic.smallArtanh 1 31 (prec / 9 + 1)
  let P : ℕ := 6 * P1 * Q2 * Q3 + 4 * Q1 * P2 * Q3 + 4 * Q1 * Q2 * P3
  let Q : ℕ := Q1 * Q2 * Q3
  ofIntFdivWithPrec P Q (prec + 3)

theorem log_two_aux :
    log 2 = 6 * artanh (1 / 17) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31) := by
  rw [show (2 : ℝ) = (9 / 8) ^ 3 * (10 / 9) ^ 2 * (16 / 15) ^ 2 by norm_num]
  simp [log_mul]
  norm_num [artanh_eq_half_log]
  field

theorem abs_log_two_sub_lt (prec : ℕ) :
    |log 2 - (Dyadic.log_two prec).toRat| < (1 / 2) ^ prec := by
  unfold Dyadic.log_two
  have hartanh17 := smallArtanh_def_aux_real 1 17 (prec / 8 + 1)
  have hartanh19 := smallArtanh_def_aux_real 1 19 (prec / 8 + 1)
  have hartanh31 := smallArtanh_def_aux_real 1 31 (prec / 9 + 1)
  have hartanh17₀ := smallArtanh.den_nonzero 1 17 (prec / 8 + 1) (by simp)
  have hartanh19₀ := smallArtanh.den_nonzero 1 19 (prec / 8 + 1) (by simp)
  have hartanh31₀ := smallArtanh.den_nonzero 1 31 (prec / 9 + 1) (by simp)
  set artanh17 : ℕ × ℕ := Dyadic.smallArtanh 1 17 (prec / 8 + 1)
  set artanh19 : ℕ × ℕ := Dyadic.smallArtanh 1 19 (prec / 8 + 1)
  set artanh31 : ℕ × ℕ := Dyadic.smallArtanh 1 31 (prec / 9 + 1)
  simp only at *
  rw [show (1 / 2 : ℝ) ^ prec = (6 + 4 + 4) * (1 / 2) ^ (prec + 4) + (1 / 2) ^ (prec + 3 : ℤ) by
    norm_cast; ring]
  refine abs_sub_le _ _ _ |>.trans_lt <|
    add_lt_add_of_lt_of_le ?_ <| abs_ofIntFdivWithPrec_le_pow _ _ _
  push_cast
  simp only [add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [log_two_aux, ← sub_sub, ← sub_sub, add_sub_right_comm, add_sub_right_comm,
    add_sub_right_comm (6 * _), ← mul_sub, add_sub_assoc, ← mul_sub, add_sub_assoc, ← mul_sub]
  grw [abs_add_le, abs_add_le, _root_.add_mul, _root_.add_mul]
  repeat rw [abs_mul, Nat.abs_ofNat]
  gcongr <;> [rw [hartanh17]; rw [hartanh19]; rw [hartanh31]]
  <;> grw [Nat.cast_one, Nat.cast_ofNat, abs_artanh_sub_le (by grind), abs_of_pos (by simp)]
  <;> clear * -
  -- <;> [set k : ℕ := prec / 8 + 1; set k : ℕ := prec / 8 + 1; set k : ℕ := prec / 9 + 1]
  -- <;> [set m : ℕ := 8 * k; set m : ℕ := 8 * k; set m : ℕ := 9 * k]
  -- <;> (norm_num [pow_add, pow_mul]; field_simp; ring_nf)
  -- <;> (gcongr; on_goal 2 => norm_num)
  -- <;> apply pow_le_pow_iff_right_of_lt_one₀ (m := m) (by norm_num) (by norm_num)
  --   |>.mpr (by omega) |>.trans_lt'
  -- <;> unfold m
  -- <;> norm_num [pow_mul]
  -- <;> exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by simp)
  · set k : ℕ := prec / 8 + 1
    norm_num [pow_add, pow_mul]
    field_simp
    ring_nf
    gcongr
    · apply pow_le_pow_iff_right_of_lt_one₀ (m := 8 * k) (by norm_num) (by norm_num)
        |>.mpr (by omega) |>.trans_lt'
      norm_num [pow_mul]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by simp)
    · norm_num
  · set k : ℕ := prec / 8 + 1
    norm_num [pow_add, pow_mul]
    field_simp
    ring_nf
    gcongr
    · apply pow_le_pow_iff_right_of_lt_one₀ (m := 8 * k) (by norm_num) (by norm_num)
        |>.mpr (by omega) |>.trans_lt'
      norm_num [pow_mul]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by simp)
    · norm_num
  · set k : ℕ := prec / 9 + 1
    norm_num [pow_add, pow_mul]
    field_simp
    ring_nf
    gcongr
    · apply pow_le_pow_iff_right_of_lt_one₀ (m := 9 * k) (by norm_num) (by norm_num)
        |>.mpr (by omega) |>.trans_lt'
      norm_num [pow_mul]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by simp)
    · norm_num

theorem log_two_lt (prec : ℕ) :
    (Dyadic.log_two prec).toRat < log 2 := by
  unfold Dyadic.log_two
  have hartanh17 := smallArtanh_def_aux_real 1 17 (prec / 8 + 1)
  have hartanh19 := smallArtanh_def_aux_real 1 19 (prec / 8 + 1)
  have hartanh31 := smallArtanh_def_aux_real 1 31 (prec / 9 + 1)
  have hartanh17₀ := smallArtanh.den_nonzero 1 17 (prec / 8 + 1) (by simp)
  have hartanh19₀ := smallArtanh.den_nonzero 1 19 (prec / 8 + 1) (by simp)
  have hartanh31₀ := smallArtanh.den_nonzero 1 31 (prec / 9 + 1) (by simp)
  set artanh17 : ℕ × ℕ := Dyadic.smallArtanh 1 17 (prec / 8 + 1)
  set artanh19 : ℕ × ℕ := Dyadic.smallArtanh 1 19 (prec / 8 + 1)
  set artanh31 : ℕ × ℕ := Dyadic.smallArtanh 1 31 (prec / 9 + 1)
  simp only at *
  grw [ofIntFdivWithPrec_le]
  push_cast
  simp only [add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [hartanh17, hartanh19, hartanh31]
  iterate 3 grw [sum_lt_of_pos (by norm_num)]
  simp only [Nat.cast_one, Nat.cast_ofNat, log_two_aux, le_rfl]

theorem lt_log_two (prec : ℕ) :
    log 2 < (Dyadic.log_two prec).toRat + (Dyadic.step prec).toReal := by
  rw [toReal_step prec, zpow_natCast]
  grind [abs_sub_lt_iff, abs_log_two_sub_lt prec]

theorem abs_sub_log_two_lt (prec : ℕ) :
    |(Dyadic.log_two prec).toRat + (Dyadic.step prec).toRat - log 2| < (1 / 2) ^ prec := by
  change |(Dyadic.log_two prec).toRat + (Dyadic.step prec).toReal - log 2| < (1 / 2) ^ prec
  rw [abs_of_pos <| sub_pos_of_lt <| lt_log_two prec, ← ofIntWithPrec_one, toReal,
    toRat_ofIntWithPrec_eq_mul_two_pow, Int.cast_one, _root_.one_mul, zpow_neg, ← inv_zpow,
    ← one_div]
  push_cast
  rw [zpow_natCast]
  simp [add_sub_right_comm, log_two_lt prec]

end SmallArtanh

section Log

/-- TODO doc -/
protected def logSum (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 1 ∨ x = -1 then 0 else
  match x with
  | zero => 0
  | ofOdd n _ _ =>
    let e : ℕ := n.natAbs.log2
    let m : ℕ := n.natAbs
    -- Dyadic.smallArtanh -> δ₁ < (1 / 2) ^ (prec + 2)
    let (P, Q) : ℕ × ℕ := Dyadic.smallArtanh (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
    -- ofIntFdivWithPrec -> δ₂ ≤ (1 / 2) ^ (prec + 2)
    -- δ ≤ 2 * (δ₁ + δ₂) < (1 / 2) ^ prec
    2 * ofIntFdivWithPrec P Q (prec + 2)

theorem _root_.Real.log_eq_two_mul_artanh {x : ℝ} (hx : 0 < x) :
    log x = 2 * artanh ((x - 1) / (x + 1)) := by
  rw [artanh_eq_half_log (by constructor <;> field_simp <;> grind)]
  simp
  congr
  field

theorem Aux (n k : ℤ) (hn : n % 2 = 1) :
    1 ≤ |Dyadic.ofOdd n k hn| ∧ |Dyadic.ofOdd n k hn| < 2 -> k = n.natAbs.log2 := by
  intro hx
  rw [← toRat_le_toRat_iff, ← toRat_lt_toRat_iff] at hx
  norm_num [toRat_ofOdd_eq_mul_two_pow, field, ← zpow_add_one₀] at hx
  have hn : 0 < |(n : ℚ)| := lt_of_lt_of_le (zpow_pos (by norm_num) k) hx.left
  rw [le_antisymm ((Int.zpow_le_iff_le_log (by norm_num) hn).mp hx.left)
    (Int.le_of_lt_add_one ((Int.lt_zpow_iff_log_lt (by norm_num) hn).mp hx.right)),
    ← Int.cast_abs, ← Nat.cast_natAbs, Int.log_natCast, ← Nat.log2_eq_log_two]

theorem logSum_lt {x : Dyadic} (hx : 1 < |x| ∧ |x| < 2) (prec : ℕ) :
    (x.logSum prec).toRat < log x.toRat := by
  fun_cases Dyadic.logSum with
  | case1 _ hx' => rcases hx' with rfl | rfl <;> simp [← toRat_lt_toRat_iff] at hx
  | case2 _ => simp [← toRat_lt_toRat_iff, not_lt_of_gt] at hx
  | case3 n k hn e m P Q hPQ hx' =>
    have hk := Aux n k hn <| hx.imp_left le_of_lt
    subst k
    have hem : m ≥ 2 ^ e := by
      refine Nat.log2_self_le ?_
      omega
    replace hem : m > 2 ^ e := by
      apply lt_of_le_of_ne hem
      simp [← toRat_lt_toRat_iff, toRat_ofOdd_eq_mul_two_pow, ← Int.cast_abs,
        ← Nat.cast_natAbs, field] at hx
      norm_cast at hx
      grind
    have hem' : (↑(m - 2 ^ e) / ↑(m + 2 ^ e) : ℝ) ∈ Set.Ioo 0 1 := by
      suffices (m : ℝ) < 2 * 2 ^ e by simpa [field, hem.le] using ⟨mod_cast hem, by linarith⟩
      norm_cast
      grind [n.natAbs.lt_log2_self]
    simp only [toRat_mul, toRat_ofNat, Rat.cast_mul, Rat.cast_ofNat]
    grw [ofIntFdivWithPrec_le P Q (prec + 2)]
    simp only [Int.cast_natCast, Rat.cast_div, Rat.cast_natCast]
    have hartanh := smallArtanh_def_aux_real (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
    simp only [hPQ] at hartanh
    grw [hartanh, sum_lt_of_pos hem', artanh_eq_half_log (by grind),
      one_div, mul_inv_cancel_left₀ (by simp)]
    apply le_of_eq
    nth_rw 2 [← Real.log_abs]
    congr
    simp [hem.le, field, toRat_ofOdd_eq_mul_two_pow, m]

theorem logSum_le {x : Dyadic} (hx : 1 ≤ |x| ∧ |x| < 2) (prec : ℕ) :
    (x.logSum prec).toRat ≤ log x.toRat := by
  by_cases hx' : |x| = 1
  · rcases eq_or_eq_neg_of_abs_eq hx' with rfl | rfl <;> simp [Dyadic.logSum]
  · exact logSum_lt (hx.imp_left (lt_of_le_of_ne · (Ne.symm hx'))) prec |>.le

theorem abs_sub_logSum_lt {x : Dyadic} (hx : 1 ≤ |x| ∧ |x| < 2) (prec : ℕ) :
    |log x.toRat - (x.logSum prec).toRat| < (1 / 2) ^ prec := by
  fun_cases Dyadic.logSum with
  | case1 _ hx' => rcases hx' with rfl | rfl <;> simp
  | case2 _ => simp
  | case3 n k hn e m P Q hPQ hx' =>
    have hem : m ≥ 2 ^ e := by
      refine Nat.log2_self_le ?_
      omega
    grw [show (1 / 2 : ℝ) ^ prec = (1 / 2) ^ (prec + 1) + (1 / 2) ^ (prec + 1) by ring,
      abs_sub_le (b := (2 * (P / Q) : ℝ))]
    apply add_lt_add_of_lt_of_le
    · rw [← Real.log_abs, Real.log_eq_two_mul_artanh (by simp), ← mul_sub, abs_mul, Nat.abs_ofNat]
      set X : ℝ := (m - 2 ^ e : ℕ) / (m + 2 ^ e : ℕ)
      have hX1 : X < 1 / 3 := by
        unfold X
        field_simp
        zify [hem]
        suffices (m : ℝ) < 2 * 2 ^ e by linarith
        norm_cast
        grind [n.natAbs.lt_log2_self]
      have hX2 : |X| < 1 / 3 := by
        rw [abs_lt]
        refine ⟨lt_of_lt_of_le (b := 0) (by norm_num) ?_, hX1⟩
        simp [X, field]
      have hX3 : X = (|↑(ofOdd n k hn).toRat| - 1) / (|↑(ofOdd n k hn).toRat| + 1) := by
        simp [toRat_ofOdd_eq_mul_two_pow, field, Aux n k hn hx, hem, m, e]
      have H := smallArtanh_def_aux_real (m - 2 ^ e) (m + 2 ^ e) (prec / 3 + 1)
      simp only [hPQ] at H
      rw [← hX3, H]
      set N : ℕ := prec / 3 + 1
      grw [abs_artanh_sub_le (by grind)]
      calc
        _ ≤ 2 * (|X| ^ (2 * N + 1) / (1 - (1 / 3) ^ 2)) := by gcongr
        _ ≤ 2 * ((1 / 3) ^ (2 * N + 1) / (1 - (1 / 3) ^ 2)) := by gcongr
        _ < (1 / 2) ^ (prec + 1) := by
          apply pow_le_pow_iff_right_of_lt_one₀ (m := 3 * N) (by norm_num) (by norm_num)
            |>.mpr (by omega) |>.trans_lt'
          norm_num [pow_add, pow_mul]
          field_simp
          ring_nf
          gcongr <;> norm_num
    · rw [toRat_mul, Rat.cast_mul, toRat_ofNat, Rat.cast_ofNat, ← mul_sub, abs_mul, Nat.abs_ofNat]
      have := abs_ofIntFdivWithPrec_le_pow P Q (prec + 2)
      simp only [Int.cast_natCast, toReal, one_div, inv_zpow', neg_add_rev, Int.reduceNeg] at this
      grw [this]
      simp [-neg_add_rev, ← sub_eq_add_neg, neg_sub_left]
      norm_num [zpow_add₀, pow_succ]
      grind

/-- Computes the lower bound for `log x`. -/
def lowerLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 1 ∨ x = -1 then 0 else
  match x with
  | zero => 0
  | ofOdd n p hn =>
    let k : ℤ := n.natAbs.log2 - p -- `k ≥ 0 ↔ |x| ≥ 1`
    let x' : Dyadic := .ofOdd n n.natAbs.log2 hn -- `|x'| ∈ [1, 2)`
    let wp : ℕ := prec + k.natAbs.log2 + 2
    if k ≥ 0 then
      Dyadic.logSum x' (prec + 1) + k * Dyadic.log_two wp
    else
      Dyadic.logSum x' (prec + 1) + k * (Dyadic.log_two wp + Dyadic.step wp)

/-- Computes the upper bound for `log x`. -/
def upperLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if x = 0 ∨ x = 1 ∨ x = -1 then 0 else lowerLog x prec + Dyadic.step prec

theorem lowerLog_lt {x : Dyadic} (hx : x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1) (prec : ℕ) :
    (x.lowerLog prec).toReal < x.toReal.log := by
  -- duplicate `have`s
  have H (n : ℤ) (hn : n % 2 = 1) :
      1 ≤ |Dyadic.ofOdd n n.natAbs.log2 hn| ∧ |Dyadic.ofOdd n n.natAbs.log2 hn| < 2 := by
    rw [← toRat_le_toRat_iff, ← toRat_lt_toRat_iff]
    simp only [toRat_one, toRat_abs, toRat_ofOdd_eq_mul_two_pow, zpow_neg, zpow_natCast, abs_pow,
      Nat.abs_ofNat, toRat_ofNat, ← div_eq_mul_inv, abs_div, ← Int.cast_abs, ← Nat.cast_natAbs]
    rw [le_div_iff₀ (by positivity), _root_.one_mul, div_lt_iff₀ (by positivity), ← pow_succ']
    exact ⟨mod_cast Nat.log2_self_le (by omega), mod_cast Nat.lt_log2_self⟩
  have H' (n k : ℤ) (hn : n % 2 = 1) :
      ofOdd n k hn = ofOdd n n.natAbs.log2 hn <<< (n.natAbs.log2 - k) := by
    grind [ofOdd_shiftLeft]
  fun_cases lowerLog with
  | case1 | case2 => tauto
  | case3 n k hn k' x' wp hk' hx' =>
    rw [H' n k hn, toReal, toReal, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), Rat.cast_zpow, Rat.cast_ofNat, log_zpow,
      toRat_add, Rat.cast_add, toRat_mul, Rat.cast_mul, toRat_intCast, Rat.cast_intCast]
    rcases lt_or_eq_of_le hk' with hk' | hk'
    · exact add_lt_add_of_le_of_lt (logSum_le (H n hn) (prec + 1)) <|
        mul_lt_mul_of_pos_left (log_two_lt wp) (mod_cast hk')
    · have := sub_eq_zero.mp hk'.symm |>.symm
      subst this
      refine add_lt_add_of_lt_of_le ?_ ?_
      · exact logSum_lt ⟨lt_of_le_of_ne (H n hn).1 (Ne.symm (by grind)), (H n hn).2⟩ (prec + 1)
      · simp [← hk']
  | case4 n k hn k' x' wp hk' hx' =>
    rw [H' n k hn, toReal, toReal, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), Rat.cast_zpow, Rat.cast_ofNat, log_zpow,
      toRat_add, Rat.cast_add]
    apply add_lt_add_of_le_of_lt (logSum_le (H n hn) (prec + 1))
    rw [toRat_mul, Rat.cast_mul, toRat_intCast, Rat.cast_intCast, toRat_add, Rat.cast_add]
    exact mul_lt_mul_of_neg_left (lt_log_two wp) (mod_cast not_le.mp hk')

theorem lowerLog_le (x : Dyadic) (prec : ℕ) :
    (x.lowerLog prec).toReal ≤ x.toReal.log := by
  by_cases hx : x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1
  · exact lowerLog_lt hx prec |>.le
  · push +distrib Not at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [toReal, lowerLog, Eq.comm, ← Dyadic.zero_eq] <;>
      simp [Dyadic.zero_eq]

theorem abs_lowerLog_lt (x : Dyadic) (prec : ℕ) :
    |x.toReal.log - (x.lowerLog prec).toReal| < (Dyadic.step prec).toReal := by
  have H (n : ℤ) (hn : n % 2 = 1) :
      1 ≤ |Dyadic.ofOdd n n.natAbs.log2 hn| ∧ |Dyadic.ofOdd n n.natAbs.log2 hn| < 2 := by
    rw [← toRat_le_toRat_iff, ← toRat_lt_toRat_iff]
    simp only [toRat_one, toRat_abs, toRat_ofOdd_eq_mul_two_pow, zpow_neg, zpow_natCast, abs_pow,
      Nat.abs_ofNat, toRat_ofNat, ← div_eq_mul_inv, abs_div, ← Int.cast_abs, ← Nat.cast_natAbs]
    rw [le_div_iff₀ (by positivity), _root_.one_mul, div_lt_iff₀ (by positivity), ← pow_succ']
    exact ⟨mod_cast Nat.log2_self_le (by omega), mod_cast Nat.lt_log2_self⟩
  have H' (n k : ℤ) (hn : n % 2 = 1) :
      ofOdd n k hn = ofOdd n n.natAbs.log2 hn <<< (n.natAbs.log2 - k) := by
    grind [ofOdd_shiftLeft]
  fun_cases lowerLog with
  | case1 _ hx => rcases hx with rfl | rfl <;> simp [toReal]
  | case2 hx' => simp [toReal]
  | case3 n k hn k' x' wp hk' hx' =>
    -- duplicate proof
    -- not a good proof
    simp only [toReal_add, toReal_mul, toReal_intCast]
    nth_grw 1 [H' n k hn, toReal, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), add_sub_add_comm, abs_add_le]
    simp only [Rat.cast_zpow, Rat.cast_ofNat, log_zpow]
    rw [← mul_sub, abs_mul, abs_of_nonneg (a := (k' : ℝ)) (mod_cast hk')]
    simp only [toReal]
    rw [← step_add_one, toRat_add, Rat.cast_add]
    apply add_lt_add_of_lt_of_le
    · rw [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]
      convert abs_sub_logSum_lt (H n hn) (prec + 1)
      simp [-neg_add_rev]
      simp only [← Nat.cast_add_one, zpow_natCast]
    · grw [abs_log_two_sub_lt wp]
      rw [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]
      simp [-neg_add_rev]
      simp only [← Nat.cast_add_one, zpow_natCast]
      field_simp
      suffices k' ≤ 2 ^ (k'.natAbs.log2 + 1) by
        grw [this]
        simp [← pow_add, wp]
        ring_nf
        rfl
      grw [k'.le_natAbs]
      exact_mod_cast Nat.lt_log2_self.le
  | case4 n k hn k' x' wp hk' hx' =>
    simp only [toReal_add, toReal_mul, toReal_intCast]
    nth_grw 1 [H' n k hn, toReal, toRat_shiftLeft, Rat.cast_mul,
      log_mul (by simp) (by norm_num [zpow_ne_zero]), add_sub_add_comm, abs_add_le]
    simp only [Rat.cast_zpow, Rat.cast_ofNat, log_zpow]
    rw [abs_sub_comm (_ * _), ← mul_sub, abs_mul]
    simp only [toReal]
    nth_rw 2 [← step_add_one]
    rw [toRat_add, Rat.cast_add]
    apply add_lt_add_of_lt_of_le
    · rw [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]
      convert abs_sub_logSum_lt (H n hn) (prec + 1)
      simp [-neg_add_rev]
      simp only [← Nat.cast_add_one, zpow_natCast]
    · grw [abs_sub_log_two_lt wp]
      rw [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]
      simp [-neg_add_rev]
      simp only [← Nat.cast_add_one, zpow_natCast]
      field_simp
      suffices |(k' : ℝ)| ≤ 2 ^ (k'.natAbs.log2 + 1) by
        grw [this]
        simp [← pow_add, wp]
        ring_nf
        rfl
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast Nat.lt_log2_self.le

theorem le_upperLog (x : Dyadic) (prec : ℕ) :
    log x.toRat ≤ (x.upperLog prec).toRat := by
  unfold upperLog
  by_cases hx : x = 0 ∨ x = 1 ∨ x = -1
  · simp only [hx, ↓reduceIte, toRat_zero, Rat.cast_zero]
    rw [log_eq_zero.mpr]
    rcases hx with rfl | rfl | rfl <;> simp
  · simp [hx]
    grind [abs_lowerLog_lt x prec, toReal]

end Log

end Dyadic

namespace Inclusion

/-- TODO doc -/
def Interval.log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let I' : Interval Dyadic := I.abs
  match I' with
  | ⟨some lb, ⊤⟩ =>
    if lb = 0 then
      .univ Dyadic
    else
      .Ici <| lb.lowerLog prec
  | ⟨some lb, some ub⟩ =>
    if lb = 0 then
      if ub = 0 then
        .singleton 0
      else
        .Iic <| (max (ub.upperLog prec) 0 : Dyadic)
    else
      ⟨lb.lowerLog prec, ub.upperLog prec⟩
  | _ => .univ Dyadic -- impossible case

theorem Interval.mem_mk {α : Type*} [Preorder α] (x a b : α) :
    x ∈ (⟨a, b⟩ : Interval α) ↔ a ≤ x ∧ x ≤ b := by
  simp

@[simp]
theorem IntervalDyadicReal.mem_mk_coe (x : ℝ) (a b : Dyadic) :
    x ∈ (⟨a, b⟩ : Interval Dyadic) ↔ a.toReal ≤ x ∧ x ≤ b.toReal := by
  simp [mem_iff_mem_map, Interval.map]

@[simp]
theorem IntervalDyadicReal.mem_Iic_coe (x : ℝ) (b : Dyadic) :
    x ∈ Interval.Iic (↑b : WithTop Dyadic) ↔ x ≤ b.toReal := by
  simp [mem_iff_mem_map, Interval.Iic, Interval.map]

@[simp]
theorem IntervalDyadicReal.mem_Ici_coe (x : ℝ) (a : Dyadic) :
    x ∈ Interval.Ici (↑a : WithBot Dyadic) ↔ a.toReal ≤ x := by
  simp [mem_iff_mem_map, Interval.Ici, Interval.map]

-- don't use this, use #43038 ?
instance : AddLeftMono Dyadic where
  elim a b c h := Dyadic.toReal_le_toReal.mp <| by simpa

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : x.log ∈ I.log prec := by
  apply IntervalDyadicReal.abs_mem at hx
  rw [← Real.log_abs]
  have hx' : 0 ≤ |x| := abs_nonneg x
  generalize |x| = x at *
  fun_cases Interval.log with
  | case1 | case6 => apply Interval.mem_map_univ
  | case2 I' lb hI' hlb =>
    rw [show I.abs = I' from rfl, hI'] at hx
    refine IntervalDyadicReal.mem_Ici_coe _ _ |>.mpr <|
      Dyadic.lowerLog_le lb prec |>.trans <| Real.log_le_log ?_ <|
        IntervalDyadicReal.mem_Ici_coe x lb |>.mp hx
    have := WithBot.coe_nonneg.mp <| hI' ▸ show 0 ≤ I'.lb from I.abs_lb_nonneg
    simpa [← Dyadic.toReal_zero] using lt_of_le_of_ne this <| Ne.symm hlb
  | case3 I' hI' =>
    rw [show I.abs = I' from rfl, hI'] at hx
    replace hx := Dyadic.toReal_zero ▸ (IntervalDyadicReal.mem_mk_coe x 0 0).mp hx
    rw [le_antisymm hx.2 hx.1, Real.log_zero, ← Dyadic.toReal_zero]
    exact Interval.mem_map_singleton 0 Dyadic.toReal
  | case4 I' ub hub hI' =>
    rw [show I.abs = I' from rfl, hI'] at hx
    replace hx : 0 ≤ x ∧ x ≤ ub.toReal :=
      Dyadic.toReal_zero ▸ (IntervalDyadicReal.mem_mk_coe x 0 ub |>.mp hx)
    refine IntervalDyadicReal.mem_Iic_coe _ _ |>.mpr ?_
    rw [Monotone.map_max (f := Dyadic.toReal) Dyadic.toRealOrderEmbedding.monotone]
    simp only [Dyadic.toReal_zero, le_max_iff]
    by_cases hx₀ : x = 0
    · simp [hx₀, Dyadic.toReal]
    · exact Or.inl <| Dyadic.le_upperLog ub prec |>.trans' <| Real.log_le_log (by grind) hx.right
  | case5 I' lb ub hI' hlb =>
    rw [show I.abs = I' from rfl, hI'] at hx
    replace hx : lb.toReal ≤ x ∧ x ≤ ub.toReal := IntervalDyadicReal.mem_mk_coe x _ _ |>.mp hx
    simp only [IntervalDyadicReal.mem_mk_coe]
    have : 0 < lb.toReal := by
      have := WithBot.coe_nonneg.mp <| hI' ▸ show 0 ≤ I'.lb from I.abs_lb_nonneg
      simpa [← Dyadic.toReal_zero] using lt_of_le_of_ne this <| Ne.symm hlb
    exact ⟨lb.lowerLog_le prec |>.trans <| Real.log_le_log this <| hx.left,
      ub.le_upperLog prec |>.trans' <| Real.log_le_log (this.trans_le hx.left) hx.right⟩

end Inclusion
