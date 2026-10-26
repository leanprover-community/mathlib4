/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# doc

## References

* <http://numbers.computation.free.fr/Constants/Algorithms/splitting.html>

-/

@[expose] public section

namespace Dyadic

@[simp]
lemma _root_.Dyadic.toReal_zero : Dyadic.toReal (0 : Dyadic) = 0 := by
  simp [Dyadic.toReal]

open Real

section SmallArtanh

theorem toReal_step (prec : ℤ) : (step prec).toReal = (1 / 2 : ℝ) ^ prec := by
  rw [← ofIntWithPrec_one, toReal, toRat_ofIntWithPrec_eq_mul_two_pow]
  simp

def ofIntFdivWithPrec (num den prec : ℤ) : Dyadic :=
  match prec with
  | .ofNat p => .ofIntWithPrec ((num <<< p).fdiv den) prec
  | .negSucc p => .ofIntWithPrec ((num >>> (p + 1)).fdiv den) prec

theorem ofIntFdivWithPrec_le (num den prec : ℤ) :
    (ofIntFdivWithPrec num den prec).toRat ≤ num / den := by
  sorry

theorem lt_ofIntFdivWithPrec (num den prec : ℤ) :
    num / den < (ofIntFdivWithPrec num den prec + step prec).toRat := by
  sorry

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
      (∏ j ∈ Finset.Ico i b, (2 * j + 3) * den ^ 2) := by
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
  let (P1, Q1) : ℕ × ℕ := Dyadic.smallArtanh 1 17 ((prec + 7) / 8)
  let (P2, Q2) : ℕ × ℕ := Dyadic.smallArtanh 1 19 ((prec + 7) / 8)
  let (P3, Q3) : ℕ × ℕ := Dyadic.smallArtanh 1 31 ((prec + 8) / 9)
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
  have hartanh17 := smallArtanh_def_aux_real 1 17 ((prec + 7) / 8)
  have hartanh19 := smallArtanh_def_aux_real 1 19 ((prec + 7) / 8)
  have hartanh31 := smallArtanh_def_aux_real 1 31 ((prec + 8) / 9)
  have hartanh17₀ := smallArtanh.den_nonzero 1 17 ((prec + 7) / 8) (by simp)
  have hartanh19₀ := smallArtanh.den_nonzero 1 19 ((prec + 7) / 8) (by simp)
  have hartanh31₀ := smallArtanh.den_nonzero 1 31 ((prec + 8) / 9) (by simp)
  set artanh17 : ℕ × ℕ := Dyadic.smallArtanh 1 17 ((prec + 7) / 8)
  set artanh19 : ℕ × ℕ := Dyadic.smallArtanh 1 19 ((prec + 7) / 8)
  set artanh31 : ℕ × ℕ := Dyadic.smallArtanh 1 31 ((prec + 8) / 9)
  simp only at *
  rw [show (1 / 2 : ℝ) ^ prec = (6 + 4 + 4) * (1 / 2) ^ (prec + 4) + (1 / 2) ^ (prec + 3 : ℤ) by
    norm_cast; ring]
  refine abs_sub_le _ _ _ |>.trans_lt <|
    add_lt_add_of_lt_of_le ?_ <| abs_ofIntFdivWithPrec_le_pow _ _ _
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [log_two_aux, ← sub_sub, ← sub_sub, add_sub_right_comm, add_sub_right_comm,
    add_sub_right_comm (6 * _), ← mul_sub, add_sub_assoc, ← mul_sub, add_sub_assoc, ← mul_sub]
  grw [abs_add_le, abs_add_le, _root_.add_mul, _root_.add_mul]
  repeat rw [abs_mul, Nat.abs_ofNat]
  gcongr <;> [rw [hartanh17]; rw [hartanh19]; rw [hartanh31]]
  <;> grw [Nat.cast_one, Nat.cast_ofNat, abs_artanh_sub_le (by grind), abs_of_pos (by simp)]
  · sorry
  · sorry
  · sorry

theorem log_two_lt (prec : ℕ) :
    (Dyadic.log_two prec).toRat < log 2 := by
  unfold Dyadic.log_two
  have hartanh17 := smallArtanh_def_aux_real 1 17 ((prec + 7) / 8)
  have hartanh19 := smallArtanh_def_aux_real 1 19 ((prec + 7) / 8)
  have hartanh31 := smallArtanh_def_aux_real 1 31 ((prec + 8) / 9)
  have hartanh17₀ := smallArtanh.den_nonzero 1 17 ((prec + 7) / 8) (by simp)
  have hartanh19₀ := smallArtanh.den_nonzero 1 19 ((prec + 7) / 8) (by simp)
  have hartanh31₀ := smallArtanh.den_nonzero 1 31 ((prec + 8) / 9) (by simp)
  set artanh17 : ℕ × ℕ := Dyadic.smallArtanh 1 17 ((prec + 7) / 8)
  set artanh19 : ℕ × ℕ := Dyadic.smallArtanh 1 19 ((prec + 7) / 8)
  set artanh31 : ℕ × ℕ := Dyadic.smallArtanh 1 31 ((prec + 8) / 9)
  simp only at *
  grw [ofIntFdivWithPrec_le]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Rat.cast_natCast, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    add_div]
  conv in _ + _ => congr; congr; all_goals field_simp; rw [mul_div_assoc]
  rw [hartanh17, hartanh19, hartanh31]
  iterate 3 grw [sum_lt_of_pos (by norm_num)]
  simp only [Nat.cast_one, Nat.cast_ofNat, log_two_aux, le_rfl]

theorem lt_log_two (prec : ℕ) :
    log 2 < (Dyadic.log_two prec).toRat + (Dyadic.step prec).toReal := by
  rw [toReal_step prec, zpow_natCast]
  grind [abs_sub_lt_iff, abs_log_two_sub_lt prec]

end SmallArtanh

section Log

/-- Assuming `x ∈ [1, 2)`, we have `(x - 1) / (x + 1) ∈ [0, 1 / 3)` and
`∀ x ∈ (1, 2), log x = 2 * artanh ((x - 1) / (x + 1)) > the sum`.
With `|log x - sum| < ulp`, this computes the lower bound `l : Dyadic`.

The error `δ ≤ 2 * x ^ (2 * n + 1) / (1 - x ^ 2) < 3 / 4 * (1 / 9) ^ n ≤ (1 / 2) ^ prec`
requires `n ≥ ((prec - 2) * log 2 + log 3) / (2 * log 3)`.
Choosing `prec / 3 : ℝ` is good enough.
-/
protected def logSum (x : Dyadic) (prec : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | ofOdd n _ _ =>
    let e : ℕ := n.natAbs.log2
    let m : ℕ := n.natAbs
    -- Dyadic.smallArtanh -> δ₁ < (1 / 2) ^ (prec + 2)
    let (P, Q) : ℕ × ℕ := Dyadic.smallArtanh (m - 2 ^ e) (m + 2 ^ e) ((prec + 2) / 3)
    -- ofIntFdivWithPrec -> δ₂ ≤ (1 / 2) ^ (prec + 2)
    -- δ ≤ 2 * (δ₁ + δ₂) < (1 / 2) ^ prec
    2 * ofIntFdivWithPrec P Q (prec + 2)

/-- Computes the lower bound for `log x`. -/
def lowerLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if |x| = 1 then 0 else
  match x with
  | zero => 0
  | ofOdd n p hn =>
    let k : ℤ := n.natAbs.log2 - p -- `k ≥ 0 ↔ |x| ≥ 1`
    let x' : Dyadic := .ofOdd n n.natAbs.log2 hn -- `|x'| ∈ [1, 2)`
    let wp : ℕ := prec + k.natAbs.log2 + 1
    if k ≥ 0 then
      Dyadic.logSum x' (prec + 1) + k * Dyadic.log_two wp
    else
      Dyadic.logSum x' (prec + 1) + k * (Dyadic.log_two wp + Dyadic.step wp)

/-- Computes the upper bound for `log x`. -/
def upperLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if |x| = 1 ∨ x = 0 then 0 else lowerLog x prec + Dyadic.step prec

theorem lowerLog_lt {x : Dyadic} (hx : 0 < x ∧ |x| ≠ 1) (prec : ℕ) :
    (x.lowerLog prec).toReal < x.toReal.log := by
  unfold lowerLog
  match x with
  | zero => simp at hx
  | ofOdd n k hn =>
    simp [hx]
    sorry

theorem lowerLog_le (x : Dyadic) (prec : ℕ) :
    (x.lowerLog prec).toReal ≤ x.toReal.log := by
  by_cases hx : 0 < x ∧ |x| ≠ 1
  · exact lowerLog_lt hx prec |>.le
  · sorry

theorem abs_lowerLog_lt (x : Dyadic) (prec : ℕ) :
    |x.toReal.log - (x.lowerLog prec).toReal| < (Dyadic.step prec).toReal := by
  sorry

theorem le_upperLog (x : Dyadic) (prec : ℕ) :
    x.toReal.log ≤ (x.upperLog prec).toReal := by
  unfold upperLog
  by_cases hx : |x| = 1 ∨ x = 0
  · simp [hx]
    rw [log_eq_zero.mpr]
    sorry
  · simp [hx]
    grind [abs_lowerLog_lt x prec]

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
