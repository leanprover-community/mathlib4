/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Exponential enclosures for interval_dyadic_real

The scalar computation uses range reduction, fixed-point Taylor evaluation, and rounded repeated
squaring. It computes a lower approximation and an error bound together, rather than evaluating
separate lower and upper Taylor series. Small computations use Horner evaluation. Larger ones use
rectangular splitting with shared powers, or binary splitting for high-precision short inputs.
-/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

/-- Binary search for the highest set bit between two known bounds. -/
def expLogSearch : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lb, _ => lb
  | fuel + 1, n, lb, ub =>
    if ub ≤ lb + 1 then lb else
      let mid := (lb + ub) / 2
      if n >>> mid = 0 then expLogSearch fuel n lb mid
      else expLogSearch fuel n mid ub

private theorem expLogSearch_eq (fuel n lb ub : ℕ) (hn : n ≠ 0)
    (hl : lb ≤ n.log2) (hu : n.log2 < ub) (hf : ub - lb ≤ 2 ^ fuel) :
    expLogSearch fuel n lb ub = n.log2 := by
  induction fuel generalizing lb ub with
  | zero => simp only [expLogSearch]; norm_num at hf; omega
  | succ fuel ih =>
    rw [expLogSearch]
    simp only []
    split_ifs with hstop hmid
    · omega
    · have hmid' : n.log2 < (lb + ub) / 2 := by
        apply (Nat.log2_lt hn).mpr
        simpa [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] using hmid
      apply ih _ _ hl hmid'
      rw [pow_succ] at hf
      omega
    · have hmid' : (lb + ub) / 2 ≤ n.log2 := by
        apply (Nat.le_log2 hn).mpr
        have : ¬n < 2 ^ ((lb + ub) / 2) := by
          simpa [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] using hmid
        omega
      apply ih _ _ hmid' hu
      rw [pow_succ] at hf
      omega

/-- Bracket the highest set bit by doubling the shift count, then use binary search. -/
def expLogBracket : ℕ → ℕ → ℕ → ℕ
  | 0, _, ub => ub
  | fuel + 1, n, ub =>
    if n >>> ub = 0 then expLogSearch (ub.log2 + 1) n (ub / 2) ub
    else expLogBracket fuel n (2 * ub)

private theorem expLogBracket_eq (fuel n ub : ℕ) (hn : n ≠ 0) (hu : 0 < ub)
    (hl : ub / 2 ≤ n.log2) (hpos : 0 < fuel) (hf : n.log2 < ub + fuel - 1) :
    expLogBracket fuel n ub = n.log2 := by
  induction fuel generalizing ub with
  | zero => omega
  | succ fuel ih =>
    rw [expLogBracket]
    split_ifs with h
    · apply expLogSearch_eq _ _ _ _ hn hl
      · exact (Nat.log2_lt hn).mpr <|
          (by simpa [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] using h)
      · apply (Nat.sub_le _ _).trans
        exact ((Nat.log2_lt (by omega : ub ≠ 0)).mp (Nat.lt_succ_self _)).le
    · have hub : ub ≤ n.log2 := by
        apply (Nat.le_log2 hn).mpr
        have : ¬n < 2 ^ ub := by
          simpa [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] using h
        omega
      apply ih
      · omega
      · simpa using hub
      · omega
      · omega

/-- The bit length, without the one-bit-per-call recursion of the logical `Nat.log2`. -/
def expBitLength (n : ℕ) : ℕ :=
  if n = 0 then 0 else expLogBracket n n 1 + 1

theorem expBitLength_eq (n : ℕ) : expBitLength n = if n = 0 then 0 else n.log2 + 1 := by
  by_cases hn : n = 0
  · simp [expBitLength, hn]
  · rw [expBitLength, ite_eq_right hn, ite_eq_right hn,
      expLogBracket_eq _ _ _ hn (by decide) (by simp) (by omega)]
    simpa using (Nat.log2_lt hn).mpr (Nat.lt_two_pow_self (n := n))

/-- The sum of `⌊log₂ k⌋` for `1 ≤ k ≤ n`, a lower bound for `log₂ (n!)`. -/
def expFactorialBits (n : ℕ) : ℕ :=
  let k := n.log2
  k * (n + 1) + 2 - (1 <<< (k + 1))

private theorem expFactorialBits_sub_le (n : ℕ) :
    2 ^ (n.log2 + 1) ≤ n.log2 * (n + 1) + 2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hp := Nat.log2_self_le hn
  rcases hk : n.log2 with _ | _ | k
  · simp
  · simp at hp ⊢
    omega
  · rw [pow_succ]
    rw [hk] at hp
    nlinarith

private theorem expFactorialBits_succ (n : ℕ) :
    expFactorialBits (n + 1) = expFactorialBits n + (n + 1).log2 := by
  by_cases hn : n = 0
  · simp [hn, expFactorialBits, Nat.log2_def]
  have hlo := Nat.log2_self_le hn
  have hhi := Nat.lt_log2_self (n := n)
  have hsub := expFactorialBits_sub_le n
  have hsub' := expFactorialBits_sub_le (n + 1)
  have ha : expFactorialBits n + 2 ^ (n.log2 + 1) = n.log2 * (n + 1) + 2 := by
    simp only [expFactorialBits, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.sub_add_cancel hsub
  have hb : expFactorialBits (n + 1) + 2 ^ ((n + 1).log2 + 1) =
      (n + 1).log2 * (n + 1 + 1) + 2 := by
    simp only [expFactorialBits, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.sub_add_cancel hsub'
  by_cases h : n + 1 = 2 ^ (n.log2 + 1)
  · have hlog : (n + 1).log2 = n.log2 + 1 := by rw [h, Nat.log2_two_pow]
    rw [hlog, pow_succ] at hb
    rw [hlog]
    nlinarith
  · have hlog : (n + 1).log2 = n.log2 :=
      (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
    rw [hlog] at hb ⊢
    nlinarith

theorem two_pow_expFactorialBits_le (n : ℕ) : 2 ^ expFactorialBits n ≤ n.factorial := by
  induction n with
  | zero => simp [expFactorialBits]
  | succ n ih =>
    rw [expFactorialBits_succ, pow_add, Nat.factorial_succ]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul ih (Nat.log2_self_le (by omega : n + 1 ≠ 0))

/-- Search for the first term whose doubled bound is at most `2⁻prec`. -/
def expTermSearch (prec reduction : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, ub => ub
  | fuel + 1, lb, ub =>
    if ub ≤ lb + 1 then ub else
      let mid := (lb + ub) / 2
      if prec + 1 ≤ mid * reduction + expFactorialBits mid then
        expTermSearch prec reduction fuel lb mid
      else expTermSearch prec reduction fuel mid ub

private theorem expTermSearch_spec (prec reduction fuel lb ub : ℕ)
    (hu : prec + 1 ≤ ub * reduction + expFactorialBits ub) :
    prec + 1 ≤ expTermSearch prec reduction fuel lb ub * reduction +
      expFactorialBits (expTermSearch prec reduction fuel lb ub) := by
  induction fuel generalizing lb ub with
  | zero => exact hu
  | succ fuel ih =>
    simp only [expTermSearch]
    split_ifs with hstop hmid
    · exact hu
    · exact ih _ _ hmid
    · exact ih _ _ hu

/-- The first omitted Taylor term for an argument in `[0, 2⁻reduction]`, with `reduction ≥ 1`. -/
def expTerms (prec reduction : ℕ) : ℕ :=
  let ub := (prec + reduction) / reduction
  expTermSearch prec reduction (ub.log2 + 1) 0 ub

theorem expTerms_spec (prec reduction : ℕ) (hr : 0 < reduction) :
    prec + 1 ≤ expTerms prec reduction * reduction +
      expFactorialBits (expTerms prec reduction) := by
  apply expTermSearch_spec
  have hmod := Nat.mod_lt (prec + reduction) hr
  have hdiv := Nat.mod_add_div (prec + reduction) reduction
  rw [Nat.mul_comm reduction] at hdiv
  omega

theorem expTerms_pos (prec reduction : ℕ) (hr : 0 < reduction) :
    0 < expTerms prec reduction := by
  have h := expTerms_spec prec reduction hr
  by_contra hzero
  have hz : expTerms prec reduction = 0 := by omega
  simp [hz, expFactorialBits] at h

private theorem expTerms_tail {x : ℝ} (prec reduction : ℕ) (hr : 0 < reduction)
    (hx : 0 ≤ x) (hxr : x ≤ 1 / 2 ^ reduction) :
    2 ^ prec * (x ^ expTerms prec reduction / (expTerms prec reduction).factorial) ≤ 1 / 2 := by
  let n := expTerms prec reduction
  have hden : (2 : ℝ) ^ (prec + 1) ≤ 2 ^ (n * reduction) * n.factorial := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (expTerms_spec prec reduction hr)
    rw [pow_add (2 : ℕ) (expTerms prec reduction * reduction)] at h
    exact_mod_cast h.trans (Nat.mul_le_mul_left _ (two_pow_expFactorialBits_le n))
  have hpow : x ^ n ≤ (1 : ℝ) / 2 ^ (n * reduction) := by
    simpa [div_pow, ← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ hx hxr n
  calc
    2 ^ prec * (x ^ n / n.factorial) ≤
        2 ^ prec * ((1 / 2 ^ (n * reduction)) / n.factorial) := by gcongr
    _ = 2 ^ prec * (1 / (2 ^ (n * reduction) * n.factorial)) := by field
    _ ≤ 2 ^ prec * (1 / 2 ^ (prec + 1)) := by gcongr
    _ = 1 / 2 := by rw [pow_succ]; field

private theorem expTerms_bounds {x : ℝ} (prec reduction : ℕ) (hr : 0 < reduction)
    (hx : 0 ≤ x) (hxr : x ≤ 1 / 2 ^ reduction) :
    let n := expTerms prec reduction
    2 ^ prec * Real.expNear n x 0 ≤ 2 ^ prec * Real.exp x ∧
      2 ^ prec * Real.exp x ≤ 2 ^ prec * Real.expNear n x 0 + 1 := by
  dsimp only
  let n := expTerms prec reduction
  have hn := expTerms_pos prec reduction hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hxf : x ≤ 1 := hxr.trans (by
    rw [div_le_iff₀ (by positivity)]
    simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ reduction))
  have hlo := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx n)
    (by positivity : (0 : ℝ) ≤ 2 ^ prec)
  constructor
  · simpa [Real.expNear] using hlo
  · have hhi := mul_le_mul_of_nonneg_left (Real.exp_bound' hx hxf hn)
      (by positivity : (0 : ℝ) ≤ 2 ^ prec)
    have ht := expTerms_tail prec reduction hr hx hxr
    have hratio : ((n : ℝ) + 1) / n ≤ 2 := by rw [div_le_iff₀ hn']; norm_cast; omega
    have htail : 2 ^ prec * (x ^ n * (n + 1) / (n.factorial * n)) ≤ 1 := calc
      _ = (2 ^ prec * (x ^ n / n.factorial)) * ((n + 1) / n) := by field
      _ ≤ (1 / 2 : ℝ) * 2 := mul_le_mul ht hratio (by positivity) (by positivity)
      _ = 1 := by norm_num
    simpa [Real.expNear] using (hhi.trans (by nlinarith only [htail]))

/-- Downward-rounded Taylor evaluation at `num / 2^exponent` by Horner's rule. -/
def expHorner (num exponent scale : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => expHorner num exponent scale n
      (scale + ((num * acc) >>> exponent) / (n + 1))

private theorem nat_div_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d < (n / d : ℕ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self n d
  · rw [div_lt_iff₀ hd']
    rw [mul_comm]
    exact_mod_cast Nat.lt_mul_div_succ n hd

private theorem shift_bounds (n p : ℕ) :
    ((n >>> p : ℕ) : ℝ) ≤ (n : ℝ) / 2 ^ p ∧
      (n : ℝ) / 2 ^ p < (n >>> p : ℕ) + 1 := by
  simpa [Nat.shiftRight_eq_div_pow] using nat_div_bounds n (2 ^ p) (by positivity)

private theorem expNear_scaled_sub (n : ℕ) (x s a b : ℝ) (hs : s ≠ 0) :
    s * Real.expNear n x (a / s) - s * Real.expNear n x (b / s) =
      x ^ n / n.factorial * (a - b) := by
  rw [← mul_sub, Real.expNear_sub, ← sub_div]
  field

private theorem expNear_scaled_succ (n : ℕ) (x s a : ℝ) (hs : s ≠ 0) :
    s * Real.expNear (n + 1) x (a / s) =
      s * Real.expNear n x ((s + x * a / (n + 1)) / s) := by
  rw [Real.expNear_succ]
  congr 2
  field

private theorem expHorner_bounds (num exponent scale n acc : ℕ) (hs : 0 < scale) :
    let x : ℝ := num / 2 ^ exponent
    (expHorner num exponent scale n acc : ℝ) ≤
        scale * Real.expNear n x (acc / scale) ∧
      scale * Real.expNear n x (acc / scale) ≤
        expHorner num exponent scale n acc +
          ∑ i ∈ Finset.range n, x ^ i / i.factorial := by
  dsimp only
  have hs' : (scale : ℝ) ≠ 0 := by positivity
  have hx : (0 : ℝ) ≤ num / 2 ^ exponent := by positivity
  induction n generalizing acc with
  | zero => simp [expHorner, mul_div_cancel₀, hs']
  | succ n ih =>
    let next := scale + ((num * acc) >>> exponent) / (n + 1)
    have hi := ih next
    have hr := nat_div_bounds (num * acc) (2 ^ exponent * (n + 1)) (by positivity)
    simp only [← Nat.div_div_eq_div_mul, ← Nat.shiftRight_eq_div_pow] at hr
    have hd := expNear_scaled_sub n ((num : ℝ) / 2 ^ exponent) scale
      ((scale : ℝ) + (num : ℝ) / 2 ^ exponent * acc / (n + 1)) next hs'
    have hp : (0 : ℝ) ≤ ((num : ℝ) / 2 ^ exponent) ^ n / n.factorial := by positivity
    have hr' : (next : ℝ) ≤ scale + (num : ℝ) / 2 ^ exponent * acc / (n + 1) ∧
        (scale : ℝ) + (num : ℝ) / 2 ^ exponent * acc / (n + 1) ≤ next + 1 := by
      dsimp [next]
      push_cast at hr ⊢
      rw [show (num : ℝ) * acc / (2 ^ exponent * (n + 1)) =
        (num : ℝ) / 2 ^ exponent * acc / (n + 1) by field] at hr
      constructor <;> linarith [hr.1, hr.2]
    rw [expHorner, expNear_scaled_succ _ _ _ _ hs', Finset.sum_range_succ]
    constructor
    · apply hi.1.trans
      apply sub_nonneg.mp
      rw [hd]
      exact mul_nonneg hp (sub_nonneg.mpr hr'.1)
    · have hround := mul_le_mul_of_nonneg_left
        (show (scale : ℝ) + (num : ℝ) / 2 ^ exponent * acc / (n + 1) - next ≤ 1 by
          linarith only [hr'.2]) hp
      linarith only [hi.2, hd, hround]

/-- Cache downward-rounded powers in descending order. -/
def expPowers (num exponent : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, result => result
  | n + 1, last, result =>
    let next := (last * num) >>> exponent
    expPowers num exponent n next (next :: result)

/-- Exact fixed-point powers in the descending order used by `expPowers`. -/
private noncomputable def expPowerList (x s : ℝ) (n : ℕ) : List ℝ :=
  (List.range n).reverse.map (fun k => s * x ^ k)

private theorem expPowerList_zero (x s : ℝ) : expPowerList x s 0 = [] := by
  simp [expPowerList]

private theorem expPowerList_succ (x s : ℝ) (n : ℕ) :
    expPowerList x s (n + 1) = s * x ^ n :: expPowerList x s n := by
  simp [expPowerList, List.range_succ]

private theorem expPowerList_drop (x s : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (expPowerList x s (n + 1)).drop (n - k) = expPowerList x s (k + 1) := by
  simp [expPowerList, List.drop_reverse, ← List.map_take, List.take_range, hk, Nat.add_comm]

private theorem expPowers_spec (num exponent scale n done last : ℕ) (result : List ℕ)
    (hx : (num : ℝ) / 2 ^ exponent ≤ 1 / 4)
    (hlast : (last : ℝ) ≤ scale * ((num : ℝ) / 2 ^ exponent) ^ done ∧
      (scale : ℝ) * ((num : ℝ) / 2 ^ exponent) ^ done ≤ last + 2)
    (hresult : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
      result (expPowerList ((num : ℝ) / 2 ^ exponent) scale (done + 1))) :
    List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
      (expPowers num exponent n last result)
      (expPowerList ((num : ℝ) / 2 ^ exponent) scale (done + n + 1)) := by
  have hx0 : (0 : ℝ) ≤ num / 2 ^ exponent := by positivity
  induction n generalizing done last result with
  | zero => simpa [expPowers] using hresult
  | succ n ih =>
    let next := (last * num) >>> exponent
    have hr := shift_bounds (last * num) exponent
    push_cast at hr
    rw [show (last : ℝ) * num / 2 ^ exponent = last * ((num : ℝ) / 2 ^ exponent) by field] at hr
    have hnext : (next : ℝ) ≤ scale * ((num : ℝ) / 2 ^ exponent) ^ (done + 1) ∧
        (scale : ℝ) * ((num : ℝ) / 2 ^ exponent) ^ (done + 1) ≤ next + 2 := by
      rw [pow_succ]
      constructor
      · exact hr.1.trans (by nlinarith [mul_le_mul_of_nonneg_right hlast.1 hx0])
      · dsimp [next]
        nlinarith [mul_le_mul_of_nonneg_right hlast.2 hx0, hr.2]
    have hresult' : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
        (next :: result) (expPowerList ((num : ℝ) / 2 ^ exponent) scale (done + 1 + 1)) := by
      rw [expPowerList_succ]
      exact .cons hnext hresult
    simpa [expPowers, next, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (done + 1) next (next :: result) hnext hresult'

private theorem expPowers_bounds (num exponent scale n : ℕ)
    (hx : (num : ℝ) / 2 ^ exponent ≤ 1 / 4) :
    List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
      (expPowers num exponent n scale [scale])
      (expPowerList ((num : ℝ) / 2 ^ exponent) scale (n + 1)) := by
  simpa using expPowers_spec num exponent scale n 0 scale [scale] hx
    (by simp) (by simp [expPowerList_succ, expPowerList_zero])

/-- Form a Taylor block with a common denominator from powers in descending order. -/
def expBlock : List ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], _, den, acc => (den, acc)
  | p :: ps, n, den, acc =>
    let den := den * n
    expBlock ps (n - 1) den (acc + den * p)

/-- The real-valued block computation before integer rounding. -/
private noncomputable def expBlockValue : List ℝ → ℕ → ℝ → ℝ
  | [], _, acc => acc
  | p :: ps, n, acc => expBlockValue ps (n - 1) (p + acc / n)

private theorem expBlock_spec (powers : List ℕ) (n den acc : ℕ)
    (hn : powers.length ≤ n) (hd : 0 < den) :
    let result := expBlock powers n den acc
    0 < result.1 ∧ (result.2 : ℝ) / result.1 =
      expBlockValue (powers.map (fun (n : ℕ) => (n : ℝ))) n ((acc : ℝ) / den) := by
  dsimp only
  induction powers generalizing n den acc with
  | nil => simpa [expBlock, expBlockValue] using hd
  | cons p ps ih =>
    have hn0 : 0 < n := by simpa using (lt_of_lt_of_le (by simp) hn)
    have hd' : (den : ℝ) ≠ 0 := by positivity
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [expBlock]
    have h := ih (n - 1) (den * n) (acc + den * n * p) (by simpa using Nat.le_sub_one_of_lt hn)
      (Nat.mul_pos hd hn0)
    refine ⟨h.1, h.2.trans ?_⟩
    simp only [List.map_cons, expBlockValue]
    congr 1
    push_cast
    field

private theorem expBlock_add (powers : List ℕ) (n den acc extra : ℕ) :
    expBlock powers n den (acc + extra) =
      ((expBlock powers n den acc).1, (expBlock powers n den acc).2 + extra) := by
  induction powers generalizing n den acc with
  | nil => rfl
  | cons p ps ih =>
    simpa [expBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (n - 1) (den * n) (acc + den * n * p)

private theorem expBlockValue_bounds {powers : List ℕ} {values : List ℝ} (n : ℕ)
    (hn : powers.length ≤ n)
    (h : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2) powers values)
    (a b : ℝ) (hab : a ≤ b ∧ b ≤ a + 5) :
    expBlockValue (powers.map (fun (n : ℕ) => (n : ℝ))) n a ≤ expBlockValue values n b ∧
      expBlockValue values n b ≤ expBlockValue (powers.map (fun (n : ℕ) => (n : ℝ))) n a + 7 := by
  induction h generalizing n a b with
  | nil => simp only [List.map_nil, expBlockValue]; constructor <;> linarith only [hab.1, hab.2]
  | @cons p q ps qs hp h ih =>
    have hn0 : 0 < n := by simpa using (lt_of_lt_of_le (by simp) hn)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    by_cases hn1 : n = 1
    · have hps : ps = [] := List.length_eq_zero_iff.mp (by simp_all)
      have hqs : qs = [] := List.length_eq_zero_iff.mp (by simpa [hps] using h.length_eq.symm)
      subst n ps qs
      simp only [List.map_cons, List.map_nil, expBlockValue, Nat.cast_one, div_one]
      constructor <;> linarith only [hp.1, hp.2, hab.1, hab.2]
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      have hd : b / n ≤ a / n + 5 / n := by
        simpa [add_div] using div_le_div_of_nonneg_right hab.2 hn'.le
      have hsmall : (5 : ℝ) / n ≤ 3 := by rw [div_le_iff₀ hn']; linarith
      have hnew : (p : ℝ) + a / n ≤ q + b / n ∧
          q + b / n ≤ (p : ℝ) + a / n + 5 := by
        constructor
        · exact add_le_add hp.1 (div_le_div_of_nonneg_right hab.1 hn'.le)
        · linarith only [hp.2, hd, hsmall]
      simpa [expBlockValue] using ih (n - 1) (by simp at hn ⊢; omega) _ _ hnew

private theorem expBlockValue_near (len n : ℕ) (x s a : ℝ) (hs : s ≠ 0) (hn : len ≤ n) :
    s * Real.expNear n x (a / s) =
      s * Real.expNear (n - len) x
        (expBlockValue (expPowerList x s len) n (x ^ len * a) / s) := by
  induction len generalizing n a with
  | zero => simp [expPowerList_zero, expBlockValue]
  | succ len ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [expPowerList_succ, expBlockValue]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_sub_add_right,
      Nat.cast_add, Nat.cast_one]
    rw [expNear_scaled_succ _ _ _ _ hs]
    rw [show s * x ^ len + x ^ (len + 1) * a / (n + 1) =
      x ^ len * (s + x * a / (n + 1)) by rw [pow_succ]; field]
    exact ih _ _ (by omega)

private theorem expBlockValue_upper (len n : ℕ) (x s a : ℝ) (hn : len ≤ n)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (hs : 0 ≤ s) (ha0 : 0 ≤ a) (ha : a ≤ 2 * s) :
    0 ≤ expBlockValue (expPowerList x s len) n (x ^ len * a) ∧
      expBlockValue (expPowerList x s len) n (x ^ len * a) ≤ 2 * s := by
  induction len generalizing n a with
  | zero => simpa [expPowerList_zero, expBlockValue] using And.intro ha0 ha
  | succ len ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [expPowerList_succ, expBlockValue]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [show s * x ^ len + x ^ (len + 1) * a / (n + 1) =
      x ^ len * (s + x * a / (n + 1)) by rw [pow_succ]; field]
    apply ih _ _ (by omega) (by positivity)
    have hb : x * a / (n + 1) ≤ x * a :=
      div_le_self (mul_nonneg hx0 ha0) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith [mul_le_mul hx ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]

private theorem expRoundedBlock_bounds (powers : List ℕ) (prec len n acc : ℕ) (x : ℝ)
    (hlen : len ≤ n) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4)
    (ha : (acc : ℝ) ≤ 2 * 2 ^ prec)
    (hp : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
      powers (expPowerList x (2 ^ prec) (len + 1))) :
    let result := expBlock powers.tail n 1 0
    let next := (result.2 + ((powers.head! * acc) >>> prec)) / result.1
    let ideal := expBlockValue (expPowerList x (2 ^ prec) len) n (x ^ len * acc)
    (next : ℝ) ≤ ideal ∧ ideal ≤ next + 8 ∧ (next : ℝ) ≤ 2 * 2 ^ prec := by
  rw [expPowerList_succ] at hp
  obtain ⟨head, tail, hhead, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hp
  simp only [List.tail_cons, List.head!_cons]
  have hs : (0 : ℝ) < 2 ^ prec := by positivity
  have hlen' : tail.length ≤ n := by
    have h : tail.length = len := by simpa [expPowerList] using htail.length_eq
    omega
  let first := (head * acc) >>> prec
  have hf := shift_bounds (head * acc) prec
  push_cast at hf
  have hf' : (first : ℝ) ≤ x ^ len * acc ∧ x ^ len * acc ≤ first + 5 := by
    constructor
    · apply (mul_le_mul_iff_left₀ hs).mp
      have h1 := (le_div_iff₀ hs).mp hf.1
      have h2 := mul_le_mul_of_nonneg_right hhead.1 (Nat.cast_nonneg (α := ℝ) acc)
      dsimp [first]
      nlinarith only [h1, h2]
    · apply (mul_le_mul_iff_left₀ hs).mp
      have h1 := (div_lt_iff₀ hs).mp hf.2
      have h2 := mul_le_mul_of_nonneg_right hhead.2 (Nat.cast_nonneg (α := ℝ) acc)
      dsimp [first]
      nlinarith only [h1, h2, ha]
  have hblock := expBlock_spec tail n 1 first hlen' (by decide)
  have hadd := expBlock_add tail n 1 0 first
  simp only [Nat.zero_add] at hadd
  rw [hadd] at hblock
  simp only [Nat.cast_one, div_one] at hblock
  have hclose := expBlockValue_bounds n hlen' htail first (x ^ len * acc) hf'
  rw [← hblock.2] at hclose
  have hround := nat_div_bounds ((expBlock tail n 1 0).2 + first)
    (expBlock tail n 1 0).1 hblock.1
  have hu := expBlockValue_upper len n x (2 ^ prec) acc hlen hx0 hx (by positivity)
    (by positivity) ha
  refine ⟨hround.1.trans hclose.1, ?_, (hround.1.trans hclose.1).trans hu.2⟩
  linarith only [hround.2, hclose.2]

/-- Evaluate Taylor blocks with one full-width multiplication and one division per block. -/
def expRectangular (powers : List ℕ) (prec blockSize : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else
      let len := min blockSize n
      let powers := if len = blockSize then powers else powers.drop (blockSize - len)
      let (den, sum) := expBlock powers.tail n 1 0
      let next := (sum + ((powers.head! * acc) >>> prec)) / den
      expRectangular powers prec blockSize fuel (n - len) next

private theorem expRectangular_zero (powers : List ℕ) (prec blockSize fuel acc : ℕ) :
    expRectangular powers prec blockSize fuel 0 acc = acc := by
  cases fuel <;> simp [expRectangular]

private theorem expRectangular_bounds (powers : List ℕ) (prec blockSize fuel n acc : ℕ) (x : ℝ)
    (hb : 0 < blockSize) (hn : n ≤ fuel * blockSize) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4)
    (ha : (acc : ℝ) ≤ 2 * 2 ^ prec)
    (hp : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
      powers (expPowerList x (2 ^ prec) (blockSize + 1))) :
    let result := expRectangular powers prec blockSize fuel n acc
    (result : ℝ) ≤ 2 ^ prec * Real.expNear n x (acc / 2 ^ prec) ∧
      2 ^ prec * Real.expNear n x (acc / 2 ^ prec) ≤
        result + 8 * ∑ i ∈ Finset.range n, x ^ i / i.factorial ∧
      (result : ℝ) ≤ 2 * 2 ^ prec := by
  dsimp only
  have hs : (0 : ℝ) < 2 ^ prec := by positivity
  induction fuel generalizing n acc with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    simpa [expRectangular, hn0, mul_div_cancel₀, hs.ne'] using ha
  | succ fuel ih =>
    by_cases hn0 : n = 0
    · simpa [hn0, expRectangular_zero, mul_div_cancel₀, hs.ne'] using ha
    let len := min blockSize n
    have hlen : len ≤ n := min_le_right _ _
    have hlenb : len ≤ blockSize := min_le_left _ _
    have hlen0 : 0 < len := lt_min hb (by omega)
    let ps := if len = blockSize then powers else powers.drop (blockSize - len)
    have hps : List.Forall₂ (fun (a : ℕ) (b : ℝ) => a ≤ b ∧ b ≤ a + 2)
        ps (expPowerList x (2 ^ prec) (len + 1)) := by
      dsimp [ps]
      split_ifs with h
      · simpa [h] using hp
      · simpa [expPowerList_drop _ _ _ _ hlenb] using List.forall₂_drop (blockSize - len) hp
    let result := expBlock ps.tail n 1 0
    let next := (result.2 + ((ps.head! * acc) >>> prec)) / result.1
    let ideal := expBlockValue (expPowerList x (2 ^ prec) len) n (x ^ len * acc)
    have hnext := expRoundedBlock_bounds ps prec len n acc x hlen hx0 hx ha hps
    have hi : (expRectangular ps prec blockSize fuel (n - len) next : ℝ) ≤
          2 ^ prec * Real.expNear (n - len) x (next / 2 ^ prec) ∧
        2 ^ prec * Real.expNear (n - len) x (next / 2 ^ prec) ≤
          expRectangular ps prec blockSize fuel (n - len) next +
            8 * ∑ i ∈ Finset.range (n - len), x ^ i / i.factorial ∧
        (expRectangular ps prec blockSize fuel (n - len) next : ℝ) ≤ 2 * 2 ^ prec := by
      by_cases hlenb' : len = blockSize
      · have hn' : n - blockSize ≤ fuel * blockSize := by
          simp only [Nat.succ_mul] at hn
          omega
        simpa [ps, hlenb'] using ih (n - len) next (by omega) hnext.2.2
      · have hz : n - len = 0 := by dsimp [len] at *; omega
        simpa [hz, expRectangular_zero, mul_div_cancel₀, hs.ne'] using hnext.2.2
    have hnear := expBlockValue_near len n x (2 ^ prec) acc hs.ne' hlen
    have hd := expNear_scaled_sub (n - len) x (2 ^ prec) ideal next hs.ne'
    have hc : 0 ≤ x ^ (n - len) / (n - len).factorial := by positivity
    have hsum : (∑ i ∈ Finset.range (n - len), x ^ i / i.factorial) +
          x ^ (n - len) / (n - len).factorial ≤ ∑ i ∈ Finset.range n, x ^ i / i.factorial := by
      rw [← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => by positivity)
    rw [expRectangular, ite_eq_right hn0]
    change (expRectangular ps prec blockSize fuel (n - len) next : ℝ) ≤ _ ∧ _
    rw [hnear]
    refine ⟨hi.1.trans ?_, ?_, hi.2.2⟩
    · apply sub_nonneg.mp
      rw [hd]
      exact mul_nonneg hc (sub_nonneg.mpr hnext.1)
    · have hround := mul_le_mul_of_nonneg_left
        (show ideal - next ≤ 8 by linarith only [hnext.2.1]) hc
      linarith only [hi.2.1, hd, hround, hsum]

/-- Form an exact Taylor block, with powers of two kept out of the denominator. -/
def expBinaryBlock (num exponent start : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, den, sum => (den, sum)
  | n + 1, done, den, sum =>
    expBinaryBlock num exponent start n (done + 1) ((start + n + 1) * den)
      (num * ((den <<< (exponent * done)) + sum))

/-- The positive-degree Taylor terms for an exact binary-splitting block. -/
private noncomputable def expTail (x : ℝ) (start n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ (i + 1) / (start + 1).ascFactorial (i + 1)

private theorem expTail_zero (x : ℝ) (start : ℕ) : expTail x start 0 = 0 := by
  simp [expTail]

private theorem expTail_succ (x : ℝ) (start n : ℕ) :
    expTail x start (n + 1) = expTail x start n +
      x ^ (n + 1) / (start + 1).ascFactorial (n + 1) := by
  simp [expTail, Finset.sum_range_succ]

private theorem expTail_add (x : ℝ) (start a b : ℕ) :
    expTail x start (a + b) = expTail x start a +
      x ^ a / (start + 1).ascFactorial a * expTail x (start + a) b := by
  simp only [expTail, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_assoc, ← Nat.ascFactorial_mul_ascFactorial]
  simp [pow_add, Nat.add_right_comm, div_mul_div_comm]

private theorem expBinaryBlock_den (num exponent start n done den sum : ℕ) :
    (expBinaryBlock num exponent start n done den sum).1 =
      den * (start + 1).ascFactorial n := by
  induction n generalizing done den sum with
  | zero => simp [expBinaryBlock]
  | succ n ih =>
    simp only [expBinaryBlock, ih, Nat.ascFactorial_succ]
    ring

private theorem expBinaryBlock_value (num exponent start n done den sum : ℕ) (hd : 0 < den) :
    let result := expBinaryBlock num exponent start n done den sum
    let x : ℝ := num / 2 ^ exponent
    (result.2 : ℝ) / result.1 / (2 ^ exponent) ^ (done + n) =
      expTail x start n + x ^ n / (start + 1).ascFactorial n *
        ((sum : ℝ) / den / (2 ^ exponent) ^ done) := by
  dsimp only
  induction n generalizing done den sum with
  | zero => simp [expBinaryBlock, expTail_zero]
  | succ n ih =>
    have hd' : (den : ℝ) ≠ 0 := by positivity
    have hf : ((start + 1).ascFactorial n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ascFactorial_pos start n).ne'
    have hk : ((start : ℝ) + n + 1) ≠ 0 := by positivity
    have ht : (2 : ℝ) ^ exponent ≠ 0 := by positivity
    rw [expBinaryBlock, show done + (n + 1) = (done + 1) + n by omega,
      ih _ _ _ (by positivity)]
    rw [expTail_succ, Nat.ascFactorial_succ]
    push_cast
    simp only [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_mul,
      pow_succ]
    field_simp
    ring

/-- Binary splitting for the Taylor series: return its common denominator and scaled numerator. -/
def expBinarySplit (num exponent : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _ => (1, 0)
  | fuel + 1, start, n =>
    if n ≤ 32 then expBinaryBlock num exponent start n 0 1 0 else
      let len := n / 2
      let (ld, ls) := expBinarySplit num exponent fuel start len
      let (rd, rs) := expBinarySplit num exponent fuel (start + len) (n - len)
      (ld * rd, ((ls * rd) <<< (exponent * (n - len))) + num ^ len * rs)

private theorem expBinarySplit_spec (num exponent fuel start n : ℕ)
    (hf : 0 < fuel) (hn : n ≤ 2 ^ fuel) :
    let result := expBinarySplit num exponent fuel start n
    result.1 = (start + 1).ascFactorial n ∧
      (result.2 : ℝ) / result.1 / (2 ^ exponent) ^ n =
        expTail ((num : ℝ) / 2 ^ exponent) start n := by
  dsimp only
  induction fuel generalizing start n with
  | zero => omega
  | succ fuel ih =>
    rw [expBinarySplit]
    split_ifs with hsmall
    · constructor
      · simp [expBinaryBlock_den]
      · simpa using expBinaryBlock_value num exponent start n 0 1 0 (by decide)
    · have hf' : 0 < fuel := by
        by_contra h
        have : fuel = 0 := by omega
        simp [this] at hn
        omega
      have hleft : n / 2 ≤ 2 ^ fuel := by rw [pow_succ] at hn; omega
      have hright : n - n / 2 ≤ 2 ^ fuel := by rw [pow_succ] at hn; omega
      have hl := ih start (n / 2) hf' hleft
      have hr := ih (start + n / 2) (n - n / 2) hf' hright
      dsimp only
      constructor
      · rw [hl.1, hr.1, show start + n / 2 + 1 = start + 1 + n / 2 by omega,
          Nat.ascFactorial_mul_ascFactorial, Nat.add_sub_of_le (Nat.div_le_self _ _)]
      · have hld : ((expBinarySplit num exponent fuel start (n / 2)).1 : ℝ) ≠ 0 := by
          rw [hl.1]
          exact_mod_cast (Nat.ascFactorial_pos start (n / 2)).ne'
        have hrd : ((expBinarySplit num exponent fuel (start + n / 2) (n - n / 2)).1 : ℝ) ≠ 0 := by
          rw [hr.1]
          exact_mod_cast (Nat.ascFactorial_pos (start + n / 2) (n - n / 2)).ne'
        have hp : ((2 : ℝ) ^ exponent) ^ n =
            (2 ^ exponent) ^ (n / 2) * (2 ^ exponent) ^ (n - n / 2) := by
          rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self _ _)]
        have ht : expTail ((num : ℝ) / 2 ^ exponent) start n =
            expTail ((num : ℝ) / 2 ^ exponent) start (n / 2) +
              ((num : ℝ) / 2 ^ exponent) ^ (n / 2) / (start + 1).ascFactorial (n / 2) *
                expTail ((num : ℝ) / 2 ^ exponent) (start + n / 2) (n - n / 2) := by
          simpa [Nat.add_sub_of_le (Nat.div_le_self n 2)] using
            expTail_add ((num : ℝ) / 2 ^ exponent) start (n / 2) (n - n / 2)
        rw [ht, ← hl.2, ← hr.2, ← hl.1]
        simp only [Nat.shiftLeft_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, pow_mul, div_pow, hp]
        field

/-- A lower exponential approximation and its error in working-grid units, for a reduced argument.
Choose Horner evaluation, rectangular splitting, or binary splitting according to the input size. -/
def expSeries (num exponent prec reduction : ℕ) : ℕ × ℕ :=
  let n := expTerms prec reduction - 1
  let scale := 1 <<< prec
  let short : Bool := num < (1 <<< 64)
  if 65536 ≤ prec && short then
    let (den, sum) := expBinarySplit num exponent (n.log2 + 2) 0 n
    let sum := if prec ≤ exponent * n then sum >>> (exponent * n - prec)
      else sum <<< (prec - exponent * n)
    (scale + sum / den, 2)
  else if prec ≤ 4096 || short then
    (expHorner num exponent scale n scale, 3)
  else
    let blockSize := max 1 n.sqrt
    let powers := expPowers num exponent blockSize scale [scale]
    (expRectangular powers prec blockSize (n / blockSize + 1) n scale, 21)

private theorem rescale_div_bounds (sum den prec exponent : ℕ) (hd : 0 < den) :
    let scaled := if prec ≤ exponent then sum >>> (exponent - prec)
      else sum <<< (prec - exponent)
    ((scaled / den : ℕ) : ℝ) ≤ 2 ^ prec * ((sum : ℝ) / den / 2 ^ exponent) ∧
      2 ^ prec * ((sum : ℝ) / den / 2 ^ exponent) < (scaled / den : ℕ) + 1 := by
  dsimp only
  split_ifs with h
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
    have he : (2 : ℝ) ^ exponent = 2 ^ prec * 2 ^ (exponent - prec) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    have hval : 2 ^ prec * ((sum : ℝ) / den / 2 ^ exponent) =
        sum / (2 ^ (exponent - prec) * den) := by rw [he]; field
    rw [hval]
    simpa using nat_div_bounds sum (2 ^ (exponent - prec) * den) (by positivity)
  · rw [Nat.shiftLeft_eq]
    have hp : (2 : ℝ) ^ prec = 2 ^ (prec - exponent) * 2 ^ exponent := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hval : 2 ^ prec * ((sum : ℝ) / den / 2 ^ exponent) =
        (sum * 2 ^ (prec - exponent)) / den := by rw [hp]; field
    rw [hval]
    simpa using nat_div_bounds (sum * 2 ^ (prec - exponent)) den hd

private theorem expTail_near (x : ℝ) (n : ℕ) :
    1 + expTail x 0 n = Real.expNear (n + 1) x 0 := by
  simp [expTail, Real.expNear, Finset.sum_range_succ', add_comm]

private theorem exp_small_bound {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x ≤ 4 / 3 := by
  apply (Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)).trans
  rw [div_le_iff₀ (by linarith : 0 < 1 - x)]
  linarith

theorem expSeries_bounds (num exponent prec reduction : ℕ) (hr : 2 ≤ reduction)
    (hx : (num : ℝ) / 2 ^ exponent ≤ 1 / 2 ^ reduction) :
    let result := expSeries num exponent prec reduction
    (result.1 : ℝ) ≤ 2 ^ prec * Real.exp ((num : ℝ) / 2 ^ exponent) ∧
      2 ^ prec * Real.exp ((num : ℝ) / 2 ^ exponent) < result.1 + result.2 := by
  let x : ℝ := num / 2 ^ exponent
  let n := expTerms prec reduction - 1
  have hn : expTerms prec reduction = n + 1 := by
    have := expTerms_pos prec reduction (by omega)
    dsimp [n]; omega
  have hx0 : 0 ≤ x := by positivity
  have hxq : x ≤ 1 / 4 := hx.trans (by
    have : (4 : ℝ) ≤ 2 ^ reduction := by
      convert (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr) using 1; norm_num
    rw [div_le_iff₀ (by positivity)]
    linarith)
  have ht := expTerms_bounds prec reduction (by omega) hx0 hx
  rw [hn] at ht
  have he := exp_small_bound hx0 hxq
  have hsum := (Real.sum_le_exp_of_nonneg hx0 n).trans he
  have hs : (0 : ℝ) < 2 ^ prec := by positivity
  have hnear : Real.expNear n x 1 = Real.expNear (n + 1) x 0 := by
    simp [Real.expNear_succ]
  dsimp [x] at hnear
  dsimp only
  unfold expSeries
  dsimp only
  split
  · have hb := expBinarySplit_spec num exponent (n.log2 + 2) 0 n (by omega)
      ((Nat.lt_log2_self (n := n)).le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [Nat.zero_add, Nat.one_ascFactorial, ← pow_mul] at hb
    have hd : 0 < (expBinarySplit num exponent (n.log2 + 2) 0 n).1 := by
      rw [hb.1]; exact Nat.factorial_pos n
    have hbround := rescale_div_bounds
      (expBinarySplit num exponent (n.log2 + 2) 0 n).2
      (expBinarySplit num exponent (n.log2 + 2) 0 n).1 prec (exponent * n) hd
    rw [hb.2] at hbround
    have hv : 2 ^ prec * (1 + expTail x 0 n) =
        2 ^ prec * Real.expNear (n + 1) x 0 := by rw [expTail_near]
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only at hbround
    simp only [Nat.shiftLeft_eq] at hbround
    constructor <;> linarith only [hbround.1, hbround.2, ht.1, ht.2, hv]
  · split
    · have hh := expHorner_bounds num exponent (1 <<< prec) n (1 <<< prec) (by
      simp [Nat.shiftLeft_eq])
      simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat,
        div_self hs.ne', hnear] at hh
      simp only [Nat.shiftLeft_eq, Nat.one_mul]
      constructor <;> push_cast <;> linarith only [hh.1, hh.2, ht.1, ht.2, hsum]
    · let blockSize := max 1 n.sqrt
      have hb : 0 < blockSize := lt_of_lt_of_le (by decide) (le_max_left _ _)
      have hf : n ≤ (n / blockSize + 1) * blockSize :=
        (by have := Nat.lt_mul_div_succ n hb; nlinarith)
      have hp := expPowers_bounds num exponent (1 <<< prec) blockSize hxq
      simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat] at hp
      have hr := expRectangular_bounds _ prec blockSize (n / blockSize + 1) n
        (1 <<< prec) x hb hf hx0 hxq (by simp [Nat.shiftLeft_eq]) hp
      dsimp [x] at hr
      simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat,
        div_self hs.ne', hnear] at hr
      simp only [Nat.shiftLeft_eq, Nat.one_mul]
      constructor <;> push_cast <;> linarith only [hr.1, hr.2.1, ht.1, ht.2, hsum]

/-- Repeatedly square a fixed-point approximation and propagate its error in working-grid units.
Each step uses one full-width square; the other products involve the smaller error bound. -/
def expSquare (prec : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, result => result
  | n + 1, (value, error) =>
    expSquare prec n ((value * value) >>> prec,
      ((2 * value * error + error * error) >>> prec) + 2)

private theorem square_bounds {x : ℝ} (hx : 0 ≤ x) (p v e : ℕ)
    (hlo : (v : ℝ) ≤ 2 ^ p * x) (hhi : 2 ^ p * x < v + e) :
    (((v * v) >>> p : ℕ) : ℝ) ≤ 2 ^ p * x ^ 2 ∧
      2 ^ p * x ^ 2 < ((v * v) >>> p : ℕ) +
        (((2 * v * e + e * e) >>> p : ℕ) + 2 : ℕ) := by
  have hs : (0 : ℝ) < 2 ^ p := by positivity
  have hv : (0 : ℝ) ≤ v := by positivity
  have he : (0 : ℝ) ≤ e := by positivity
  have hvv := shift_bounds (v * v) p
  have hee := shift_bounds (2 * v * e + e * e) p
  push_cast at hvv hee ⊢
  constructor
  · apply hvv.1.trans
    rw [div_le_iff₀ hs]
    nlinarith [sq_le_sq₀ hv (by positivity : 0 ≤ 2 ^ p * x) |>.mpr hlo]
  · have hsq : (2 ^ p * x) ^ 2 < ((v : ℝ) + e) ^ 2 := by
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr hhi
    have h1 := (div_lt_iff₀ hs).mp hvv.2
    have h2 := (div_lt_iff₀ hs).mp hee.2
    apply (mul_lt_mul_iff_left₀ hs).mp
    nlinarith

theorem expSquare_bounds (p n v e : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hlo : (v : ℝ) ≤ 2 ^ p * x) (hhi : 2 ^ p * x < v + e) :
    ((expSquare p n (v, e)).1 : ℝ) ≤ 2 ^ p * x ^ (2 ^ n) ∧
      2 ^ p * x ^ (2 ^ n) <
        (expSquare p n (v, e)).1 + (expSquare p n (v, e)).2 := by
  induction n generalizing v e x with
  | zero => simpa [expSquare] using And.intro hlo hhi
  | succ n ih =>
    have h := square_bounds hx p v e hlo hhi
    rw [expSquare, pow_succ, Nat.mul_comm (2 ^ n) 2, pow_mul]
    exact ih _ _ (sq_nonneg x) h.1 h.2

/-- Natural-number bounds for `2^prec * exp (±num / 2^exponent)`, for nonzero `num`. -/
def expNatBounds (num : ℕ) (exponent : ℤ) (negative : Bool) (prec : ℕ) : ℕ × ℕ :=
  let magnitude := (expBitLength num : ℤ) - exponent
  let scale := 1 <<< prec
  if magnitude ≤ -((prec + 1 : ℕ) : ℤ) then
    if negative then (scale - 1, scale) else (scale, scale + 1)
  else if negative && (expBitLength (prec + 1) : ℤ) < magnitude then (0, 1)
  else
    let integerPart := match exponent with
      | .ofNat n => num >>> n
      | .negSucc n => num <<< (n + 1)
    if negative && prec + 1 ≤ integerPart then (0, 1) else
      -- Since `exp 1 < 2^(3/2)`, this bounds amplification for positive inputs.
      let growth := if negative then 0 else (3 * (integerPart + 1) + 1) / 2
      let target := prec + growth + 16
      let reduction := max 2 (target.sqrt / if target < 65536 then 2 else 3)
      let reduction := if 65536 ≤ target && num < (1 <<< 64) then min 128 reduction else reduction
      let squarings := (magnitude + reduction).toNat
      let working := target + squarings
      let exponent := (exponent + squarings).toNat
      let num := if exponent ≤ working then num else num >>> (exponent - working)
      let (value, error) := expSeries num (min exponent working) working reduction
      -- Truncating the reduced argument contributes less than two working-grid units.
      let error := error + 2
      let initial := if negative then
        ((1 <<< (2 * working)) / (value + error), error + 1)
      else (value, error)
      let (value, error) := expSquare working squarings initial
      let shift := working - prec
      let ub := ((value + error - 1) >>> shift) + 1
      (value >>> shift, if negative then min ub scale else ub)

private theorem exp_sub_one_small {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x - 1 ≤ 4 / 3 * x := by
  have h := Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
  have h' : 1 / (1 - x) ≤ 1 + 4 / 3 * x := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - x)]
    nlinarith
  linarith

private theorem exp_input_rounding {x y : ℝ} (prec : ℕ)
    (hy0 : 0 ≤ y) (hxy : y ≤ x) (hx : x ≤ 1 / 4)
    (hround : 2 ^ prec * (x - y) < 1) :
    2 ^ prec * (Real.exp x - Real.exp y) < 2 := by
  have hd0 : 0 ≤ x - y := sub_nonneg.mpr hxy
  have hd := exp_sub_one_small hd0 (by linarith : x - y ≤ 1 / 4)
  have hy := exp_small_bound hy0 (hxy.trans hx)
  have he0 : 0 ≤ Real.exp (x - y) - 1 := by
    have := Real.one_le_exp_iff.mpr hd0
    linarith
  have hmul := mul_le_mul hy hd he0 (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hexp : Real.exp x - Real.exp y = Real.exp y * (Real.exp (x - y) - 1) := by
    rw [mul_sub, ← Real.exp_add]
    simp
  have hb := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 2 ^ prec)
  rw [hexp]
  nlinarith only [hb, hround]

private theorem exp_truncate_input (num exponent working : ℕ) :
    let rounded := if exponent ≤ working then num else num >>> (exponent - working)
    let y : ℝ := rounded / 2 ^ min exponent working
    y ≤ num / 2 ^ exponent ∧ 2 ^ working * (num / 2 ^ exponent - y) < 1 := by
  dsimp only
  split_ifs with h
  · simp [min_eq_left h]
  · have hle : working ≤ exponent := by omega
    rw [min_eq_right hle]
    have hs : (0 : ℝ) < 2 ^ working := by positivity
    have hpow : (2 : ℝ) ^ exponent = 2 ^ (exponent - working) * 2 ^ working := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hval : (2 : ℝ) ^ working * (num / 2 ^ exponent) =
        num / 2 ^ (exponent - working) := by rw [hpow]; field
    have hround := shift_bounds num (exponent - working)
    constructor
    · rw [div_le_iff₀ hs, mul_comm, hval]
      exact hround.1
    · rw [mul_sub, hval, mul_div_cancel₀ _ hs.ne']
      linarith only [hround.2]

private theorem exp_reduced_bounds (num exponent working reduction : ℕ)
    (hr : 2 ≤ reduction) (hx : (num : ℝ) / 2 ^ exponent ≤ 1 / 2 ^ reduction) :
    let rounded := if exponent ≤ working then num else num >>> (exponent - working)
    let result := expSeries rounded (min exponent working) working reduction
    (result.1 : ℝ) ≤ 2 ^ working * Real.exp ((num : ℝ) / 2 ^ exponent) ∧
      2 ^ working * Real.exp ((num : ℝ) / 2 ^ exponent) < result.1 + (result.2 + 2 : ℕ) := by
  dsimp only
  let rounded := if exponent ≤ working then num else num >>> (exponent - working)
  let y : ℝ := rounded / 2 ^ min exponent working
  have ht := exp_truncate_input num exponent working
  have hb := expSeries_bounds rounded (min exponent working) working reduction hr
    (ht.1.trans hx)
  have hxq : (num : ℝ) / 2 ^ exponent ≤ 1 / 4 := hx.trans (by
    have hpow : (4 : ℝ) ≤ 2 ^ reduction := by
      convert (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr) using 1; norm_num
    rw [div_le_iff₀ (by positivity)]
    linarith)
  have he := exp_input_rounding working (by positivity : 0 ≤ y) ht.1 hxq ht.2
  constructor
  · exact hb.1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.1) (by positivity))
  · push_cast
    linarith only [hb.2, he]

private theorem reciprocal_bounds (prec v e : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (hlo : (v : ℝ) ≤ 2 ^ prec * x) (hhi : 2 ^ prec * x < v + e) :
    (((1 <<< (2 * prec)) / (v + e) : ℕ) : ℝ) ≤ 2 ^ prec / x ∧
      2 ^ prec / x < ((1 <<< (2 * prec)) / (v + e) : ℕ) + (e + 1 : ℕ) := by
  have hs : (0 : ℝ) < 2 ^ prec := by positivity
  have hx0 : 0 < x := by linarith
  have hbReal : (0 : ℝ) < v + e := lt_trans (by positivity) hhi
  have hb : 0 < v + e := by exact_mod_cast hbReal
  have hb' : (0 : ℝ) < (v + e : ℕ) := by positivity
  have hr := nat_div_bounds (1 <<< (2 * prec)) (v + e) hb
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
    pow_mul, mul_comm 2 prec] at hr
  have hl : (2 ^ prec) ^ 2 / (v + e) ≤ 2 ^ prec / x := by
    rw [div_le_div_iff₀ (by exact_mod_cast hb) hx0]
    nlinarith only [mul_le_mul_of_nonneg_left hhi.le hs.le]
  have hu : 2 ^ prec / x ≤ (2 ^ prec) ^ 2 / (v + e) + e := by
    apply (div_le_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hbReal).mp
    have hbx : (2 : ℝ) ^ prec ≤ (v + e) * x := by
      have hbs : (2 : ℝ) ^ prec ≤ v + e := by nlinarith
      nlinarith [Nat.cast_nonneg (α := ℝ) e, Nat.cast_nonneg (α := ℝ) v]
    have hm := mul_le_mul_of_nonneg_left hbx (Nat.cast_nonneg (α := ℝ) e)
    have hv := mul_le_mul_of_nonneg_left hlo hs.le
    rw [show ((v : ℝ) + e) * (((2 ^ prec) ^ 2 / (v + e) + e) * x) =
      (2 ^ prec) ^ 2 * x + e * x * (v + e) by field]
    nlinarith only [hm, hv]
  simp only [Nat.shiftLeft_eq, Nat.one_mul, mul_comm 2 prec, pow_mul]
  constructor
  · exact hr.1.trans hl
  · push_cast
    linarith only [hu, hr.2]

private theorem exp_round_out (prec working v e : ℕ) {x : ℝ} (hp : prec ≤ working)
    (hx : 0 ≤ x) (hlo : (v : ℝ) ≤ 2 ^ working * x)
    (hhi : 2 ^ working * x < v + e) :
    ((v >>> (working - prec) : ℕ) : ℝ) ≤ 2 ^ prec * x ∧
      2 ^ prec * x ≤ (((v + e - 1) >>> (working - prec)) + 1 : ℕ) := by
  have hs : (0 : ℝ) < 2 ^ (working - prec) := by positivity
  have hpw : (2 : ℝ) ^ working = 2 ^ prec * 2 ^ (working - prec) := by
    rw [← pow_add, Nat.add_sub_of_le hp]
  constructor
  · apply (shift_bounds v (working - prec)).1.trans
    rw [div_le_iff₀ hs]
    rw [hpw] at hlo
    nlinarith only [hlo]
  · have hposReal : (0 : ℝ) < v + e := lt_of_le_of_lt (by positivity) hhi
    have hpos : 0 < v + e := by exact_mod_cast hposReal
    have hnat := Nat.lt_mul_div_succ (v + e - 1) (by positivity : 0 < 2 ^ (working - prec))
    have hup : v + e ≤ (((v + e - 1) >>> (working - prec)) + 1) * 2 ^ (working - prec) := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.mul_comm] at hnat
      omega
    have hup' : (v : ℝ) + e ≤
        (((v + e - 1) >>> (working - prec)) + 1 : ℕ) * (2 : ℝ) ^ (working - prec) := by
      exact_mod_cast hup
    apply (mul_le_mul_iff_right₀ hs).mp
    rw [hpw] at hhi
    nlinarith only [hhi, hup']

private theorem exp_compute_bounds (num exponent working reduction squarings prec : ℕ)
    (negative : Bool) (hr : 2 ≤ reduction) (hp : prec ≤ working)
    (hx : (num : ℝ) / 2 ^ exponent ≤ 1 / 2 ^ reduction) :
    let rounded := if exponent ≤ working then num else num >>> (exponent - working)
    let series := expSeries rounded (min exponent working) working reduction
    let error := series.2 + 2
    let initial := if negative then ((1 <<< (2 * working)) / (series.1 + error), error + 1)
      else (series.1, error)
    let result := expSquare working squarings initial
    let ub := ((result.1 + result.2 - 1) >>> (working - prec)) + 1
    let x : ℝ := 2 ^ squarings * (num / 2 ^ exponent)
    (result.1 >>> (working - prec) : ℕ) ≤ 2 ^ prec * Real.exp (if negative then -x else x) ∧
      2 ^ prec * Real.exp (if negative then -x else x) ≤
        ((if negative then min ub (1 <<< prec) else ub) : ℕ) := by
  dsimp only
  let rounded := if exponent ≤ working then num else num >>> (exponent - working)
  let series := expSeries rounded (min exponent working) working reduction
  let error := series.2 + 2
  let initial := if negative then ((1 <<< (2 * working)) / (series.1 + error), error + 1)
    else (series.1, error)
  let u : ℝ := num / 2 ^ exponent
  have hs := exp_reduced_bounds num exponent working reduction hr hx
  have hi : (initial.1 : ℝ) ≤ 2 ^ working * Real.exp (if negative then -u else u) ∧
      2 ^ working * Real.exp (if negative then -u else u) < initial.1 + initial.2 := by
    cases negative
    · exact hs
    · have h := reciprocal_bounds working series.1 error
        (Real.one_le_exp_iff.mpr (by positivity : 0 ≤ u)) hs.1 hs.2
      simpa [initial, Real.exp_neg, div_eq_mul_inv] using h
  have hsq := expSquare_bounds working squarings initial.1 initial.2
    (Real.exp_pos _).le hi.1 hi.2
  have he : Real.exp (if negative then -u else u) ^ (2 ^ squarings) =
      Real.exp (if negative then -(2 ^ squarings * u) else 2 ^ squarings * u) := by
    rw [← Real.exp_nat_mul]
    cases negative <;> simp
  rw [he] at hsq
  have ho := exp_round_out prec working
    (expSquare working squarings initial).1 (expSquare working squarings initial).2 hp
    (Real.exp_pos _).le hsq.1 hsq.2
  refine ⟨ho.1, ?_⟩
  cases negative
  · exact ho.2
  · simp only [ite_true, Nat.cast_min]
    apply le_min ho.2
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hle : Real.exp (-(2 ^ squarings * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    simpa using mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 ^ prec)

private theorem exp_magnitude_bounds (num : ℕ) (exponent : ℤ) (hn : num ≠ 0) :
    (2 : ℝ) ^ ((expBitLength num : ℤ) - exponent - 1) ≤ num / (2 : ℝ) ^ exponent ∧
      (num : ℝ) / (2 : ℝ) ^ exponent < 2 ^ ((expBitLength num : ℤ) - exponent) := by
  have hlo : (2 : ℝ) ^ ((expBitLength num : ℤ) - 1) ≤ num := by
    simp only [expBitLength_eq, ite_eq_right hn, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, zpow_natCast]
    exact_mod_cast Nat.log2_self_le hn
  have hhi : (num : ℝ) < (2 : ℝ) ^ (expBitLength num : ℤ) := by
    simp only [expBitLength_eq, ite_eq_right hn, zpow_natCast]
    exact_mod_cast (Nat.lt_log2_self (n := num))
  have he : ((expBitLength num : ℤ) - exponent - 1) =
      ((expBitLength num : ℤ) - 1) - exponent := by omega
  rw [he, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0) ((expBitLength num : ℤ) - 1) exponent,
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0) (expBitLength num : ℤ) exponent]
  exact ⟨(div_le_div_iff_of_pos_right (zpow_pos (by norm_num) exponent)).mpr hlo,
    (div_lt_div_iff_of_pos_right (zpow_pos (by norm_num) exponent)).mpr hhi⟩

private theorem exp_tiny_bounds (prec : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2 ^ (prec + 1)) :
    (2 ^ prec : ℝ) ≤ 2 ^ prec * Real.exp x ∧
      2 ^ prec * Real.exp x ≤ 2 ^ prec + 1 ∧
      (2 ^ prec - 1 : ℕ) ≤ 2 ^ prec * Real.exp (-x) ∧
      2 ^ prec * Real.exp (-x) ≤ 2 ^ prec := by
  have hs : (0 : ℝ) < 2 ^ prec := by positivity
  have hs1 : (1 : ℝ) ≤ 2 ^ prec := one_le_pow₀ (by norm_num)
  have hxsmall : x ≤ 1 / 2 := hx.trans (by rw [pow_succ, div_le_iff₀ (by positivity)]; linarith)
  have he := Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
  have he' : Real.exp x ≤ 1 + 2 * x := he.trans (by
    rw [div_le_iff₀ (by linarith : 0 < 1 - x)]
    nlinarith)
  have hxs : 2 ^ prec * x ≤ 1 / 2 := by
    rw [pow_succ, le_div_iff₀ (by positivity)] at hx
    linarith
  have hlo := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hx0) hs.le
  have hhi := mul_le_mul_of_nonneg_left he' hs.le
  have hneglo := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg x) hs.le
  have hneghi := mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)) hs.le
  have hcast : ((2 ^ prec - 1 : ℕ) : ℝ) = 2 ^ prec - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow prec 2 (by decide))]
    norm_cast
  rw [hcast]
  refine ⟨by simpa using hlo, ?_, ?_, by simpa using hneghi⟩ <;> linarith

private theorem exp_large_negative (prec : ℕ) {x : ℝ} (hx : (prec : ℝ) ≤ x) :
    2 ^ prec * Real.exp (-x) ≤ 1 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : (2 : ℝ) ^ prec ≤ Real.exp x := by
    apply (pow_le_pow_left₀ (by norm_num) htwo prec).trans
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.exp_le_exp.mpr hx
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact hexp

private theorem exp_reduction_spec (num reduction : ℕ) (exponent : ℤ) (hn : num ≠ 0) :
    let squarings := ((expBitLength num : ℤ) - exponent + reduction).toNat
    let reducedExponent := (exponent + squarings).toNat
    (num : ℝ) / 2 ^ reducedExponent ≤ 1 / 2 ^ reduction ∧
      (2 : ℝ) ^ squarings * (num / 2 ^ reducedExponent) = num / (2 : ℝ) ^ exponent := by
  dsimp only
  let s := ((expBitLength num : ℤ) - exponent + reduction).toNat
  have hk : 0 ≤ exponent + s := by dsimp [s]; omega
  have hkn : expBitLength num + reduction ≤ (exponent + s).toNat := by dsimp [s]; omega
  have heq : (2 : ℝ) ^ (exponent + s).toNat = (2 : ℝ) ^ exponent * 2 ^ s := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hk, zpow_add₀ (by norm_num), zpow_natCast]
  constructor
  · have hb : (num : ℝ) ≤ (2 : ℝ) ^ expBitLength num := by
      have := (exp_magnitude_bounds num 0 hn).2.le
      simpa using this
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    apply (mul_le_mul_of_nonneg_right hb (by positivity)).trans
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hkn
  · rw [heq]
    field

theorem expNatBounds_bounds (num : ℕ) (exponent : ℤ) (negative : Bool) (prec : ℕ)
    (hn : num ≠ 0) :
    let result := expNatBounds num exponent negative prec
    let x : ℝ := num / (2 : ℝ) ^ exponent
    (result.1 : ℝ) ≤ 2 ^ prec * Real.exp (if negative then -x else x) ∧
      2 ^ prec * Real.exp (if negative then -x else x) ≤ result.2 := by
  dsimp only
  have hmag := exp_magnitude_bounds num exponent hn
  let x : ℝ := num / (2 : ℝ) ^ exponent
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) exponent).le
  by_cases htiny : (expBitLength num : ℤ) - exponent ≤ -((prec + 1 : ℕ) : ℤ)
  · rw [expNatBounds.eq_def, ite_eq_left htiny]
    have hsmall : x ≤ 1 / 2 ^ (prec + 1) := by
      have hp := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) htiny
      simp only [zpow_neg, zpow_natCast, ← one_div] at hp
      exact hmag.2.le.trans hp
    have ht := exp_tiny_bounds prec hx0 hsmall
    cases negative
    · simpa [Nat.shiftLeft_eq] using And.intro ht.1 ht.2.1
    · simpa [Nat.shiftLeft_eq] using And.intro ht.2.2.1 ht.2.2.2
  · rw [expNatBounds.eq_def, ite_eq_right htiny]
    split
    · rename_i hlarge
      have hlarge' : negative = true ∧ (expBitLength (prec + 1) : ℤ) <
          (expBitLength num : ℤ) - exponent := by simpa using hlarge
      rcases hlarge' with ⟨rfl, hlarge'⟩
      have hpx : (prec : ℝ) ≤ x := by
        have hpow : (2 : ℝ) ^ (expBitLength (prec + 1) : ℤ) ≤
            2 ^ ((expBitLength num : ℤ) - exponent - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hp := (exp_magnitude_bounds (prec + 1) 0 (by omega)).2.le
        simp only [zpow_zero, div_one, sub_zero, Nat.cast_add, Nat.cast_one] at hp
        have := hp.trans (hpow.trans hmag.1)
        dsimp [x]
        linarith only [this]
      simp only [ite_true, Nat.cast_zero, Nat.cast_one]
      exact ⟨mul_nonneg (by positivity) (Real.exp_pos _).le, exp_large_negative prec hpx⟩
    · set integerPart := match exponent with
        | .ofNat n => num >>> n
        | .negSucc n => num <<< (n + 1)
      have hip : (integerPart : ℝ) ≤ x := by
        cases exponent with
        | ofNat n => simpa [integerPart, x] using (shift_bounds num n).1
        | negSucc n =>
          simp [integerPart, x, Nat.shiftLeft_eq, zpow_negSucc, div_eq_mul_inv]
      dsimp only
      by_cases hlarge : (negative && decide (prec + 1 ≤ integerPart)) = true
      · erw [ite_eq_left hlarge]
        have hlarge' : negative = true ∧ prec + 1 ≤ integerPart := by
          simpa [integerPart] using hlarge
        rcases hlarge' with ⟨rfl, hlarge'⟩
        have hp : (prec : ℝ) ≤ x := by
          have hp' : (prec : ℝ) + 1 ≤ integerPart := by exact_mod_cast hlarge'
          linarith only [hp', hip]
        simp only [ite_true, Nat.cast_zero, Nat.cast_one]
        exact ⟨mul_nonneg (by positivity) (Real.exp_pos _).le, exp_large_negative prec hp⟩
      · erw [ite_eq_right hlarge]
        let growth := if negative then 0 else (3 * (integerPart + 1) + 1) / 2
        let target := prec + growth + 16
        let reduction₀ := max 2 (target.sqrt / if target < 65536 then 2 else 3)
        let reduction := if 65536 ≤ target && num < (1 <<< 64) then
          min 128 reduction₀ else reduction₀
        let squarings := ((expBitLength num : ℤ) - exponent + reduction).toNat
        let working := target + squarings
        let reducedExponent := (exponent + squarings).toNat
        have hr : 2 ≤ reduction := by
          dsimp [reduction, reduction₀]
          split_ifs <;> simp
        have hp : prec ≤ working := by dsimp [working, target]; omega
        have hs := exp_reduction_spec num reduction exponent hn
        have h := exp_compute_bounds num reducedExponent working reduction squarings prec
          negative hr hp hs.1
        rw [hs.2] at h
        exact h

/-- Construct a dyadic grid point, removing long trailing-zero runs before dyadic normalization.
In particular, an endpoint equal to `1` should not require `prec` normalization steps. -/
def expOfNatWithPrec (num prec : ℕ) : Dyadic :=
  if num &&& 1 = 1 then Dyadic.ofIntWithPrec num prec else
    let zeros := expBitLength (num - (num &&& (num - 1))) - 1
    Dyadic.ofIntWithPrec (num >>> zeros) ((prec : ℤ) - zeros)

private theorem nat_lowbit (n : ℕ) (hn : n ≠ 0) :
    n - (n &&& (n - 1)) = 2 ^ (n : ℤ).trailingZeros := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hmod : (n &&& (n - 1)) % 2 = 0 := by
      have : ¬(n &&& (n - 1)) % 2 = 1 := by
        rw [Nat.and_mod_two_eq_one]
        omega
      omega
    have hdiv := Nat.and_div_two (a := n) (b := n - 1)
    have hbound := Nat.and_le_left (n := n / 2) (m := (n - 1) / 2)
    by_cases hodd : n % 2 = 1
    · have heq : (n - 1) / 2 = n / 2 := by omega
      rw [heq, Nat.and_self] at hdiv
      rw [Int.trailingZeros_eq_zero_of_mod_eq (by exact_mod_cast hodd)]
      simp only [pow_zero]
      omega
    · have hn0 : n / 2 ≠ 0 := by omega
      have hn2 : n = 2 * (n / 2) := by omega
      have heq : (n - 1) / 2 = n / 2 - 1 := by omega
      rw [heq] at hdiv
      have hlow : n - (n &&& (n - 1)) = 2 * (n / 2 - (n / 2 &&& (n / 2 - 1))) := by
        rw [heq] at hbound
        omega
      have hz : (n : ℤ).trailingZeros = ((n / 2 : ℕ) : ℤ).trailingZeros + 1 := by
        conv_lhs => rw [hn2]
        push_cast
        exact Int.trailingZeros_two_mul (by exact_mod_cast hn0)
      rw [hlow, ih (n / 2) (by omega) hn0, hz, pow_succ, Nat.mul_comm]

theorem expOfNatWithPrec_eq (num prec : ℕ) :
    expOfNatWithPrec num prec = Dyadic.ofIntWithPrec num prec := by
  rw [expOfNatWithPrec]
  split_ifs with hodd
  · rfl
  · by_cases hn : num = 0
    · simp [hn, expBitLength_eq]
    have hlow := nat_lowbit num hn
    have hbit : expBitLength (num - (num &&& (num - 1))) - 1 =
        (num : ℤ).trailingZeros := by
      rw [hlow, expBitLength_eq, ite_eq_right (by positivity), Nat.log2_two_pow]
      omega
    rw [hbit]
    have hd := Int.two_pow_trailingZeros_dvd (by exact_mod_cast hn : (num : ℤ) ≠ 0)
    have hn' : (num : ℤ) =
        ((num >>> (num : ℤ).trailingZeros : ℕ) : ℤ) <<< (num : ℤ).trailingZeros := by
      rw [Int.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Int.natCast_ediv, Nat.cast_pow,
        Nat.cast_ofNat, Int.ediv_mul_cancel hd]
    have he := Dyadic.ofIntWithPrec_shiftLeft_add
      (x := ((num >>> (num : ℤ).trailingZeros : ℕ) : ℤ))
      (i := prec - (num : ℤ).trailingZeros) (n := (num : ℤ).trailingZeros)
    rw [← hn', sub_add_cancel] at he
    exact he.symm

theorem toReal_expOfNatWithPrec (num prec : ℕ) :
    Dyadic.toReal (expOfNatWithPrec num prec) = num / 2 ^ prec := by
  rw [expOfNatWithPrec_eq, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  simp [zpow_neg, div_eq_mul_inv]

/-- Enclose the exponential of a dyadic number, rounding outward to the `2⁻prec` grid.
Working precision includes guard bits for range reduction and error propagation; the endpoints
need not be the nearest outward grid points. -/
def expBounds (x : Dyadic) (prec : ℕ) : Dyadic × Dyadic :=
  match x with
  | .zero => (1, 1)
  | .ofOdd num exponent _ =>
    let (lb, ub) := expNatBounds num.natAbs exponent (!num.decNonneg.decide) prec
    (expOfNatWithPrec lb prec, expOfNatWithPrec ub prec)

theorem expBounds_bounds (x : Dyadic) (prec : ℕ) :
    Dyadic.toReal (expBounds x prec).1 ≤ Real.exp x.toReal ∧
      Real.exp x.toReal ≤ Dyadic.toReal (expBounds x prec).2 := by
  cases x with
  | zero =>
    have hone : Dyadic.toReal 1 = (1 : ℝ) := by
      have h : Dyadic.toRat 1 = (1 : ℚ) := by decide
      simp [Dyadic.toReal, h]
    have hzero : Dyadic.toReal 0 = (0 : ℝ) := by simp [Dyadic.toReal]
    simp [expBounds, Dyadic.zero_eq, hone, hzero]
  | ofOdd num exponent hodd =>
    have hn : num.natAbs ≠ 0 := by rw [Int.natAbs_ne_zero]; omega
    have h := expNatBounds_bounds num.natAbs exponent (!num.decNonneg.decide) prec hn
    have hx : (Dyadic.ofOdd num exponent hodd).toReal =
        if !num.decNonneg.decide then -((num.natAbs : ℝ) / (2 : ℝ) ^ exponent)
        else (num.natAbs : ℝ) / (2 : ℝ) ^ exponent := by
      cases num <;>
        simp [Dyadic.toReal, Dyadic.toRat_ofOdd_eq_mul_two_pow, Int.nonneg_def,
          Int.natAbs, zpow_neg, div_eq_mul_inv]
      ring
    dsimp only at h
    rw [← hx] at h
    simp only [expBounds, toReal_expOfNatWithPrec]
    constructor
    · rw [div_le_iff₀ (by positivity), mul_comm]
      exact h.1
    · rw [le_div_iff₀ (by positivity), mul_comm]
      exact h.2

/-- Enclose the exponential of a dyadic interval using monotonicity, with finite endpoints rounded
outward to the `2⁻prec` grid. An infinite lower endpoint contributes zero. -/
def exp (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.lb, I.ub with
  | some lb, some ub =>
    if lb = ub then
      let (lb, ub) := expBounds lb prec
      Interval.Icc lb ub
    else Interval.Icc (expBounds lb prec).1 (expBounds ub prec).2
  | some lb, ⊤ => Interval.Ici (expBounds lb prec).1
  | ⊥, some ub => Interval.Icc 0 (expBounds ub prec).2
  | ⊥, ⊤ => Interval.Ici 0

@[inclusion_op interval_dyadic_real]
theorem exp_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.exp x ∈ exp I prec := by
  rw [mem_iff_mem_map] at hx ⊢
  rcases I with ⟨_ | lb, _ | ub⟩
  · simpa [exp, Interval.Ici, Interval.map, Dyadic.toReal] using (Real.exp_pos x).le
  · apply Interval.mem_map_Icc Dyadic.toReal
    · simpa [Dyadic.toReal] using (Real.exp_pos x).le
    · exact (Real.exp_le_exp.mpr (Interval.le_map_ub Dyadic.toReal hx)).trans
        (expBounds_bounds ub prec).2
  · exact ⟨WithBot.coe_le_coe.mpr ((expBounds_bounds lb prec).1.trans
      (Real.exp_le_exp.mpr (Interval.map_lb_le Dyadic.toReal hx))), le_top⟩
  · have hl := (expBounds_bounds lb prec).1.trans
      (Real.exp_le_exp.mpr (Interval.map_lb_le Dyadic.toReal hx))
    have hu := (Real.exp_le_exp.mpr (Interval.le_map_ub Dyadic.toReal hx)).trans
      (expBounds_bounds ub prec).2
    simp only [exp]
    split_ifs with h
    · subst ub
      exact Interval.mem_map_Icc Dyadic.toReal hl hu
    · exact Interval.mem_map_Icc Dyadic.toReal hl hu

end Inclusion.IntervalDyadicReal
