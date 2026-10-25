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

open Real

section SmallArtanh

/-- TODO doc -/
protected def smallArtanh (num : ℕ) (den : ℕ) (n : ℕ) : ℕ × ℕ :=
  let (_, Q, R) := go 0 n
  (num * R, den * Q)
where
  go : ℕ -> ℕ -> ℕ × ℕ × ℕ := fun a b =>
    match h : b - a with
    | 0 => (1, 1, 0)
    | 1 => ((2 * a + 1) * num ^ 2, (2 * a + 3) * den ^ 2, (2 * a + 3) * den ^ 2)
    | _ + 2 =>
      let m := (a + b) / 2
      let (Pl, Ql, Rl) := go a m
      let (Pr, Qr, Rr) := go m b
      (Pl * Pr, Ql * Qr, Rl * Qr + Rr * Pl)
  termination_by a b => b - a
  decreasing_by all_goals omega

-- private theorem abs_sub_le (n : ℕ) (x : ℚ) (hx : x ∈ Set.Ioo (-1) 1) :
--     |artanh x - Dyadic.smallArtanh n x| ≤ |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
--   have := sum_range_sub_log_div_le (x := x) (abs_lt.mpr (mod_cast hx)) n
--   rw [artanh_eq_half_log <| Set.Ioo_subset_Icc_self (by simpa using mod_cast hx)]
--   simpa [Dyadic.smallArtanh] using this

/-- Computes the lower bound `l : Dyadic` for `log 2` with precision `prec`,
that is, `l < log 2` and `log 2 - l` < `ulp`. -/
protected def log_two (prec : ℕ) : Dyadic :=
  let (P1, Q1) := Dyadic.smallArtanh 1 17 ((prec + 7) / 8)
  let (P2, Q2) := Dyadic.smallArtanh 1 19 ((prec + 7) / 8)
  let (P3, Q3) := Dyadic.smallArtanh 1 31 ((prec + 8) / 9)
  let P := 6 * P1 * Q2 * Q3 + 4 * Q1 * P2 * Q3 + 4 * Q1 * Q2 * P3
  let Q := Q1 * Q2 * Q3
  .ofIntWithPrec (Int.fdiv (P <<< (prec + 4)) Q) (prec + 4)

theorem log_two_aux :
    log 2 = 6 * artanh (1 / 17 : ℚ) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31) := by
  rw [show (2 : ℝ) = (9 / 8) ^ 3 * (10 / 9) ^ 2 * (16 / 15) ^ 2 by norm_num]
  simp [log_mul]
  norm_num [artanh_eq_half_log]
  field

theorem abs_log_two_sub_le (prec : ℕ) :
    |log 2 - (Dyadic.log_two prec).toReal| ≤ 1 / (2 ^ prec) := by
  sorry

end SmallArtanh

section Log

/-- Assuming `x ∈ [1, 2)`, we have `(x - 1) / (x + 1) ∈ [0, 1 / 3)` and
`∀ x ∈ (1, 2), log x = 2 * artanh ((x - 1) / (x + 1)) > the sum`.
With `|log x - sum| < ulp`, this computes the lower bound `l : Dyadic`.

The error `δ ≤ 2 * x ^ (2 * n + 1) / (1 - x ^ 2) < 3 / 4 * (1 / 9) ^ n ≤ (1 / 2) ^ prec`
requires `n ≥ ((prec - 2) * log 2 + log 3) / (2 * log 3)`.
Choosing `prec / 3` is good enough.
-/
protected def logSum (x : Dyadic) (prec : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | ofOdd n _ _ =>
    let e : ℕ := n.natAbs.log2
    let m : ℕ := n.natAbs
    let (P, Q) := Dyadic.smallArtanh (m - 2 ^ e) (m + 2 ^ e) ((prec + 2) / 3)
    Dyadic.ofIntWithPrec (Int.fdiv (2 * P <<< (prec + 2)) Q) (prec + 2)

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
      Dyadic.logSum x' prec + k * Dyadic.log_two wp
    else
      Dyadic.logSum x' prec + k * (Dyadic.log_two wp + Dyadic.step wp)

/-- Computes the upper bound for `log x`. -/
def upperLog (x : Dyadic) (prec : ℕ) : Dyadic :=
  if |x| = 1 ∨ x = 0 then 0 else lowerLog x prec + Dyadic.step prec

theorem lowerLog_lt {x : Dyadic} (hx : 0 < x ∧ |x| ≠ 1) (prec : ℕ) :
    (x.lowerLog prec).toReal < x.toReal.log := by
  sorry

theorem lowerLog_le (x : Dyadic) (prec : ℕ) :
    (x.lowerLog prec).toReal ≤ x.toReal.log := by
  sorry

theorem abs_lowerLog_lt (x : Dyadic) (prec : ℕ) :
    |x.toReal.log - (x.lowerLog prec).toReal| < (Dyadic.step prec).toReal := by
  sorry

theorem lt_upperLog {x : Dyadic} (hx : 0 < x ∧ |x| ≠ 1) (prec : ℕ) :
    x.toReal.log < (x.upperLog prec).toReal := by
  sorry

theorem le_upperLog (x : Dyadic) (prec : ℕ) :
    x.toReal.log ≤ (x.upperLog prec).toReal := by
  sorry

theorem abs_upperLog_lt (x : Dyadic) (prec : ℕ) :
    |x.toReal.log - (x.upperLog prec).toReal| < (Dyadic.step prec).toReal := by
  sorry

end Log

end Dyadic

namespace Inclusion

/-- TODO doc -/
def Interval.log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let I' : Interval Dyadic := I.abs
  match I' with
  | ⟨some lb, ⊤⟩ =>
    if lb = 0 then .univ Dyadic
    else .Ici <| lb.lowerLog prec
  | ⟨some lb, some ub⟩ =>
    if lb = 0 then
      if ub = 0 then .singleton 0
      else .Iic <| (max (ub.upperLog prec) 0 : Dyadic)
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

@[simp]
lemma _root_.Dyadic.toReal_zero : Dyadic.toReal (0 : Dyadic) = 0 := by
  simp [Dyadic.toReal]

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
