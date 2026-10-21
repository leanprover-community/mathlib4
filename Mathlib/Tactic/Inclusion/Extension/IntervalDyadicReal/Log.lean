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

-- don't use ℚ?
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/LeanCert.20-.20Verified.20Computation.20.26.20Interval.20Arithmetic/near/567588580

-- TODO: use binary splitting
-- <http://numbers.computation.free.fr/Constants/Algorithms/splitting.html>
/-- TODO doc -/
protected def smallArtanh (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

private theorem abs_sub_le (n : ℕ) (x : ℚ) (hx : x ∈ Set.Ioo (-1) 1) :
    |artanh x - Dyadic.smallArtanh n x| ≤ |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  have := sum_range_sub_log_div_le (x := x) (abs_lt.mpr (mod_cast hx)) n
  rw [artanh_eq_half_log <| Set.Ioo_subset_Icc_self (by simpa using mod_cast hx)]
  simpa [Dyadic.smallArtanh] using this

/-- Computes the lower bound `l : Dyadic` for `log 2` with precision `prec`,
that is, `l < log 2` and `log 2 - l` < `ulp`. -/
protected def log_two (prec : ℕ) : Dyadic :=
  6 * (Dyadic.smallArtanh ((prec + 7) / 8) (1 / 17)).toDyadic (prec + 4) +
  4 * (Dyadic.smallArtanh ((prec + 7) / 8) (1 / 19)).toDyadic (prec + 4) +
  4 * (Dyadic.smallArtanh ((prec + 8) / 9) (1 / 31)).toDyadic (prec + 4)

theorem log_two_aux :
    log 2 = 6 * artanh (1 / 17 : ℚ) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31) := by
  rw [show (2 : ℝ) = (9 / 8) ^ 3 * (10 / 9) ^ 2 * (16 / 15) ^ 2 by norm_num]
  simp [log_mul]
  norm_num [artanh_eq_half_log]
  field

theorem abs_log_two_sub_le (prec : ℕ) :
    |log 2 - (Dyadic.log_two prec).toReal| ≤ 1 / (2 ^ prec) := by
  rw [log_two_aux, Dyadic.log_two]
  rw [toReal_add, toReal_add, sub_add_eq_sub_sub, sub_add_eq_sub_sub]
  grw [← sub_add_eq_add_sub, ← sub_add_eq_add_sub, ← add_sub, abs_add_le,
    ← sub_add_eq_add_sub, ← add_sub, abs_add_le]
  simp only [toReal_mul, toReal_ofNat, ← mul_sub, abs_mul, Nat.abs_ofNat]
  rw [show (1 / 2 ^ prec : ℝ) = (1 / 2 + 1 / 4 + 1 / 4) * (1 / 2 ^ prec) by norm_num,
    _root_.add_mul, _root_.add_mul]
  iterate 2 gcongr 1
  · sorry
  · sorry
  · sorry

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
  2 * (Dyadic.smallArtanh (prec / 3) ((x - 1).toRat / (x + 1).toRat)).toDyadic prec

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

theorem Interval.abs_lb_nonneg {α : Type*} [AddGroup α] [LinearOrder α] [AddLeftMono α]
    (I : Interval α) : 0 ≤ I.abs.lb := by
  -- no
  fun_cases Interval.abs with
  | case1 lb h hlb =>
    rw [h]
    apply WithBot.coe_nonneg.mpr ‹_›
  | case2 => exact WithBot.coe_nonneg.mpr <| neg_nonneg.mpr ‹_›
  | case3 | case4 => rfl
  | case5 _ lb =>
    rcases I with ⟨_, ⟨⟩ | ⟨ub⟩⟩
    · simp only [lb]
      rfl
    · simp only [lb]
      split_ifs with hub
      · simp only [Ici, hub, ↓reduceIte]
        exact WithBot.coe_nonneg.mpr <| neg_nonneg.mpr ‹_›
      · simp [hub]
        rfl

-- don't use this, use `IsOrderedAddMonoid`.
instance : AddLeftMono Dyadic where
  elim a b c h := Dyadic.toReal_le_toReal.mp <| by simpa

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : x.log ∈ I.log prec := by
  apply IntervalDyadicReal.abs_mem at hx
  rw [← Real.log_abs]
  have hx' : 0 ≤ |x| := abs_nonneg x
  generalize |x| = x at *
  fun_cases Interval.log with
  | case1 I' hI' => apply Interval.mem_map_univ
  | case2 I' lb hI' hlb =>
    change x ∈ I' at hx
    rw [hI'] at hx
    refine IntervalDyadicReal.mem_Ici_coe _ _ |>.mpr <|
      Dyadic.lowerLog_le lb prec |>.trans <| Real.log_le_log ?_ <|
        IntervalDyadicReal.mem_Ici_coe x lb |>.mp hx
    have := WithBot.coe_nonneg.mp <| hI' ▸ show 0 ≤ I'.lb from I.abs_lb_nonneg
    simpa [← Dyadic.toReal_zero] using lt_of_le_of_ne this <| Ne.symm hlb
  | case3 I' hI' =>
    -- bad proof
    suffices x.log = Dyadic.toReal 0 from this ▸ Interval.mem_map_singleton 0 Dyadic.toReal
    suffices x = 0 by simp [this, Dyadic.toReal]
    change x ∈ I' at hx
    rw [hI'] at hx
    change x ∈ Interval.singleton 0 at hx
    ----------------------------------------
    rw [IntervalDyadicReal.mem_iff_mem_map] at hx
    simp only [Interval.map, WithBot.map, WithTop.map, Interval.mem_def] at hx
    replace hx := hx.imp_left WithBot.coe_le_coe.mp |>.imp_right WithTop.coe_le_coe.mp
    unfold Dyadic.toReal at hx
    simp at hx
    grind
  | case4 I' ub hub hI' =>
    change x ∈ I' at hx
    rw [hI'] at hx
    replace hx : 0 ≤ x ∧ x ≤ ub.toReal :=
      Dyadic.toReal_zero ▸ (IntervalDyadicReal.mem_mk_coe x 0 ub |>.mp hx)
    refine IntervalDyadicReal.mem_Iic_coe _ _ |>.mpr ?_
    rw [Monotone.map_max (f := Dyadic.toReal) Dyadic.toRealOrderEmbedding.monotone, ]
    simp only [Dyadic.toReal_zero, le_max_iff]
    by_cases hx₀ : x = 0
    · simp [hx₀, Dyadic.toReal]
    · apply Or.inl <| Dyadic.le_upperLog ub prec |>.trans' <| Real.log_le_log (by grind) hx.right
  | case5 I' lb ub hI' hlb =>
    change x ∈ I' at hx
    rw [hI'] at hx
    replace hx : lb.toReal ≤ x ∧ x ≤ ub.toReal := IntervalDyadicReal.mem_mk_coe x _ _ |>.mp hx
    simp only [IntervalDyadicReal.mem_mk_coe]
    have : 0 < lb.toReal := by
      -- duplicate proof
      have := WithBot.coe_nonneg.mp <| hI' ▸ show 0 ≤ I'.lb from I.abs_lb_nonneg
      simpa [← Dyadic.toReal_zero] using lt_of_le_of_ne this <| Ne.symm hlb
    exact ⟨lb.lowerLog_le prec |>.trans <| Real.log_le_log this <| hx.left,
      ub.le_upperLog prec |>.trans' <| Real.log_le_log (this.trans_le hx.left) hx.right⟩
  | case6 I' hI' => apply Interval.mem_map_univ

end Inclusion
