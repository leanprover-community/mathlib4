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
protected def smallArtanhSum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

/-- TODO doc -/
protected def smallArtanhError (n : ℕ) (x : ℚ) : ℚ :=
  |x| ^ (2 * n + 1) / (1 - x ^ 2)

private theorem abs_sub_le (n : ℕ) (x : ℚ) (hx : x ∈ Set.Ioo (-1) 1) :
    |artanh x - Dyadic.smallArtanhSum n x| ≤ Dyadic.smallArtanhError n x := by
  have := sum_range_sub_log_div_le (x := x) (abs_lt.mpr (mod_cast hx)) n
  rw [artanh_eq_half_log <| Set.Ioo_subset_Icc_self (by simpa using mod_cast hx)]
  simpa [Dyadic.smallArtanhSum, Dyadic.smallArtanhError] using this

def log_two (prec : ℕ) : Dyadic :=
  let N := (prec + 19) / 8
  let wp := prec + 8
  6 * (Dyadic.smallArtanhSum N (1 / 17)).toDyadic wp +
  4 * (Dyadic.smallArtanhSum N (1 / 19)).toDyadic wp +
  4 * (Dyadic.smallArtanhSum N (1 / 31)).toDyadic wp

theorem log_two_aux :
    log 2 = 6 * artanh (1 / 17) + 4 * artanh (1 / 19) + 4 * artanh (1 / 31) := by
  rw [show (2 : ℝ) = (9 / 8) ^ 3 * (10 / 9) ^ 2 * (16 / 15) ^ 2 by norm_num]
  simp [log_mul]
  norm_num [artanh_eq_half_log]
  field

theorem abs_log_two_sub_le (prec : ℕ) : |log 2 - (log_two prec).toReal| ≤ 1 / (2 ^ prec) := by
  rw [log_two_aux]
  have := abs_sub_le prec (1 / 3) (by norm_num)
  rw [artanh_eq_half_log (by norm_num)] at this
  norm_num at this
  sorry

end SmallArtanh

section Log

def logSum (x : Dyadic) (prec : ℕ) : Dyadic :=
  2 * (Dyadic.smallArtanhSum ((prec + 8) / 3 + 2) ((x - 1).toRat / (x + 1).toRat)).toDyadic prec

def log (x : Dyadic) (prec : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | ofOdd n p hn =>
    let k : ℤ := n.natAbs.log2 - p
    let x' : Dyadic := .ofOdd n n.natAbs.log2 hn
    logSum x' prec + k * Dyadic.log_two (prec + k.natAbs.log2 + 1)

end Log

end Dyadic

namespace Inclusion

/-- TODO doc -/
def Interval.log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let I' : Interval Dyadic := I.abs
  let wp : ℕ := prec + 4
  match I' with
  | ⟨some lb, ⊤⟩ =>
    if lb = 0 then ⟨⊥, ⊤⟩
    else if lb = 1 then ⟨0, ⊤⟩
    else ⟨(lb.log wp - Dyadic.step prec), ⊤⟩
  | ⟨some lb, some ub⟩ =>
    if lb = 0 then
      if ub = 0 then .singleton 0
      else if ub = 1 then ⟨⊥, 0⟩
      else ⟨⊥, (max (ub.log wp + Dyadic.step prec) 0)⟩
    else
      let lo : Dyadic := if lb = 1 then 0 else lb.log wp - Dyadic.step prec
      let hi : Dyadic := if ub = 1 then 0 else ub.log wp + Dyadic.step prec
      ⟨lo, hi⟩
  | _ => .univ Dyadic -- impossible case

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : x.log ∈ I.log prec := by
  sorry

end Inclusion
