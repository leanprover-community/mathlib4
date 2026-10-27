/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Rational enclosures for interval_dyadic_real

This file defines inclusion operations for the `interval_dyadic_real` inclusion family which
define dyadic interval enclosures for rational numbers.
-/

public meta section

open Lean Qq

namespace Inclusion

namespace IntervalDyadicReal

/-- The precision of dyadic approximations, defaulting to zero. -/
@[inclusion_param]
def precParam : InclusionParamDecl where
  name := `prec
  type := q(Nat)
  defaultValue? := some q(0)

end IntervalDyadicReal

end Inclusion

end

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

/-- Enclose a rational number in a dyadic interval with precision `prec`. -/
def rat (x : ℚ) (prec : ℕ) : Interval Dyadic :=
  let lower := x.toDyadic prec
  let upper := if lower.toRat = x then lower else lower + Dyadic.step prec
  Interval.Icc lower upper

@[inclusion_op interval_dyadic_real]
theorem ratCast_mem (q : ℚ) (prec : ℕ) : (q : ℝ) ∈ rat q prec := by
  apply Interval.mem_map_Icc Dyadic.toReal
  · exact Rat.cast_le.mpr Rat.toRat_toDyadic_le
  · split_ifs with h
    · rw [Dyadic.toReal, h]
    · rw [← Dyadic.ofIntWithPrec_one]
      exact Rat.cast_lt.mpr Rat.lt_toRat_toDyadic_add |>.le

/-- Efficiently enclose `m / d` in a dyadic interval with precision `prec`. -/
def natDiv (m d prec : ℕ) : Interval Dyadic :=
  let scaled := m <<< prec
  let quotient := scaled / d
  let lower := Dyadic.ofIntWithPrec quotient prec
  let upper := if quotient * d = scaled then lower else lower + Dyadic.step prec
  Interval.Icc lower upper

theorem natDiv_eq_rat (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    natDiv m d prec = rat (mkRat m d) prec := by
  rw [natDiv, rat]
  congr 2 <;>
    simp [Rat.toDyadic_mkRat, Dyadic.toRat_ofIntWithPrec_eq_mkRat, Rat.mkRat_eq_iff,
      Int.shiftLeft_eq, Nat.shiftLeft_eq, hd.ne']
  norm_cast

theorem natDiv_mem (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    (m : ℝ) / d ∈ natDiv m d prec := by
  rw [natDiv_eq_rat m prec hd]
  simpa [Rat.cast_mkRat_of_ne_zero, hd.ne'] using ratCast_mem (mkRat m d) prec

/-- Enclose a scientific literal in a dyadic interval with precision `prec`. -/
def scientific (m : ℕ) (s : Bool) (e prec : ℕ) : Interval Dyadic :=
  if s then
    natDiv m (10 ^ e) prec
  else
    Interval.singleton (m * (10 : Dyadic) ^ e)

@[inclusion_op interval_dyadic_real]
theorem scientific_mem (m : ℕ) (s : Bool) (e prec : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientific m s e prec := by
  cases s
  · simpa [scientific, NNRatCast.ofScientific_eq_ite, mem_iff_mem_map] using
      Interval.mem_map_singleton (m * (10 : Dyadic) ^ e) Dyadic.toReal
  · simpa [scientific, NNRatCast.ofScientific_eq_ite] using
      natDiv_mem m prec (Nat.pow_pos (by decide : 0 < 10))

end IntervalDyadicReal

end Inclusion
