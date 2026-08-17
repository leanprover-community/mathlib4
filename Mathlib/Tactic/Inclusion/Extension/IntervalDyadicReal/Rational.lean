/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Rational constants for interval_dyadic_real

This file defines dyadic enclosures of rational casts and scientific literals for the
`interval_dyadic_real` inclusion family.
-/

public meta section

open Lean Qq

namespace Inclusion

namespace IntervalDyadicReal

/-- The precision of dyadic approximations. -/
@[inclusionParam]
def precParam : InclusionParamDecl where
  name := `prec
  type := q(Nat)

end IntervalDyadicReal

end Inclusion

end

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

/-- Efficiently enclose `m / d` in a dyadic interval with precision `prec`, for positive `d`. -/
def divNatInterval (m d prec : ℕ) : Interval Dyadic :=
  let scaled := m <<< prec
  let quotient := scaled / d
  let upper := if quotient * d = scaled then quotient else quotient + 1
  Interval.Icc (Dyadic.ofIntWithPrec quotient prec) (Dyadic.ofIntWithPrec upper prec)

/-- Enclose a rational number in a dyadic interval with precision `prec`. -/
def ratInterval (x : ℚ) (prec : ℕ) : Interval Dyadic :=
  let lower := x.toDyadic prec
  let upper := if lower.toRat = x then lower else lower + Dyadic.ofIntWithPrec 1 prec
  Interval.Icc lower upper

/-- Enclose a scientific literal in a dyadic interval with precision `prec`. -/
def scientificInterval (m : ℕ) (s : Bool) (e prec : ℕ) : Interval Dyadic :=
  if s then
    divNatInterval m (10 ^ e) prec
  else
    Interval.singleton Dyadic ((m * 10 ^ e : ℕ) : Dyadic)

@[inclusionOp interval_dyadic_real]
theorem ratCast_mem (q : ℚ) (prec : ℕ) : (q : ℝ) ∈ ratInterval q prec := by
  rw [mem_iff_mem_map]
  constructor
  · exact WithBot.coe_le_coe.mpr <| Rat.cast_le.mpr Rat.toRat_toDyadic_le
  · apply WithTop.coe_le_coe.mpr
    split_ifs with h
    · rw [Dyadic.toReal, h]
    · exact (Rat.cast_lt (K := ℝ)).mpr Rat.lt_toRat_toDyadic_add |>.le

private theorem divNatInterval_lower_le (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    Dyadic.toReal (Dyadic.ofIntWithPrec ((m <<< prec) / d) prec) ≤ (m : ℝ) / d := by
  norm_num [Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Int.shiftLeft_eq]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀
    (by exact_mod_cast Nat.pow_pos (by decide : 0 < 2))
    (by exact_mod_cast hd)).2
  exact_mod_cast Nat.div_mul_le_self (m * 2 ^ prec) d

private theorem le_divNatInterval_upper (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    (m : ℝ) / d ≤ Dyadic.toReal (Dyadic.ofIntWithPrec
      (if (m <<< prec) / d * d = m <<< prec then (m <<< prec) / d else (m <<< prec) / d + 1)
      prec) := by
  rw [Dyadic.toReal, ← Rat.cast_natCast (α := ℝ) m, ← Rat.cast_natCast (α := ℝ) d,
    ← Rat.cast_div, Rat.cast_le]
  norm_num [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  split_ifs with h
  all_goals
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by exact_mod_cast hd) (pow_pos (by norm_num) _)).2
    simp only [Nat.shiftLeft_eq, Int.shiftLeft_eq] at h ⊢
    norm_cast
  · exact h.ge
  · simpa [Nat.add_mul] using (Nat.lt_div_mul_add (a := m * 2 ^ prec) hd).le

private theorem divNat_mem_interval (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    (m : ℝ) / d ∈ (divNatInterval m d prec).map Dyadic.toReal := by
  constructor
  · apply WithBot.coe_le_coe.mpr
    simpa [divNatInterval] using divNatInterval_lower_le m prec hd
  · apply WithTop.coe_le_coe.mpr
    simpa [divNatInterval] using le_divNatInterval_upper m prec hd

@[inclusionOp interval_dyadic_real]
theorem scientific_mem (m : ℕ) (s : Bool) (e prec : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientificInterval m s e prec := by
  cases s
  · rw [mem_iff_mem_map, NNRatCast.ofScientific_eq_ite]
    simp only [Bool.false_eq_true, if_false, NNRat.cast_natCast]
    simpa [scientificInterval] using
      Interval.mem_map_singleton ((m * 10 ^ e : ℕ) : Dyadic) Dyadic.toReal
  · rw [mem_iff_mem_map]
    simpa [scientificInterval, NNRatCast.ofScientific_eq_ite] using
      divNat_mem_interval m prec (Nat.pow_pos (by decide : 0 < 10))

end IntervalDyadicReal

end Inclusion
