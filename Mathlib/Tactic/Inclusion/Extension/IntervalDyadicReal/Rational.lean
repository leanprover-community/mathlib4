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

/-- Enclose a quotient of natural numbers in a dyadic interval with precision `prec`. -/
def divNatBounds (prec m d : ℕ) : Interval Dyadic :=
  let scaled := m <<< prec
  let quotient := scaled / d
  let upper := if quotient * d = scaled then quotient else quotient + 1
  Interval.Icc (Dyadic.ofIntWithPrec quotient prec) (Dyadic.ofIntWithPrec upper prec)

/-- Enclose a rational number in a dyadic interval with precision `prec`. -/
def ratBounds (prec : ℕ) (q : ℚ) : Interval Dyadic :=
  let lower := q.toDyadic prec
  let upper := if lower.toRat = q then lower else lower + Dyadic.ofIntWithPrec 1 prec
  ⟨lower, upper⟩

/-- Enclose a scientific literal in a dyadic interval with precision `prec`. -/
def scientific (prec m : ℕ) (s : Bool) (e : ℕ) : Interval Dyadic :=
  if s then
    divNatBounds prec m (10 ^ e)
  else
    Interval.singleton Dyadic ((m * 10 ^ e : ℕ) : Dyadic)

@[inclusionOp interval_dyadic_real]
theorem ratCast_mem (prec : ℕ) (q : ℚ) : (q : ℝ) ∈ ratBounds prec q := by
  rw [mem_iff_mem_map]
  constructor
  · exact WithBot.coe_le_coe.mpr <| Rat.cast_le.mpr Rat.toRat_toDyadic_le
  · apply WithTop.coe_le_coe.mpr
    split_ifs with h
    · rw [Dyadic.toReal, h]
    · exact (Rat.cast_lt (K := ℝ)).mpr Rat.lt_toRat_toDyadic_add |>.le

theorem divNatDown_le (prec m : ℕ) {d : ℕ} (hd : 0 < d) :
    Dyadic.toReal (Dyadic.divNatDown prec m d) ≤ (m : ℝ) / d := by
  rw [Dyadic.toReal, Dyadic.divNatDown, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  norm_num
  rw [Int.shiftLeft_eq, ← div_eq_mul_inv]
  apply (div_le_div_iff₀
    (by exact_mod_cast Nat.pow_pos (by decide : 0 < 2))
    (by exact_mod_cast hd)).2
  norm_cast
  exact Nat.div_mul_le_self (m * 2 ^ prec) d

theorem le_divNatUp (prec m : ℕ) {d : ℕ} (hd : 0 < d) :
    (m : ℝ) / d ≤ Dyadic.toReal (Dyadic.divNatUp prec m d) := by
  rw [Dyadic.toReal, ← Rat.cast_natCast (α := ℝ) m, ← Rat.cast_natCast (α := ℝ) d,
    ← Rat.cast_div, Rat.cast_le]
  rw [Dyadic.divNatUp, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  norm_num
  split_ifs with h
  all_goals
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by exact_mod_cast hd) (pow_pos (by norm_num) _)).2
    simp only [Nat.shiftLeft_eq, Int.shiftLeft_eq] at h ⊢
    norm_cast
  · exact h.ge
  · have hlt := Nat.lt_mul_div_self_add (x := m * 2 ^ prec) hd
    rw [Nat.mul_comm d] at hlt
    rw [Nat.add_mul, Nat.one_mul]
    exact hlt.le

theorem divNat_mem_bounds (prec m : ℕ) {d : ℕ} (hd : 0 < d) :
    (m : ℝ) / d ∈ (divNatBounds prec m d).map Dyadic.toReal := by
  constructor
  · apply WithBot.coe_le_coe.mpr
    simpa [divNatBounds, Dyadic.divNatDown] using divNatDown_le prec m hd
  · apply WithTop.coe_le_coe.mpr
    simpa [divNatBounds, Dyadic.divNatUp] using le_divNatUp prec m hd

@[inclusionOp interval_dyadic_real]
theorem scientific_mem (prec m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientific prec m s e := by
  cases s
  · rw [mem_iff_mem_map, NNRatCast.ofScientific_eq_ite]
    simp only [Bool.false_eq_true, if_false, NNRat.cast_natCast]
    simpa [scientific] using
      Interval.mem_map_singleton ((m * 10 ^ e : ℕ) : Dyadic) Dyadic.toReal
  · rw [mem_iff_mem_map]
    simpa [scientific, NNRatCast.ofScientific_eq_ite] using
      divNat_mem_bounds prec m (Nat.pow_pos (by decide : 0 < 10))

end IntervalDyadicReal

end Inclusion
