/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Defs.LinearOrder

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Dyadic rationals

This file provides general API for Dyadic rationals that are used in Mathlib but not available in
core.
-/

@[expose] public section

instance : LinearOrder Dyadic where
  le_refl := Std.IsPreorder.le_refl
  le_trans := Std.IsPreorder.le_trans
  le_antisymm := Std.IsPartialOrder.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_total := Std.IsLinearOrder.le_total
  toDecidableLE := Dyadic.instDecidableLE

instance : AddCommGroup Dyadic where
  nsmul := (· * ·)
  zsmul := (· * ·)
  add_zero := Dyadic.add_zero
  zero_add := Dyadic.zero_add
  add_assoc := Dyadic.add_assoc
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Dyadic.neg_add_cancel
  add_comm := Dyadic.add_comm
  nsmul_zero := by grind
  nsmul_succ := by grind
  zsmul_zero' := by grind
  zsmul_succ' := by grind
  zsmul_neg' := by grind

namespace Dyadic

-- From Violeta Hernández's leanprover/lean4#15532. TODO: Remove the following instance and
-- attributes once that PR is included in Mathlib's Lean toolchain.
attribute [coe] toRat

instance : Coe Dyadic Rat := ⟨toRat⟩

attribute [norm_cast] toRat_zero toRat_add toRat_neg toRat_sub toRat_mul toRat_pow
  toRat_intCast toRat_natCast toRat_eq_zero_iff toRat_lt_toRat_iff toRat_le_toRat_iff
attribute [simp, norm_cast] toRat_inj

@[simp, norm_cast]
theorem toRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    toRat (ofNat(n) : Dyadic) = (ofNat(n) : Rat) := by
  rw [← Nat.cast_ofNat (R := Dyadic)]
  exact toRat_natCast n

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

end Dyadic
