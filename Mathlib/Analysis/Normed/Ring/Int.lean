/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

public section


namespace Int

theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_coe_units, NNReal.coe_one]

@[simp]
theorem nnnorm_natCast (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnnorm_natCast _

@[simp] lemma enorm_natCast (n : ℕ) : ‖(n : ℤ)‖ₑ = n := Real.enorm_natCast _

@[simp]
theorem toNat_add_toNat_neg_eq_nnnorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, toNat_add_toNat_neg_eq_natAbs, NNReal.natCast_natAbs]

@[simp]
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

end Int
