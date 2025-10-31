/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Int.Defs

/-!
# The rational numbers possess a linear order

This file constructs the order on `ℚ` and proves various facts relating the order to
ring structure on `ℚ`. This only uses unbundled type classes, e.g. `CovariantClass`,
relating the order structure and algebra structure on `ℚ`.
For the bundled `LinearOrderedCommRing` instance on `ℚ`, see `Algebra.Order.Ring.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists IsOrderedMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b c p q : ℚ}

@[simp] lemma mkRat_nonneg {a : ℤ} (ha : 0 ≤ a) (b : ℕ) : 0 ≤ mkRat a b := by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)

theorem ofScientific_nonneg (m : ℕ) (s : Bool) (e : ℕ) : 0 ≤ Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
    exact num_nonneg.mp <| Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]

instance _root_.NNRatCast.toOfScientific {K} [NNRatCast K] : OfScientific K where
  ofScientific (m : ℕ) (b : Bool) (d : ℕ) :=
    NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

theorem _root_.NNRatCast.toOfScientific_def {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      NNRat.cast ⟨(OfScientific.ofScientific m b d : ℚ), ofScientific_nonneg m b d⟩ :=
  rfl

/-- Casting a scientific literal via `ℚ≥0` is the same as casting directly. -/
@[simp, norm_cast]
theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ≥0) = (OfScientific.ofScientific m s e : K) :=
  rfl

protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

protected lemma lt_iff_le_not_ge (a b : ℚ) : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Std.LawfulOrderLT.lt_iff a b

instance linearOrder : LinearOrder ℚ where
  le_refl _ := Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge

theorem mkRat_nonneg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 ≤ mkRat a b ↔ 0 ≤ a :=
  divInt_nonneg_iff_of_pos_right (show 0 < (b : ℤ) by simpa using Nat.pos_of_ne_zero hb)

theorem mkRat_pos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b ↔ 0 < a := by
  grind [mkRat_nonneg_iff, Rat.mkRat_eq_zero]

theorem mkRat_pos {a : ℤ} (ha : 0 < a) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b :=
  (mkRat_pos_iff a hb).mpr ha

theorem mkRat_nonpos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b ≤ 0 ↔ a ≤ 0 := by
  grind [mkRat_pos_iff]

theorem mkRat_nonpos {a : ℤ} (ha : a ≤ 0) (b : ℕ) : mkRat a b ≤ 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha

theorem mkRat_neg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 ↔ a < 0 := by
  grind [mkRat_nonneg_iff]

theorem mkRat_neg {a : ℤ} (ha : a < 0) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 :=
  (mkRat_neg_iff a hb).mpr ha

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instDistribLattice : DistribLattice ℚ := inferInstance
instance instLattice : Lattice ℚ := inferInstance
instance instSemilatticeInf : SemilatticeInf ℚ := inferInstance
instance instSemilatticeSup : SemilatticeSup ℚ := inferInstance
instance instInf : Min ℚ := inferInstance
instance instSup : Max ℚ := inferInstance
instance instPartialOrder : PartialOrder ℚ := inferInstance
instance instPreorder : Preorder ℚ := inferInstance

/-! ### Miscellaneous lemmas -/

@[deprecated (since := "2025-08-14")] alias le_def := Rat.le_iff

@[deprecated (since := "2025-08-14")] alias lt_def := Rat.lt_iff

instance : AddLeftMono ℚ where
  elim := fun _ _ _ h => Rat.add_le_add_left.2 h

@[simp] lemma num_nonpos {a : ℚ} : a.num ≤ 0 ↔ a ≤ 0 := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt]
@[simp] lemma num_pos {a : ℚ} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
@[simp] lemma num_neg {a : ℚ} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · simp [div_def', Rat.divInt_le_divInt d_pos b_pos]

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_iff]

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]

theorem abs_def' (q : ℚ) :
    |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_natAbs ▸ q.reduced⟩ := by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

@[simp]
theorem num_abs_eq_abs_num (q : ℚ) : |q|.num = |q.num| := by
  rw [abs_def']

@[simp]
theorem den_abs_eq_den (q : ℚ) : |q|.den = q.den := by
  rw [abs_def']

end Rat
