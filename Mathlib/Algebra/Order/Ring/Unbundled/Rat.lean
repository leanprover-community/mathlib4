/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Int.Order.Basic
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

assert_not_exists OrderedCommMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b c p q : ℚ}

@[simp] lemma mkRat_nonneg {a : ℤ} (ha : 0 ≤ a) (b : ℕ) : 0 ≤ mkRat a b := by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)

theorem ofScientific_nonneg (m : ℕ) (s : Bool) (e : ℕ) :
    0 ≤ Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
    refine num_nonneg.mp ?_
    rw [num_natCast]
    exact Int.natCast_nonneg _
  · rw [if_pos rfl, normalize_eq_mkRat]
    exact Rat.mkRat_nonneg (Int.natCast_nonneg _) _

instance _root_.NNRatCast.toOfScientific {K} [NNRatCast K] : OfScientific K where
  ofScientific (m : ℕ) (b : Bool) (d : ℕ) :=
    NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

/-- Casting a scientific literal via `ℚ≥0` is the same as casting directly. -/
@[simp, norm_cast]
theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ≥0) = (OfScientific.ofScientific m s e : K) :=
  rfl

protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

protected lemma lt_iff_le_not_ge (a b : ℚ) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [← Rat.not_le, and_iff_right_of_imp Rat.le_total.resolve_left]

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
  grind [lt_iff_le_and_ne, mkRat_nonneg_iff, Rat.mkRat_eq_zero]

theorem mkRat_pos {a : ℤ} (ha : 0 < a) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b :=
  (mkRat_pos_iff a hb).mpr ha

theorem mkRat_nonpos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b ≤ 0 ↔ a ≤ 0 := by
  grind [lt_iff_not_ge, mkRat_pos_iff]

theorem mkRat_nonpos {a : ℤ} (ha : a ≤ 0) (b : ℕ) : mkRat a b ≤ 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha

theorem mkRat_neg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 ↔ a < 0 := by
  grind [lt_iff_not_ge, mkRat_nonneg_iff]

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

protected lemma le_def : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← num_divInt_den q, ← num_divInt_den p]
  conv_rhs => simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast p.pos) (mod_cast q.pos)

protected lemma lt_def : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [lt_iff_le_and_ne, Rat.le_def]
  suffices p ≠ q ↔ p.num * q.den ≠ q.num * p.den by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact not_iff_not.mpr eq_iff_mul_eq_mul

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

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_def]

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  rcases le_total q 0 with hq | hq
  · rw [abs_of_nonpos hq]
    rw [← num_divInt_den q, ← zero_divInt, Rat.divInt_le_divInt (mod_cast q.pos) Int.zero_lt_one,
      mul_one, zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def]
  · rw [abs_of_nonneg hq]
    rw [← num_divInt_den q, ← zero_divInt, Rat.divInt_le_divInt Int.zero_lt_one (mod_cast q.pos),
      mul_one, zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_divInt_den]

end Rat
