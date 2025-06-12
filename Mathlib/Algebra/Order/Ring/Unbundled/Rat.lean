/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.Order.Basic

/-!
# The rational numbers possess a linear order

This file constructs the order on `ℚ` and proves various facts relating the order to
ring structure on `ℚ`. This only uses unbundled type classes, eg `CovariantClass`,
relating the order structure and algebra structure on `ℚ`.
For the bundled `LinearOrderedCommRing` instance on `ℚ`, see `Algebra.Order.Ring.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists OrderedCommMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b p q : ℚ}

@[simp] lemma divInt_nonneg_iff_of_pos_right {a b : ℤ} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  rcases hab : a /. b with ⟨n, d, hd, hnd⟩
  rw [mk'_eq_divInt, divInt_eq_iff hb.ne' (mod_cast hd)] at hab
  rw [← num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

@[simp] lemma divInt_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a /. b := by
  obtain rfl | hb := hb.eq_or_lt
  · simp
    rfl
  rwa [divInt_nonneg_iff_of_pos_right hb]

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

protected lemma add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ by
    have d₁0 : 0 < (d₁ : ℤ) := mod_cast Nat.pos_of_ne_zero h₁
    have d₂0 : 0 < (d₂ : ℤ) := mod_cast Nat.pos_of_ne_zero h₂
    simp only [d₁0, d₂0, h₁, h₂, Int.mul_pos, divInt_nonneg_iff_of_pos_right, divInt_add_divInt, Ne,
      Nat.cast_eq_zero, not_false_iff]
    intro n₁0 n₂0
    apply Int.add_nonneg <;> apply Int.mul_nonneg <;> · first | assumption | apply Int.ofNat_zero_le

protected lemma mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := mod_cast Nat.pos_of_ne_zero h₁
      have d₂0 : 0 < (d₂ : ℤ) := mod_cast Nat.pos_of_ne_zero h₂
      simp only [d₁0, d₂0, Int.mul_pos, divInt_nonneg_iff_of_pos_right,
        divInt_mul_divInt _ _ d₁0.ne' d₂0.ne']
      apply Int.mul_nonneg

protected theorem not_le {a b : ℚ} : ¬a ≤ b ↔ b < a := (Bool.not_eq_false _).to_iff

protected theorem not_lt {a b : ℚ} : ¬a < b ↔ b ≤ a := by
  rw [← Rat.not_le, not_not]

protected theorem lt_iff (a b : ℚ) : a < b ↔ a.num * b.den < b.num * a.den :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      show Rat.blt _ _ = true ↔ _
      suffices
        (na < 0 ∧ 0 ≤ nb ∨ if na = 0 then 0 < nb else (na ≤ 0 ∨ 0 < nb) ∧ na * ↑db < nb * da) ↔
        na * db < nb * da by simpa [Rat.blt]
      split_ifs with h
      · suffices 0 < nb ↔ 0 < nb * da by simpa [h]
        refine ⟨(Int.mul_pos · (by omega)), ?_⟩
        contrapose!
        exact (Int.mul_nonpos_of_nonpos_of_nonneg · (by omega))
      · constructor
        · refine (·.elim ?_ And.right)
          rintro ⟨hna, nb0⟩
          apply (Int.mul_neg_of_neg_of_pos hna _).trans_le (Int.mul_nonneg nb0 _) <;> omega
        · intro h
          suffices na < 0 ∧ 0 ≤ nb ∨ na ≤ 0 ∨ 0 < nb by simpa [h]
          contrapose! h
          apply (Int.mul_nonpos_of_nonpos_of_nonneg _ _).trans (Int.mul_nonneg _ _) <;> omega

protected theorem le_iff (a b : ℚ) : a ≤ b ↔ a.num * b.den ≤ b.num * a.den := by
  simpa only [Rat.not_lt, not_lt] using (Rat.lt_iff b a).not

protected theorem le_iff_sub_nonneg (a b : ℚ) : a ≤ b ↔ 0 ≤ b - a :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      rw [Rat.le_iff, sub_def, normalize_eq, ← num_nonneg, ← Int.sub_nonneg]
      dsimp only
      refine ⟨(Int.ediv_nonneg · (Int.natCast_nonneg _)), fun H ↦ ?_⟩
      contrapose! H
      apply Int.ediv_neg_of_neg_of_pos H
      simp only [Int.natCast_pos, Nat.pos_iff_ne_zero]
      exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)

protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

protected lemma le_total : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, neg_sub] using Rat.nonneg_total (b - a)

instance linearOrder : LinearOrder ℚ where
  le_refl a := by rw [Rat.le_iff_sub_nonneg, ← num_nonneg]; simp
  le_trans a b c hab hbc := by
    rw [Rat.le_iff_sub_nonneg] at hab hbc
    have := Rat.add_nonneg hab hbc
    simp_rw [sub_eq_add_neg, add_left_comm (b + -a) c (-b), add_comm (b + -a) (-b),
      add_left_comm (-b) b (-a), add_comm (-b) (-a), add_neg_cancel_comm_assoc,
      ← sub_eq_add_neg] at this
    rwa [Rat.le_iff_sub_nonneg]
  le_antisymm a b hab hba := by
    rw [Rat.le_iff_sub_nonneg] at hab hba
    rw [sub_eq_add_neg] at hba
    rw [← neg_sub, sub_eq_add_neg] at hab
    have := eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hba hab)
    rwa [neg_neg] at this
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge _ _ := by rw [← Rat.not_le, and_iff_right_of_imp Rat.le_total.resolve_left]

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

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, add_sub_add_left_eq_sub, ← Rat.le_iff_sub_nonneg]

instance : AddLeftMono ℚ where
  elim := fun _ _ _ h => Rat.add_le_add_left.2 h

@[simp] lemma num_nonpos {a : ℚ} : a.num ≤ 0 ↔ a ≤ 0 := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]
@[simp] lemma num_pos {a : ℚ} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
@[simp] lemma num_neg {a : ℚ} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · apply not_congr
    simp [div_def', Rat.divInt_le_divInt d_pos b_pos]

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
