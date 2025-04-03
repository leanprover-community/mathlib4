/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Rat

#align_import data.rat.order from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# The rational numbers form a linear ordered field

This file constructs the order on `ℚ` and proves that `ℚ` is a discrete, linearly ordered
commutative ring.

`ℚ` is in fact a linearly ordered field, but this fact is located in `Data.Rat.Field` instead of
here because we need the order on `ℚ` to define `ℚ≥0`, which we itself need to define `Field`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists Field
assert_not_exists Finset
assert_not_exists Set.Icc
assert_not_exists GaloisConnection

namespace Rat

variable {a b c p q : ℚ}

@[simp] lemma divInt_nonneg_iff_of_pos_right {a b : ℤ} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  cases' hab : a /. b with n d hd hnd
  rw [mk'_eq_divInt, divInt_eq_iff hb.ne' (mod_cast hd)] at hab
  rw [← num_nonneg, ← mul_nonneg_iff_of_pos_right hb, ← hab,
    mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]
#align rat.mk_nonneg Rat.divInt_nonneg_iff_of_pos_right

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
    simp only [d₁0, d₂0, h₁, h₂, mul_pos, divInt_nonneg_iff_of_pos_right, divInt_add_divInt, Ne,
      Nat.cast_eq_zero, not_false_iff]
    intro n₁0 n₂0
    apply add_nonneg <;> apply mul_nonneg <;> · first |assumption|apply Int.ofNat_zero_le
#align rat.nonneg_add Rat.add_nonneg

protected lemma mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := mod_cast Nat.pos_of_ne_zero h₁
      have d₂0 : 0 < (d₂ : ℤ) := mod_cast Nat.pos_of_ne_zero h₂
      simp only [d₁0, d₂0, mul_pos, divInt_nonneg_iff_of_pos_right,
        divInt_mul_divInt _ _ d₁0.ne' d₂0.ne']
      apply mul_nonneg
#align rat.nonneg_mul Rat.mul_nonneg
#align rat.mul_nonneg Rat.mul_nonneg

-- Porting note (#11215): TODO can this be shortened?
protected theorem le_iff_sub_nonneg (a b : ℚ) : a ≤ b ↔ 0 ≤ b - a :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      change Rat.blt _ _ = false ↔ _
      unfold Rat.blt
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, not_lt, ite_eq_left_iff, not_and, not_le, ← num_nonneg]
      split_ifs with h h'
      · rw [Rat.sub_def]
        simp only [false_iff, not_le]
        simp only [normalize_eq]
        apply Int.ediv_neg'
        · rw [sub_neg]
          apply lt_of_lt_of_le
          · apply mul_neg_of_neg_of_pos h.1
            rwa [Int.natCast_pos, Nat.pos_iff_ne_zero]
          · apply mul_nonneg h.2 (Int.natCast_nonneg _)
        · simp only [Int.natCast_pos, Nat.pos_iff_ne_zero]
          exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)
      · simp only [divInt_ofNat, ← zero_iff_num_zero, mkRat_eq_zero hb] at h'
        simp [h']
      · simp only [Rat.sub_def, normalize_eq]
        refine ⟨fun H => ?_, fun H _ => ?_⟩
        · refine Int.ediv_nonneg ?_ (Int.natCast_nonneg _)
          rw [sub_nonneg]
          push_neg at h
          obtain hb|hb := Ne.lt_or_lt h'
          · apply H
            intro H'
            exact (hb.trans H').false.elim
          · obtain ha|ha := le_or_lt na 0
            · apply le_trans <| mul_nonpos_of_nonpos_of_nonneg ha (Int.natCast_nonneg _)
              exact mul_nonneg hb.le (Int.natCast_nonneg _)
            · exact H (fun _ => ha)
        · rw [← sub_nonneg]
          contrapose! H
          apply Int.ediv_neg' H
          simp only [Int.natCast_pos, Nat.pos_iff_ne_zero]
          exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)

protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← sub_nonneg (α := ℤ)]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
#align rat.le_def Rat.divInt_le_divInt

protected lemma le_total : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, neg_sub] using Rat.nonneg_total (b - a)
#align rat.le_total Rat.le_total

protected theorem not_le {a b : ℚ} : ¬a ≤ b ↔ b < a := (Bool.not_eq_false _).to_iff

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
  decidableEq := inferInstance
  decidableLE := inferInstance
  decidableLT := inferInstance
  lt_iff_le_not_le _ _ := by rw [← Rat.not_le, and_iff_right_of_imp Rat.le_total.resolve_left]
#align rat.le_refl le_refl
#align rat.le_antisymm le_antisymm
#align rat.le_trans le_trans

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instDistribLattice : DistribLattice ℚ := inferInstance
instance instLattice        : Lattice ℚ        := inferInstance
instance instSemilatticeInf : SemilatticeInf ℚ := inferInstance
instance instSemilatticeSup : SemilatticeSup ℚ := inferInstance
instance instInf            : Inf ℚ            := inferInstance
instance instSup            : Sup ℚ            := inferInstance
instance instPartialOrder   : PartialOrder ℚ   := inferInstance
instance instPreorder       : Preorder ℚ       := inferInstance

/-! ### Miscellaneous lemmas -/

protected lemma le_def : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← num_divInt_den q, ← num_divInt_den p]
  conv_rhs => simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast p.pos) (mod_cast q.pos)
#align rat.le_def' Rat.le_def

protected lemma lt_def : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [lt_iff_le_and_ne, Rat.le_def]
  suffices p ≠ q ↔ p.num * q.den ≠ q.num * p.den by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact not_iff_not.mpr eq_iff_mul_eq_mul
#align rat.lt_def Rat.lt_def

#noalign rat.nonneg_iff_zero_le

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, add_sub_add_left_eq_sub, ← Rat.le_iff_sub_nonneg]
#align rat.add_le_add_left Rat.add_le_add_left

instance instLinearOrderedCommRing : LinearOrderedCommRing ℚ where
  __ := Rat.linearOrder
  __ := Rat.commRing
  zero_le_one := by decide
  add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
  mul_pos a b ha hb := (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedRing ℚ := by infer_instance

instance : OrderedRing ℚ := by infer_instance

instance : LinearOrderedSemiring ℚ := by infer_instance

instance : OrderedSemiring ℚ := by infer_instance

instance : LinearOrderedAddCommGroup ℚ := by infer_instance

instance : OrderedAddCommGroup ℚ := by infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance

instance : OrderedAddCommMonoid ℚ := by infer_instance

@[simp] lemma num_nonpos {a : ℚ} : a.num ≤ 0 ↔ a ≤ 0 := by simpa using @num_nonneg (-a)
@[simp] lemma num_pos {a : ℚ} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
#align rat.num_pos_iff_pos Rat.num_pos
@[simp] lemma num_neg {a : ℚ} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg

@[deprecated] alias num_nonneg_iff_zero_le := num_nonneg -- 2024-02-16
@[deprecated] alias num_pos_iff_pos := num_pos -- 2024-02-16

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_le]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · apply not_congr
    simp [div_def', Rat.divInt_le_divInt d_pos b_pos]
#align rat.div_lt_div_iff_mul_lt_mul Rat.div_lt_div_iff_mul_lt_mul

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_def]
#align rat.lt_one_iff_num_lt_denom Rat.lt_one_iff_num_lt_denom

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  rcases le_total q 0 with hq | hq
  · rw [abs_of_nonpos hq]
    rw [← num_divInt_den q, ← zero_divInt, Rat.divInt_le_divInt (mod_cast q.pos) zero_lt_one,
      mul_one, zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def]
  · rw [abs_of_nonneg hq]
    rw [← num_divInt_den q, ← zero_divInt, Rat.divInt_le_divInt zero_lt_one (mod_cast q.pos),
      mul_one, zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_divInt_den]
#align rat.abs_def Rat.abs_def

end Rat
