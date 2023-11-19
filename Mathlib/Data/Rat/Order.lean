/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.Cast.Lemmas

#align_import data.rat.order from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.


## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable (a b c : ℚ)

open Rat

/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def Nonneg (r : ℚ) : Prop :=
  0 ≤ r.num
#align rat.nonneg Rat.Nonneg

@[simp]
theorem divInt_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).Nonneg ↔ 0 ≤ a := by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_den'] at ha
  simp only [Rat.Nonneg]
  have d0 := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h₁)
  have := (divInt_eq_iff (ne_of_gt h) (ne_of_gt d0)).1 ha
  constructor <;> intro h₂
  · apply nonneg_of_mul_nonneg_left _ d0
    rw [this]
    exact mul_nonneg h₂ (le_of_lt h)
  · apply nonneg_of_mul_nonneg_left _ h
    rw [← this]
    exact mul_nonneg h₂ (Int.ofNat_zero_le _)
#align rat.mk_nonneg Rat.divInt_nonneg

protected theorem nonneg_add {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a + b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      simp only [d₁0, d₂0, h₁, h₂, mul_pos, divInt_nonneg, add_def'', Ne.def,
        Nat.cast_eq_zero, not_false_iff]
      intro n₁0 n₂0
      apply add_nonneg <;> apply mul_nonneg <;> · first |assumption|apply Int.ofNat_zero_le
#align rat.nonneg_add Rat.nonneg_add

protected theorem nonneg_mul {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a * b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      rw [mul_def' d₁0.ne.symm d₂0.ne.symm, divInt_nonneg _ d₁0, divInt_nonneg _ d₂0,
        divInt_nonneg _ (mul_pos d₁0 d₂0)]
      apply mul_nonneg
#align rat.nonneg_mul Rat.nonneg_mul

protected theorem nonneg_antisymm {a} : Rat.Nonneg a → Rat.Nonneg (-a) → a = 0 :=
  numDenCasesOn' a fun n d h => by
    have d0 : 0 < (d : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h)
    rw [divInt_nonneg _ d0, neg_def, divInt_nonneg _ d0, Right.nonneg_neg_iff,
      divInt_eq_zero d0.ne.symm]
    exact fun h₁ h₂ => le_antisymm h₂ h₁
#align rat.nonneg_antisymm Rat.nonneg_antisymm

protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) := by
  cases' a with n; exact Or.imp_right neg_nonneg_of_nonpos (le_total 0 n)
#align rat.nonneg_total Rat.nonneg_total

instance decidableNonneg : Decidable (Rat.Nonneg a) := by
  cases a; unfold Rat.Nonneg; infer_instance
#align rat.decidable_nonneg Rat.decidableNonneg

-- Porting note: Now `Std` defines `≤` on `Rat`.
-- This is the old mathlib3 definition.
/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ Rat.Nonneg (b - a)`. Use `a ≤ b` instead of
`Rat.le a b`. -/
protected def le' (a b : ℚ) := Rat.Nonneg (b - a)
#align rat.le Rat.le'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
-- Porting note: TODO move
@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) :
    C a :=
  numDenCasesOn a fun n d h h' => by
    rw [←mk_eq_divInt _ _ h.ne' h']
    exact H n d h.ne' _

-- Porting note: TODO can this be shortened?
protected theorem le_iff_Nonneg (a b : ℚ) : a ≤ b ↔ Rat.Nonneg (b - a) :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      change Rat.blt _ _ = false ↔ _
      unfold Rat.blt
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, not_lt, ite_eq_left_iff, not_and, not_le]
      split_ifs with h h'
      · rw [Rat.sub_def]
        simp only [Rat.Nonneg, false_iff, not_le]
        simp only [normalize_eq]
        apply Int.ediv_neg'
        · rw [sub_neg]
          apply lt_of_lt_of_le
          · apply mul_neg_of_neg_of_pos h.1
            rwa [Nat.cast_pos, pos_iff_ne_zero]
          · apply mul_nonneg h.2 (Nat.cast_nonneg _)
        · simp only [Nat.cast_pos]
          apply Nat.gcd_pos_of_pos_right
          apply mul_pos <;> rwa [pos_iff_ne_zero]
      · simp only [divInt_ofNat, ←zero_iff_num_zero, mkRat_eq_zero hb] at h'
        simp [h', Rat.Nonneg]
      · simp [Rat.Nonneg, Rat.sub_def, normalize_eq]
        refine ⟨fun H => ?_, fun H _ => ?_⟩
        · refine Int.ediv_nonneg ?_ (Nat.cast_nonneg _)
          rw [sub_nonneg]
          push_neg at h
          obtain hb|hb := Ne.lt_or_lt h'
          · apply H
            intro H'
            exact (hb.trans H').false.elim
          · obtain ha|ha := le_or_lt na 0
            · apply le_trans <| mul_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
              exact mul_nonneg hb.le (Nat.cast_nonneg _)
            · exact H (fun _ => ha)
        · rw [←sub_nonneg]
          contrapose! H
          apply Int.ediv_neg' H
          simp only [Nat.cast_pos]
          apply Nat.gcd_pos_of_pos_right
          apply mul_pos <;> rwa [pos_iff_ne_zero]

protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_Nonneg]
  show Rat.Nonneg _ ↔ _
  rw [← sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
#align rat.le_def Rat.le_def

protected theorem le_refl : a ≤ a := by
  rw [Rat.le_iff_Nonneg]
  show Rat.Nonneg (a - a)
  rw [sub_self]
  exact le_refl (0 : ℤ)
#align rat.le_refl Rat.le_refl

protected theorem le_total : a ≤ b ∨ b ≤ a := by
  have := Rat.nonneg_total (b - a)
  rw [Rat.le_iff_Nonneg, Rat.le_iff_Nonneg]
  rwa [neg_sub] at this
#align rat.le_total Rat.le_total

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_Nonneg] at hab hba
  rw [sub_eq_add_neg] at hba
  rw [←neg_sub, sub_eq_add_neg] at hab
  have := eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hba hab)
  rwa [neg_neg] at this
#align rat.le_antisymm Rat.le_antisymm

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_Nonneg] at hab hbc
  have : Rat.Nonneg (b - a + (c - b)) := Rat.nonneg_add hab hbc
  simp_rw [sub_eq_add_neg, add_left_comm (b + -a) c (-b), add_comm (b + -a) (-b),
    add_left_comm (-b) b (-a), add_comm (-b) (-a), add_neg_cancel_comm_assoc,
    ← sub_eq_add_neg] at this
  rw [Rat.le_iff_Nonneg]
  exact this
#align rat.le_trans Rat.le_trans

protected theorem not_le {a b : ℚ} : ¬a ≤ b ↔ b < a := (Bool.not_eq_false _).to_iff

instance linearOrder : LinearOrder ℚ where
  le_refl := Rat.le_refl
  le_trans := @Rat.le_trans
  le_antisymm := @Rat.le_antisymm
  le_total := Rat.le_total
  decidableLE _ _ := by infer_instance
  lt_iff_le_not_le _ _ := by
    rw [← Rat.not_le, and_iff_right_of_imp (Rat.le_total _ _).resolve_left]

-- Extra instances to short-circuit type class resolution
instance : LT ℚ := by infer_instance

instance : DistribLattice ℚ := by infer_instance

instance : Lattice ℚ := by infer_instance

instance : SemilatticeInf ℚ := by infer_instance

instance : SemilatticeSup ℚ := by infer_instance

instance : Inf ℚ := by infer_instance

instance : Sup ℚ := by infer_instance

instance : PartialOrder ℚ := by infer_instance

instance : Preorder ℚ := by infer_instance

protected theorem le_def' {p q : ℚ} : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← @num_den q, ← @num_den p]
  conv_rhs => simp only [num_den]
  exact Rat.le_def (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
#align rat.le_def' Rat.le_def'

protected theorem lt_def {p q : ℚ} : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [lt_iff_le_and_ne, Rat.le_def']
  suffices p ≠ q ↔ p.num * q.den ≠ q.num * p.den by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact not_iff_not.mpr eq_iff_mul_eq_mul
#align rat.lt_def Rat.lt_def

theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a := by
  rw [Rat.le_iff_Nonneg]
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0)
  simp
#align rat.nonneg_iff_zero_le Rat.nonneg_iff_zero_le

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
  | ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩
#align rat.num_nonneg_iff_zero_le Rat.num_nonneg_iff_zero_le

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_Nonneg, add_sub_add_left_eq_sub, Rat.le_iff_Nonneg]
#align rat.add_le_add_left Rat.add_le_add_left

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rw [← nonneg_iff_zero_le] at ha hb ⊢; exact Rat.nonneg_mul ha hb
#align rat.mul_nonneg Rat.mul_nonneg

instance : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder, Rat.semiring with
    zero_le_one := by decide
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
    mul_pos := fun a b ha hb =>
      lt_of_le_of_ne (Rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
        (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm }

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedCommRing ℚ := by infer_instance

instance : LinearOrderedRing ℚ := by infer_instance

instance : OrderedRing ℚ := by infer_instance

instance : LinearOrderedSemiring ℚ := by infer_instance

instance : OrderedSemiring ℚ := by infer_instance

instance : LinearOrderedAddCommGroup ℚ := by infer_instance

instance : OrderedAddCommGroup ℚ := by infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance

instance : OrderedAddCommMonoid ℚ := by infer_instance

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le <| by
    simpa [(by cases a; rfl : (-a).num = -a.num)] using @num_nonneg_iff_zero_le (-a)
#align rat.num_pos_iff_pos Rat.num_pos_iff_pos

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_le]
  apply and_congr
  · simp [div_num_den, Rat.le_def b_pos d_pos]
  · apply not_congr
    simp [div_num_den, Rat.le_def d_pos b_pos]
#align rat.div_lt_div_iff_mul_lt_mul Rat.div_lt_div_iff_mul_lt_mul

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_def]
#align rat.lt_one_iff_num_lt_denom Rat.lt_one_iff_num_lt_denom

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  cases' le_total q 0 with hq hq
  · rw [abs_of_nonpos hq]
    rw [← @num_den q, ← divInt_zero_one, Rat.le_def (Int.coe_nat_pos.2 q.pos) zero_lt_one, mul_one,
      zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def, num_den]
  · rw [abs_of_nonneg hq]
    rw [← @num_den q, ← divInt_zero_one, Rat.le_def zero_lt_one (Int.coe_nat_pos.2 q.pos), mul_one,
      zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_den]
#align rat.abs_def Rat.abs_def

end Rat

-- We make some assertions here about declarations that do not need to be in the import dependencies
-- for this file, but have been in the past.
assert_not_exists Fintype

assert_not_exists Set.Icc

assert_not_exists GaloisConnection

-- These are less significant, but should not be relaxed until at least after port to Lean 4.
assert_not_exists LinearOrderedCommGroupWithZero
