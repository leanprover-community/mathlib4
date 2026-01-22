/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! # Lemmas for the `algebra` tactic.
-/

@[expose] public section

open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Algebra

section ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/- evalCast -/
theorem isInt_negOfNat_eq {a : A} {lit : ℕ} (h : IsInt a (Int.negOfNat lit)) :
    a = algebraMap R A (Int.rawCast (Int.negOfNat lit) + 0 : R) + 0 := by
  simp [h.out]


-- /- eval -/
-- theorem eval_neg {a a' b : A} (ha : a = a') (hb : -a' = b) :
--     -a = b := by
--   grind

-- /- eval -/
-- theorem eval_sub {a b a' b' c : A} (ha : a = a') (hb : b = b') (hc : a' - b' = c) :
--     a - b = c := by
--   grind

end ring

section semifield

variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

/- evalCast -/
theorem isNNRat_eq_rawCast {a : A} {n d : ℕ} (h : IsNNRat a n d) :
    a = algebraMap R A (NNRat.rawCast n d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_nnrat h]

end semifield

section field

variable {R A : Type*} [Field R] [Field A] [Algebra R A]

/- evalCast -/
theorem isRat_eq_rawCast {a : A} {n d : ℕ} (h : IsRat a (.negOfNat n) d) :
    a = algebraMap R A (Rat.rawCast (.negOfNat n) d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_rat h]

end field

variable {R A : Type*} [sR : CommSemiring R] [sA : CommSemiring A] [sAlg : Algebra R A]

/- evalCast -/
theorem isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0 := by
  have := h.out
  simp [this]

section cleanup

variable {n d : ℕ}

section cleanupSMul

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

end cleanupSMul
section cleanupConsts

theorem ofNat_smul {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [n.AtLeastTwo] {a : A} :
    (ofNat(n) : R) • a = ofNat(n) * a := by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]

theorem neg_ofNat_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo] :
    (- ofNat(n) : R) • a = - (ofNat(n)) * a := by
  simpa [← nat_rawCast_2] using ofNat_smul

theorem neg_1_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    (-1 : R) • a = - a := by
  simp

theorem nnRat_ofNat_smul_1 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    (1 / ofNat(d) : R) • a = (1 / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

theorem nnRat_ofNat_smul_2 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    (ofNat(n) / ofNat(d) : R) • a = (ofNat(n) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

theorem rat_ofNat_smul_1 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    ((- 1) / ofNat(d) : R) • a = ((- 1) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

theorem rat_ofNat_smul_2 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    ((- ofNat(n)) / ofNat(d) : R) • a = ((- ofNat(n)) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

end cleanupConsts

end cleanup

section equateScalars

/- ExProd.equateZero -/
theorem smul_one_eq_zero {r : R} (h : r = 0) :
    r • (1 : A) = 0 := by
  simp [h]

/- ExProd.equateZero -/
theorem add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) :
    a + b = 0 := by
  simp [ha, hb]

/- ExProd.equateScalarsProd -/
theorem smul_one_eq_smul_one' {r s : R} (h : r = s) :
    r • (1 : A) = s • 1 := by
  simp [h]

/- equateScalarsSum -/
theorem add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A}
    (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
theorem add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A}
    (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
theorem add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ = b₁) (hb : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  rfl

/- matchScalarsAux -/
omit sA in
theorem eq_trans_trans {e₁ e₂ a b : A}
    (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
    e₁ = e₂ := by
  subst_vars
  rfl

/- ExProd.equateScalarsProd -/
theorem mul_eq_mul_of_eq {c a b : A}
    (h : a = b) :
    c * a = c * b := by
  simp [h]

end equateScalars

end Mathlib.Tactic.Algebra
