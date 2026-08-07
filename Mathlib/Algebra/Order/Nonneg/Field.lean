/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`Nonneg α` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.
-/

@[expose] public section

assert_not_exists abs_inv

open Set

variable {α : Type*}

section NNRat
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

lemma NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

lemma nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps]
def unitsEquivPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R] :
    (Nonneg R)ˣ ≃* { r : R // 0 < r } where
  toFun r := ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

instance inv : Inv (Nonneg α) :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
protected theorem coe_inv (a : Nonneg α) : ((a⁻¹ : Nonneg α) : α) = (a : α)⁻¹ :=
  rfl

@[simp]
theorem inv_mk (hx : 0 ≤ x) :
    (⟨x, hx⟩ : Nonneg α)⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl

instance div : Div (Nonneg α) :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]
protected theorem coe_div (a b : Nonneg α) : ((a / b : Nonneg α) : α) = a / b :=
  rfl

@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : Nonneg α) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl

instance zpow : Pow (Nonneg α) ℤ :=
  ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]
protected theorem coe_zpow (a : Nonneg α) (n : ℤ) :
    ((a ^ n : Nonneg α) : α) = (a : α) ^ n :=
  rfl

@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : Nonneg α) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl

instance instNNRatCast : NNRatCast (Nonneg α) := ⟨fun q ↦ ⟨q, q.cast_nonneg⟩⟩
instance instNNRatSMul : SMul ℚ≥0 (Nonneg α) where
  smul q a := ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩

@[simp, norm_cast] lemma coe_nnratCast (q : ℚ≥0) : (q : Nonneg α) = (q : α) := rfl
@[simp] lemma mk_nnratCast (q : ℚ≥0) : (⟨q, q.cast_nonneg⟩ : Nonneg α) = q := rfl

@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (a : Nonneg α) :
    ↑(q • a) = (q • a : α) := rfl
@[simp] lemma mk_nnqsmul (q : ℚ≥0) (a : α) (ha : 0 ≤ a) :
    (⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha⟩ : Nonneg α) =
      q • a := rfl

instance semifield : Semifield (Nonneg α) := fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

end LinearOrderedSemifield

instance linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommGroupWithZero (Nonneg α) :=
  fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

end Nonneg
