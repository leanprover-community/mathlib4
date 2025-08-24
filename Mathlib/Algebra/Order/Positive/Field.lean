/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Positive.Ring

/-!
# Algebraic structures on the set of positive numbers

In this file we prove that the set of positive elements of a linear ordered field is a linear
ordered commutative group.
-/


namespace Positive

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K]

instance instInv : Inv { x : K // 0 < x } := ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]
theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K) :=
  rfl

instance instDiv : Div { x : K // 0 < x } := ⟨fun x y ↦ ⟨x / y, div_pos x.2 y.2⟩⟩

@[simp]
theorem val_div (x y : { x : K // 0 < x }) : (x / y).1 = x.1 / y.1 := rfl

instance instZPow : Pow { x : K // 0 < x } ℤ :=
  ⟨fun x n => ⟨(x : K) ^ n, zpow_pos x.2 _⟩⟩

@[simp]
theorem coe_zpow (x : { x : K // 0 < x }) (n : ℤ) : ↑(x ^ n) = (x : K) ^ n :=
  rfl

instance instGroup : Group { x : K // 0 < x } where
  inv_mul_cancel a := by ext; simp [a.2.ne']
  div_eq_mul_inv a b := Subtype.eq <| div_eq_mul_inv a.1 b.1

end DivisionSemiring

instance instCommGroup {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] :
    CommGroup { x : K // 0 < x } where

end Positive
