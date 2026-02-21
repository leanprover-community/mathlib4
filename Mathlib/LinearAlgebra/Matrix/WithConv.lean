/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.WithConv
public import Mathlib.LinearAlgebra.Matrix.Hadamard

/-! The convolutive star ring on matrices

In this file, we provide the star algebra instance on `WithConv (Matrix m n R)` given by
the Hadamard product and intrinsic star (i.e., the star of each element in the matrix). -/

@[expose] public section

variable {α β m n : Type*}

open Matrix WithConv

instance [Mul α] : Mul (WithConv (Matrix m n α)) where mul a b := toConv (a.ofConv ⊙ b.ofConv)

lemma convMul_def [Mul α] (x y : WithConv (Matrix m n α)) :
    x * y = toConv (x.ofConv ⊙ y.ofConv) := rfl

attribute [local simp] convMul_def

instance [Semigroup α] : Semigroup (WithConv (Matrix m n α)) where
  mul_assoc _ _ _ := by simp [convMul_def, hadamard_assoc]

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (WithConv (Matrix m n α)) where
  left_distrib _ _ _ := by simp [hadamard_add]
  right_distrib _ _ _ := by simp [add_hadamard]
  zero_mul := by simp
  mul_zero := by simp

instance [CommMagma α] : CommMagma (WithConv (Matrix m n α)) where
  mul_comm := by simp [hadamard_comm]

instance [One α] : One (WithConv (Matrix m n α)) where one := toConv (of 1)

lemma convOne_def [One α] : (1 : WithConv (Matrix m n α)) = toConv (of 1) := rfl

attribute [local simp] convOne_def

instance [MulOneClass α] : MulOneClass (WithConv (Matrix m n α)) where
  one_mul := by simp
  mul_one := by simp

instance [Monoid α] : Monoid (WithConv (Matrix m n α)) where
instance [CommMonoid α] : CommMonoid (WithConv (Matrix m n α)) where
instance [NonAssocSemiring α] : NonAssocSemiring (WithConv (Matrix m n α)) where
instance [NonUnitalSemiring α] : NonUnitalSemiring (WithConv (Matrix m n α)) where
instance [NonUnitalNonAssocCommSemiring α] :
    NonUnitalNonAssocCommSemiring (WithConv (Matrix m n α)) where
instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (WithConv (Matrix m n α)) where
instance [NonAssocCommSemiring α] : NonAssocCommSemiring (WithConv (Matrix m n α)) where
instance [Semiring α] : Semiring (WithConv (Matrix m n α)) where
instance [CommSemiring α] : CommSemiring (WithConv (Matrix m n α)) where
instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (WithConv (Matrix m n α)) where
instance [NonUnitalNonAssocCommRing α] : NonUnitalNonAssocCommRing (WithConv (Matrix m n α)) where
instance [NonUnitalRing α] : NonUnitalRing (WithConv (Matrix m n α)) where
instance [NonUnitalCommRing α] : NonUnitalCommRing (WithConv (Matrix m n α)) where
instance [NonAssocRing α] : NonAssocRing (WithConv (Matrix m n α)) where
instance [NonAssocCommRing α] : NonAssocCommRing (WithConv (Matrix m n α)) where
instance [Ring α] : Ring (WithConv (Matrix m n α)) where
instance [CommRing α] : CommRing (WithConv (Matrix m n α)) where

instance [Star α] : Star (WithConv (Matrix m n α)) where star x := toConv (x.ofConv.map star)

lemma intrinsicStar_def [Star α] (x : WithConv (Matrix m n α)) :
    star x = toConv (x.ofConv.map star) := rfl

attribute [local simp] intrinsicStar_def

instance [InvolutiveStar α] : InvolutiveStar (WithConv (Matrix m n α)) where
  star_involutive _ := by ext; simp

instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (WithConv (Matrix m n α)) where
  star_add _ _ := by simp [Matrix.map_add]

instance [Mul α] [StarMul α] : StarMul (WithConv (Matrix m n α)) where
  star_mul _ _ := by ext; simp

instance [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (WithConv (Matrix m n α)) where
  star_add := by simp

instance [Monoid β] [MulAction β α] [Mul α] [SMulCommClass β α α] :
    SMulCommClass β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_comm := by simp

instance [Monoid β] [MulAction β α] [Mul α] [IsScalarTower β α α] :
    IsScalarTower β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_assoc := by simp

instance [CommSemiring β] [Semiring α] [Algebra β α] : Algebra β (WithConv (Matrix m n α)) :=
  .ofModule smul_mul_assoc mul_smul_comm
