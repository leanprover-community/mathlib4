/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.PFunLike

/-!
# Partial monoid and group homomorphisms

This file defines the typeclasses for types whose terms can be seen as partial
group/monoid homomorphisms, namely `MonoidPHomClass` and `AddMonoidPHomClass`. We also define
`ZeroPHomClass`, `OnePHomClass`, `AddPHomClass` and `MulPHomClass` as building blocks for for other
partial homomorphisms.
-/

/-- `ZeroPHomClass F M γ N` states that `F` is a type of partial zero-preserving homomorphisms
with domains of type `γ`. -/
class ZeroPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [Zero M] [Zero N]
    [ZeroMemClass γ M] [PFunLike F M γ N] where
  pmap_zero : ∀ (f : F), f 0 = 0

export ZeroPHomClass (pmap_zero)

attribute [simp] pmap_zero

/-- `OnePHomClass F M γ N` states that `F` is a type of partial one-preserving homomorphisms
with domains of type `γ`. -/
@[to_additive]
class OnePHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [One M] [One N]
    [OneMemClass γ M] [PFunLike F M γ N] where
  pmap_one : ∀ (f : F), f 1 = 1

export OnePHomClass (pmap_one)

attribute [simp] pmap_one

/-- `AddPHomClass F M γ N` states that `F` is a type of partial addition-preserving homomorphisms
with domains of type `γ`. -/
class AddPHomClass (F : Type*) (M γ N : outParam Type*)
    [SetLike γ M] [Add M] [Add N] [AddMemClass γ M] [PFunLike F M γ N] where
  pmap_add : ∀ (f : F) (x y : PFunLike.domain f), f (x + y) = f x + f y

export AddPHomClass (pmap_add)

attribute [simp] pmap_add

/-- `MulPHomClass F M γ N` states that `F` is a type of partial multiplication-preserving
homomorphisms with domains of type `γ`. -/
@[to_additive]
class MulPHomClass (F : Type*) (M γ N : outParam Type*)
    [SetLike γ M] [Mul M] [Mul N] [MulMemClass γ M] [PFunLike F M γ N] where
  pmap_mul : ∀ (f : F) (x y : PFunLike.domain f), f (x * y) = f x * f y

export MulPHomClass (pmap_mul)

attribute [simp] pmap_mul

/-- `AddMonoidPHomClass F M γ N` states that `F` is a type of partial `AddZeroClass`-preserving
homomorphisms with domains of type `γ`. -/
class AddMonoidPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M]
    [AddZeroClass M] [AddZeroClass N] [AddSubmonoidClass γ M] [PFunLike F M γ N]
    extends AddPHomClass F M γ N, ZeroPHomClass F M γ N

/-- `MonoidPHomClass F M γ N` states that `F` is a type of partial `MulOneClass`-preserving
homomorphisms with domains of type `γ`. -/
@[to_additive]
class MonoidPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M]
    [MulOneClass M] [MulOneClass N] [SubmonoidClass γ M] [PFunLike F M γ N]
    extends MulPHomClass F M γ N, OnePHomClass F M γ N

@[to_additive]
theorem pmap_mul_eq_one {F M γ N : Type*} [MulOneClass M] [MulOneClass N] [SetLike γ M]
    [SubmonoidClass γ M] [PFunLike F M γ N] [MonoidPHomClass F M γ N]
    {f : F} {a b : PFunLike.domain f} (h : a * b = 1) : f a * f b = 1 := by
  rw [← MulPHomClass.pmap_mul, h, OnePHomClass.pmap_one]

@[to_additive, simp]
theorem pmap_inv {F G γ H : Type*} [Group G] [DivisionMonoid H] [SetLike γ G]
    [SubgroupClass γ G] [PFunLike F G γ H] [MonoidPHomClass F G γ H]
    {f : F} (a : PFunLike.domain f) : f (a⁻¹) = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| pmap_mul_eq_one <| inv_mul_cancel _

@[to_additive, simp]
theorem pmap_div {F G γ H : Type*} [Group G] [DivisionMonoid H] [SetLike γ G]
    [SubgroupClass γ G] [PFunLike F G γ H] [MonoidPHomClass F G γ H]
    {f : F} (a b : PFunLike.domain f) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, MulPHomClass.pmap_mul, pmap_inv]
