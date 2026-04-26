/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.FunLike.Basic

/-! # Group structure for `FunLike`
In this file we provide typeclasses for the compatibility of algebraic structures and`FunLike`
instances.
-/

public section

section Def

section Zero

/-- `IsZeroApply F α β` states for all `x : α`, `(0 : F) x = 0`. -/
class IsZeroApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Zero β] [Zero F] where
  zero_apply (x : α) : (0 : F) x = 0

/-- `IsOneApply F α β` states for all `x : α`, `(1 : F) x = 1`. -/
@[to_additive]
class IsOneApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [One β] [One F] where
  one_apply (x : α) : (1 : F) x = 1

@[to_additive (attr := simp, grind =)] alias one_apply := IsOneApply.one_apply

end Zero

section Add

/-- `IsAddApply F α β` states for all `f g : F` and `x : α`, `(f + g) x = f x + g x`. -/
class IsAddApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Add β] [Add F] where
  add_apply (f g : F) (x : α) : (f + g) x = f x + g x

/-- `IsMulApply F α β` states for all `f g : F` and `x : α`, `(f * g) x = f x * g x`. -/
@[to_additive]
class IsMulApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Mul β] [Mul F] where
  mul_apply (f g : F) (x : α) : (f * g) x = f x * g x

@[to_additive (attr := simp, grind =)] alias mul_apply := IsMulApply.mul_apply

end Add

section Sub

/-- `IsSubApply F α β` states for all `f g : F` and `x : α`, `(f - g) x = f x - g x`. -/
class IsSubApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Sub β] [Sub F] where
  sub_apply (f g : F) (x : α) : (f - g) x = f x - g x

/-- `IsDivApply F α β` states for all `f g : F` and `x : α`, `(f / g) x = f x / g x`. -/
@[to_additive]
class IsDivApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Div β] [Div F] where
  div_apply (f g : F) (x : α) : (f / g) x = f x / g x

@[to_additive (attr := simp, grind =)] alias div_apply := IsDivApply.div_apply

end Sub

section Neg

/-- `IsNegApply F α β` states for all `f : F` and `x : α`, `(-f) x = -f x`. -/
class IsNegApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Neg β] [Neg F] where
  neg_apply (f : F) (x : α) : (-f) x = -f x

/-- `IsInvApply F α β` states for all `f : F` and `x : α`, `f⁻¹ x = (f x)⁻¹`. -/
@[to_additive]
class IsInvApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Inv β] [Inv F] where
  inv_apply (f : F) (x : α) : f⁻¹ x = (f x)⁻¹

@[to_additive (attr := simp, grind =)] alias inv_apply := IsInvApply.inv_apply

end Neg

section SMul

/-- `IsVAddApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n +ᵥ f) x = n +ᵥ f x`. -/
class IsVAddApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [VAdd M β] [VAdd M F] where
  vadd_apply (f : F) (n : M) (x : α) : (n +ᵥ f) x = n +ᵥ f x

/-- `IsSMulApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n • f) x = n • f x`. -/
@[to_additive]
class IsSMulApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [SMul M β] [SMul M F] where
  smul_apply (f : F) (r : M) (x : α) : (r • f) x = r • f x

@[to_additive (attr := simp, grind =)] alias smul_apply := IsSMulApply.smul_apply

/-- `IsPowApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(f ^ n) x = (f x) ^ n`. -/
@[to_additive IsSMulApply]
class IsPowApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [Pow β M] [Pow F M] where
  pow_apply (f : F) (n : M) (x : α) : (f ^ n) x = (f x) ^ n

@[to_additive] alias pow_apply := IsPowApply.pow_apply

attribute [simp, grind =] pow_apply

end SMul

end Def

namespace FunLike

variable {M M' F α β : Type*} [FunLike F α β]

section Coercion

@[to_additive (attr := norm_cast)]
theorem coe_one [One F] [One β] [IsOneApply F α β] : ↑(1 : F) = (1 : α → β) := by ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : ↑(f * g) = (f : α → β) * g := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_div [Div F] [Div β] [IsDivApply F α β] (f g : F) : ↑(f / g) = (f : α → β) / g := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_inv [Inv F] [Inv β] [IsInvApply F α β] (f : F) : ↑(f⁻¹) = (f : α → β)⁻¹ := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (n : M) (f : F) :
    ↑(n • f) = n • (f : α → β) := by
  ext; simp

@[to_additive coe_smul']
theorem coe_pow [Pow F M] [Pow β M] [IsPowApply M F α β] (f : F) (n : M) :
    ↑(f ^ n) = (f : α → β) ^ n := by
  ext; simp

attribute [norm_cast] coe_pow

end Coercion

end FunLike
