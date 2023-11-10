/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Ring.InjSurj

#align_import algebra.order.field.inj_surj from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Pulling back linearly ordered fields along injective maps.

-/


open Function OrderDual

variable {ι α β : Type*}

namespace Function

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedSemifield` under an injective map. -/
@[reducible]
def Injective.linearOrderedSemifield [LinearOrderedSemifield α] [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [SMul ℕ β] [NatCast β] [Inv β] [Div β] [Pow β ℤ] [Sup β] [Inf β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedSemifield β :=
  { hf.linearOrderedSemiring f zero one add mul nsmul npow nat_cast hsup hinf,
    hf.semifield f zero one add mul inv div nsmul npow zpow nat_cast with }
#align function.injective.linear_ordered_semifield Function.Injective.linearOrderedSemifield


-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedField` under an injective map. -/
@[reducible]
def Injective.linearOrderedField [LinearOrderedField α] [Zero β] [One β] [Add β] [Mul β] [Neg β]
    [Sub β] [Pow β ℕ] [SMul ℕ β] [SMul ℤ β] [SMul ℚ β] [NatCast β] [IntCast β]
    [RatCast β] [Inv β] [Div β] [Pow β ℤ] [Sup β] [Inf β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedField β :=
  { hf.linearOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast hsup hinf,
    hf.field f zero one add mul neg sub inv div nsmul zsmul qsmul npow zpow nat_cast int_cast
      rat_cast with }
#align function.injective.linear_ordered_field Function.Injective.linearOrderedField

end Function
