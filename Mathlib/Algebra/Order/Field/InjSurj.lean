/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.InjSurj

#align_import algebra.order.field.inj_surj from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Pulling back linearly ordered fields along injective maps
-/

open Function OrderDual

variable {ι α β : Type*}

namespace Function.Injective
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [Pow β ℕ] [SMul ℕ β] [SMul ℤ β]
  [SMul ℚ≥0 β] [SMul ℚ β] [NatCast β] [IntCast β] [NNRatCast β] [RatCast β] [Inv β] [Div β]
  [Pow β ℤ] [Sup β] [Inf β] (f : β → α) (hf : Injective f)

/-- Pullback a `LinearOrderedSemifield` under an injective map. -/
-- See note [reducible non-instances]
abbrev linearOrderedSemifield [LinearOrderedSemifield α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedSemifield β where
  __ := hf.linearOrderedCommSemiring f zero one add mul nsmul npow natCast hsup hinf
  __ := hf.semifield f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
#align function.injective.linear_ordered_semifield Function.Injective.linearOrderedSemifield

/-- Pullback a `LinearOrderedField` under an injective map. -/
-- See note [reducible non-instances]
abbrev linearOrderedField [LinearOrderedField α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedField β where
  __ := hf.linearOrderedCommRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
    hsup hinf
  __ := hf.field f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow natCast
    intCast nnratCast ratCast
#align function.injective.linear_ordered_field Function.Injective.linearOrderedField

end Function.Injective
