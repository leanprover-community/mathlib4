/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Order.Hom.CompleteLattice

/-!
# Quantale homomorphism classes

This file defines morphisms between (additive) quantales

## Types of morphisms

* `AddQuantaleHom`: Additive quantale homomorphisms
* `QuantaleHom`: Quantale homomorphisms

As isomorphism, `OrderMonoidIso` - denoted `α ≃*o` works also for (additive) Quantales.

## Notation

* `→ₙ+q`: Bundled additive (non-unital) quantale homs.
* `→ₙ*q`: Bundled (non-unital) quantale homs.

## Implementation notes

The implementation follows largely the style of `Mathlib.Algebra.Order.Hom.Monoid`.

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom
as a function via this coercion.

In the file `Mathlib.Algebra.Order.Hom.Monoid` it is mentioned that there used to be classes:
`OrderAddMonoidHomClass` etc., but that in #10544 there was a migration from these typeclasses to
assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`.
We follow that approach here as well, and only define `AddQuantaleHom` without needing
`AddQuantaleHomClass`.

## Tags

quantale, ordered semigroup, complete lattice

-/

open Function

variable {F α β γ δ : Type*}

section AddQuantale

/-- `α →ₙ+q β` is the type of monotone functions `α → β` that preserve the `AddQuantale`
structure.

When possible, instead of parametrizing results over `(f : α →ₙ+q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
structure AddQuantaleHom (α β : Type*)
  [AddSemigroup α] [CompleteLattice α] [AddSemigroup β] [CompleteLattice β]
  extends α →ₙ+ β, sSupHom α β

/-- Infix notation for `AddQuantaleHom`. -/
infixr:25 " →ₙ+q " => AddQuantaleHom

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

section Quantale

/-- `α →ₙ*q β` is the type of monotone functions `α → β` that preserve the `Quantale`
structure.

When possible, instead of parametrizing results over `(f : α →ₙ*q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
@[to_additive]
structure QuantaleHom (α β : Type*)
  [Semigroup α] [CompleteLattice α] [Semigroup β] [CompleteLattice β]
  extends α →ₙ* β, sSupHom α β

/-- Infix notation for `AddQuantaleHom`. -/
infixr:25 " →ₙ*q " => QuantaleHom

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `MulHomClass F α β` and `sSupHomClass F α β`
into an actual `QuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ*q β`. -/
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `AddHomClass F α β` and `sSupHomClass F α β`
into an actual `AddQuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ+q β`."]
def toQuantaleHom [MulHomClass F α β] [sSupHomClass F α β] (f : F) :
    α →ₙ*q β := { (f : α →ₙ* β) with map_sSup' := sSupHomClass.map_sSup f }

/-- Any type satisfying `QuantaleHomClass` can be cast into `QuantaleHom` via
  `QuantaleHomClass.toQuantaleHom`. -/
@[to_additive "Any type satisfying `AddQuantaleHomClass` can be cast into `AddQuantaleHom` via
  `AddQuantaleHomClass.toAddQuantaleHom`."]
instance [MulHomClass F α β] [sSupHomClass F α β] : CoeTC F (α →ₙ*q β) :=
  ⟨toQuantaleHom⟩

end Quantale

namespace QuantaleHom

/- Now, to be honest, I don't really understand which theorems below are necessary
and which ones should already be there in some other way. While proving some,
I got the impression I was overlooking something very basic.

My main confusion at the moment, is how `HomClass`es are being used, and how
I get automatic results about `Hom`s from the `HomClass` theorems. See for
example the `toOrderHom` theorem below.

Which ones should I have, which ones do I not need, and why??
-/

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β] {f g : α →ₙ*q β}

@[to_additive]
instance : FunLike (α →ₙ*q β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨ _ ⟩, _⟩ := f
    obtain ⟨⟨ _ ⟩, _⟩ := g
    congr

@[to_additive]
instance : MulHomClass (α →ₙ*q β) α β where
  map_mul f _ _ := f.map_mul' _ _

@[to_additive]
instance : sSupHomClass (α →ₙ*q β) α β where
  map_sSup f := f.map_sSup'

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
theorem toFun_eq_coe (f : α →ₙ*q β) : f.toFun = (f : α → β) :=
  rfl

@[to_additive (attr := simp)]
theorem coe_mk (f : α →ₙ* β) (h) : (QuantaleHom.mk f h : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
theorem mk_coe (f : α →ₙ*q β) (h) : QuantaleHom.mk (f : α →ₙ* β) h = f := rfl

/-- Reinterpret a quantale homomorphism as a supsemilattice homomorphism-/
@[to_additive "Reinterpret an additive quantale homomorphism as a supsemilattice homomorphism."]
def toSupBotHom (f : α →ₙ*q β) : SupBotHom α β where
  toFun := f
  map_sup':= sSupHomClass.toSupBotHomClass.map_sup f
  map_bot':= sSupHomClass.toSupBotHomClass.map_bot f

@[to_additive (attr := simp)]
theorem coe_SupBotHom (f : α →ₙ*q β) : ((f : SupBotHom α β) : α → β) = f :=
  rfl

/-- Reinterpret a quantale homomorphism as an order homomorphism. -/
@[to_additive "Reinterpret an additive quantale homomorphism as an order homomorphism."]
def toOrderHom (f : α →ₙ*q β) : α →o β where
  toFun := f
  monotone' := by
    -- This should not be so elaborate, what am I overlooking? --
    intro x y h
    apply le_of_sup_eq
    rw [← (f : SupBotHom α β).map_sup']
    dsimp only [toFun_eq_coe]
    congr
    apply sup_of_le_right
    exact h

@[to_additive (attr := simp)]
theorem coe_MulHom (f : α →ₙ*q β) : ((f : α →ₙ* β) : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_orderHom (f : α →ₙ*q β) : ((f : α →o β) : α → β) = f :=
  rfl

@[to_additive]
theorem toMulHom_injective : Injective (toMulHom : _ → α →ₙ* β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0

@[to_additive]
theorem toOrderHom_injective : Injective (toOrderHom : _ → α →o β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0

end QuantaleHom

/- Theory connecting `QuantaleHom`'s to `OrderMonoidIso` (or technically `OrderMulIso`) -/

namespace OrderMonoidIso

section QuantaleHom

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β]

/-- Reinterpret an ordered mul isomorphism as a quantale homomorphism -/
@[to_additive "Reinterpret an ordered additive mul isomomorphism as an additive
quantale homomorphism."]
def toQuantaleHom (f : α ≃*o β) : α →ₙ*q β where
  toFun := f.toFun
  map_mul' := f.map_mul'
  map_sSup' := by simp only [toMulEquiv_eq_coe, MulEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe, coe_mulEquiv, map_sSup, implies_true]

@[to_additive (attr := simp)]
theorem coe_QuantaleHom (f : α ≃*o β) : ((f : α →ₙ*q β) : α → β) = f :=
  rfl

@[to_additive]
theorem toQuantaleHom_injective : Injective (toQuantaleHom : _ → α →ₙ*q β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0

/- Todo: basically proving that QuantaleHoms form a category (composition and identity) -/

end QuantaleHom

end OrderMonoidIso
