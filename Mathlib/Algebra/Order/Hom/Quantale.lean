/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.Hom.CompleteLattice

/-!
# Quantale homomorphism classes

This file defines morphisms between (additive) quantales

## Types of morphisms

* `AddQuantaleHom`: Additive quantale homomorphisms
* `QuantaleHom`: Quantale homomorphisms

As isomorphism, `OrderMonoidIso` as defined in `Mathlib.Algebra.Order.Hom.Monoid`
works also for (additive) Quantales, so we do not need to add any theory for them here.

We do add theorems for identity and composition of (additive) quantale homs, as well
as a theorem showing that any function that maps everything to `⊥` is a quantale hom.

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

/-- Converts an AddQuantaleHom to a sSupHom -/
add_decl_doc AddQuantaleHom.tosSupHom

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
@[to_additive existing]
structure QuantaleHom (α β : Type*)
  [Semigroup α] [CompleteLattice α] [Semigroup β] [CompleteLattice β]
  extends α →ₙ* β, sSupHom α β

/-- Converts a QuantaleHom to a sSupHom -/
add_decl_doc QuantaleHom.tosSupHom

/-- Infix notation for `QuantaleHom`. -/
infixr:25 " →ₙ*q " => QuantaleHom

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `MulHomClass F α β` and `sSupHomClass F α β`
into an actual `QuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ*q β`. -/
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `AddHomClass F α β` and `sSupHomClass F α β`
into an actual `AddQuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ+q β`."]
def QuantaleHom.ofClass [MulHomClass F α β] [sSupHomClass F α β] (f : F) :
    α →ₙ*q β := { (f : α →ₙ* β) with map_sSup' := sSupHomClass.map_sSup f }

end Quantale

namespace QuantaleHom

variable [Semigroup α] [Semigroup β] [Semigroup γ] [Semigroup δ]
  [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]
  {f g : α →ₙ*q β}

@[to_additive]
instance : FunLike (α →ₙ*q β) α β where
  coe f := f.toFun
  coe_injective' f g h := by congr!

@[to_additive]
instance : MulHomClass (α →ₙ*q β) α β where
  map_mul f _ _ := f.map_mul' _ _

@[to_additive]
instance : sSupHomClass (α →ₙ*q β) α β where
  map_sSup f := f.map_sSup'

@[to_additive]
instance : OrderHomClass (α →ₙ*q β) α β where
  map_rel f := by apply (f : OrderHom α β).monotone'

@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
theorem toFun_eq_coe (f : α →ₙ*q β) : f.toFun = (f : α → β) := rfl

@[to_additive (attr := simp)]
theorem coe_mk (f : α →ₙ* β) (h) : mk f h = f := rfl

@[to_additive (attr := simp)]
theorem mk_coe (f : α →ₙ*q β) (h) : mk (f : α →ₙ* β) h = f := rfl

section Id

/-- The identity map as a quantale homomorphism. -/
@[to_additive "The identity map as an additive quantale homomorphism."]
protected def id : α →ₙ*q α where
  toFun x := x
  map_mul' _ _ := rfl
  map_sSup' _ := by simp_all only [Set.image_id']

@[to_additive (attr := simp)]
theorem coe_id : ⇑(QuantaleHom.id α) = id := rfl

@[to_additive]
instance : Inhabited (α →ₙ*q α) := ⟨QuantaleHom.id α⟩

end Id

section Comp

/-- Composition of `QuantaleHom`s as a `QuantaleHom`. -/
@[to_additive "Composition of `AddQuantaleHom`s as an `AddQuantaleHom`"]
def comp (f : β →ₙ*q γ) (g : α →ₙ*q β) : α →ₙ*q γ :=
  {f.toMulHom.comp (g : α →ₙ* β), f.tosSupHom.comp (g : sSupHom α β) with }

@[to_additive (attr := simp)]
theorem coe_comp (f : β →ₙ*q γ) (g : α →ₙ*q β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_additive (attr := simp)]
theorem comp_apply (f : β →ₙ*q γ) (g : α →ₙ*q β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_additive (attr := simp)]
theorem comp_assoc (f : γ →ₙ*q δ) (g : β →ₙ*q γ) (h : α →ₙ*q β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_additive (attr := simp)]
theorem comp_id (f : α →ₙ*q β) : f.comp (QuantaleHom.id α) = f :=
  rfl

@[to_additive (attr := simp)]
theorem id_comp (f : α →ₙ*q β) : (QuantaleHom.id β).comp f = f :=
  rfl

end Comp

section Bot

/-- `⊥` is the quantale homomorphism sending all elements to `⊥`. -/
@[to_additive "`⊥` is the quantale homomorphism sending all elements to `⊥`."]
instance [IsQuantale β] : Bot (α →ₙ*q β) := ⟨{ (⊥ : sSupHom α β) with
  map_mul' := by
    simp only [sSupHom.toFun_eq_coe, sSupHom.bot_apply, IsQuantale.mul_bot, implies_true]
  }⟩

@[to_additive (attr := simp)]
theorem coe_bot [IsQuantale β] : ⇑(⊥ : α →ₙ*q β) = ⊥ := rfl

end Bot

end QuantaleHom
