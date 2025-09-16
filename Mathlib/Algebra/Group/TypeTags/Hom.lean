/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Transport algebra morphisms between additive and multiplicative types.
-/


universe u v

variable {α : Type u} {β : Type v}

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

/-- Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f a.toAdd)
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => f (ofAdd a) |>.toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative [AddZeroClass α] [AddZeroClass β] (f : α →+ β) :
    ⇑(toMultiplicative f) = ofAdd ∘ f ∘ toAdd := rfl

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f a.toMul)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => (f (ofMul a)).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }

@[simp, norm_cast]
lemma MonoidHom.coe_toMultiplicative [MulOneClass α] [MulOneClass β] (f : α →* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => (f a.toMul).toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative' [MulOneClass α] [AddZeroClass β] (f : Additive α →+ β) :
    ⇑(toMultiplicative' f) = ofAdd ∘ f ∘ ofMul := rfl

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditive' [MulOneClass α] [AddZeroClass β] (f : α →* Multiplicative β) :
    ⇑(toAdditive' f) = toAdd ∘ f ∘ toMul := rfl

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => (f a.toAdd).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative'' [AddZeroClass α] [MulOneClass β] (f : α →+ Additive β) :
    ⇑(toMultiplicative'' f) = toMul ∘ f ∘ toAdd := rfl

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditive'' [AddZeroClass α] [MulOneClass β] (f : Multiplicative α →* β) :
    ⇑(toAdditive'' f) = ofMul ∘ f ∘ ofAdd := rfl

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →+ Additive β` from equality in `Multiplicative α →* β`. -/
@[ext]
lemma Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α →* β) (h : f.toAdditive'' = g.toAdditive'') : f = g :=
  MonoidHom.toAdditive''.injective h

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →* Multiplicative β` from equality in `Additive α →+ β`. -/
@[ext]
lemma Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α →+ β) (h : f.toMultiplicative' = g.toMultiplicative') : f = g :=
  AddMonoidHom.toMultiplicative'.injective h
