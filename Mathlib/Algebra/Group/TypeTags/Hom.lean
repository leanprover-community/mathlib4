/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Transport algebra morphisms between additive and multiplicative types.
-/

@[expose] public section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

variable {M N α β : Type*}

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

@[simp]
lemma AddMonoidHom.toMultiplicative_id [AddZeroClass α] : (id α).toMultiplicative = .id _ := rfl

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
lemma MonoidHom.coe_toAdditive [MulOneClass α] [MulOneClass β] (f : α →* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl

@[deprecated (since := "2025-11-07")]
alias MonoidHom.coe_toMultiplicative := MonoidHom.coe_toAdditive

@[simp] lemma MonoidHom.toAdditive_id [MulOneClass α] : (id α).toAdditive = .id _ := rfl

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicativeRight [MulOneClass α] [AddZeroClass β] :
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

@[deprecated (since := "2025-09-19")]
alias AddMonoidHom.toMultiplicative' := AddMonoidHom.toMultiplicativeRight

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicativeRight [MulOneClass α] [AddZeroClass β]
    (f : Additive α →+ β) : ⇑(toMultiplicativeRight f) = ofAdd ∘ f ∘ ofMul := rfl

@[deprecated (since := "2025-09-19")]
alias AddMonoidHom.coe_toMultiplicative' := AddMonoidHom.coe_toMultiplicativeRight

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
def MonoidHom.toAdditiveLeft [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicativeRight.symm

@[deprecated (since := "2025-09-19")] alias MonoidHom.toAdditive' := MonoidHom.toAdditiveLeft

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditiveLeft [MulOneClass α] [AddZeroClass β] (f : α →* Multiplicative β) :
    ⇑(toAdditiveLeft f) = toAdd ∘ f ∘ toMul := rfl

@[deprecated (since := "2025-09-19")]
alias MonoidHom.coe_toAdditive' := MonoidHom.coe_toAdditiveLeft

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] :
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

@[deprecated (since := "2025-09-19")]
alias AddMonoidHom.toMultiplicative'' := AddMonoidHom.toMultiplicativeLeft

@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] (f : α →+ Additive β) :
    ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd := rfl

@[deprecated (since := "2025-09-19")]
alias AddMonoidHom.coe_toMultiplicative'' := AddMonoidHom.coe_toMultiplicativeLeft

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
def MonoidHom.toAdditiveRight [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicativeLeft.symm

@[deprecated (since := "2025-09-19")] alias MonoidHom.toAdditive'' := MonoidHom.toAdditiveRight

@[simp, norm_cast]
lemma MonoidHom.coe_toAdditiveRight [AddZeroClass α] [MulOneClass β] (f : Multiplicative α →* β) :
    ⇑(toAdditiveRight f) = ofMul ∘ f ∘ ofAdd := rfl

@[deprecated (since := "2025-09-19")]
alias MonoidHom.coe_toAdditive'' := MonoidHom.coe_toAdditiveRight

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →+ Additive β` from equality in `Multiplicative α →* β`. -/
@[ext]
lemma Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α →* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g :=
  MonoidHom.toAdditiveRight.injective h

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →* Multiplicative β` from equality in `Additive α →+ β`. -/
@[ext]
lemma Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α →+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g :=
  AddMonoidHom.toMultiplicativeRight.injective h

section AddCommMonoid
variable [AddMonoid M] [AddCommMonoid N]

@[simp]
lemma AddMonoidHom.toMultiplicative_add (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl

end AddCommMonoid

/-- `AddMonoidHom.toMultiplicativeLeft` as an `AddEquiv`. -/
def AddMonoidHom.toMultiplicativeLeftAddEquiv [AddMonoid M] [CommMonoid N] :
    (M →+ Additive N) ≃+ Additive (Multiplicative M →* N) where
  toEquiv := AddMonoidHom.toMultiplicativeLeft.trans Additive.ofMul
  map_add' _ _ := rfl

/-- `AddMonoidHom.toMultiplicativeRight` as an `AddEquiv`. -/
def AddMonoidHom.toMultiplicativeRightAddEquiv [Monoid M] [AddCommMonoid N] :
    (Additive M →+ N) ≃+ Additive (M →* Multiplicative N) where
  toEquiv := AddMonoidHom.toMultiplicativeRight.trans Additive.ofMul
  map_add' _ _ := rfl

/-- `MonoidHom.toAdditiveLeft` as a `MulEquiv`. -/
def MonoidHom.toAdditiveLeftMulEquiv [Monoid M] [AddCommMonoid N] :
    (M →* Multiplicative N) ≃* Multiplicative (Additive M →+ N) where
  toEquiv := MonoidHom.toAdditiveLeft.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

/-- `MonoidHom.toAdditiveRight` as a `MulEquiv`. -/
def MonoidHom.toAdditiveRightMulEquiv [AddMonoid M] [CommMonoid N] :
    (Multiplicative M →* N) ≃* Multiplicative (M →+ Additive N) where
  toEquiv := MonoidHom.toAdditiveRight.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl
