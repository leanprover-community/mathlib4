/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
Ported by: Frédéric Dupuis

! This file was ported from Lean 3 source module algebra.hom.equiv.type_tags
! leanprover-community/mathlib commit 3342d1b2178381196f818146ff79bc0e7ccd9e2d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/


variable {G H : Type _}

/-- Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
    { AddMonoidHom.toMultiplicative f.toAddMonoidHom with
      invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
      left_inv := fun _ ↦ toAdd_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ toAdd_injective <| f.apply_symm_apply _ }
  invFun f :=
    { AddMonoidHom.toMultiplicative.symm f.toMonoidHom with
      invFun := AddMonoidHom.toMultiplicative.symm f.symm.toMonoidHom,
      left_inv := fun _ ↦ ofAdd_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ ofAdd_injective <| f.apply_symm_apply _ }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_equiv.to_multiplicative AddEquiv.toMultiplicative

/-- Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f :=
    { MonoidHom.toAdditive f.toMonoidHom with
      invFun := MonoidHom.toAdditive f.symm.toMonoidHom
      left_inv := fun _ ↦ toMul_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ toMul_injective <| f.apply_symm_apply _ }
  invFun f :=
    { MonoidHom.toAdditive.symm f.toAddMonoidHom with
      invFun := MonoidHom.toAdditive.symm f.symm.toAddMonoidHom
      left_inv := fun _ ↦ ofMul_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ ofMul_injective <| f.apply_symm_apply _ }
  left_inv _ := rfl
  right_inv _ := rfl
#align mul_equiv.to_additive MulEquiv.toAdditive

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
    { AddMonoidHom.toMultiplicative' f.toAddMonoidHom with
      invFun := AddMonoidHom.toMultiplicative'' f.symm.toAddMonoidHom
      left_inv := fun _ ↦ ofMul_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ toAdd_injective <| f.apply_symm_apply _ }
  invFun f :=
    { MonoidHom.toAdditive' f.toMonoidHom with
      invFun := MonoidHom.toAdditive'' f.symm.toMonoidHom
      left_inv := fun _ ↦ toMul_injective <| f.symm_apply_apply _
      right_inv := fun _ ↦ ofAdd_injective <| f.apply_symm_apply _ }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_equiv.to_multiplicative' AddEquiv.toMultiplicative'

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm
#align mul_equiv.to_additive' MulEquiv.toAdditive'

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
    { AddMonoidHom.toMultiplicative'' f.toAddMonoidHom with
      invFun := AddMonoidHom.toMultiplicative' f.symm.toAddMonoidHom
      left_inv := fun x ↦ toAdd_injective <| f.symm_apply_apply _
      right_inv := fun x ↦ ofMul_injective <| f.apply_symm_apply _ }
  invFun f :=
    { MonoidHom.toAdditive'' f.toMonoidHom with
      invFun := MonoidHom.toAdditive' f.symm.toMonoidHom
      left_inv := fun x ↦ ofAdd_injective <| f.symm_apply_apply _
      right_inv := fun x ↦ toMul_injective <| f.apply_symm_apply _ }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
#align add_equiv.to_multiplicative'' AddEquiv.toMultiplicative''

/-- Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm
#align mul_equiv.to_additive'' MulEquiv.toAdditive''

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive' (MulEquiv.refl (Multiplicative G))
#align add_equiv.additive_multiplicative AddEquiv.additiveMultiplicative

/-- `Multiplicative (Additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))
#align mul_equiv.multiplicative_additive MulEquiv.multiplicativeAdditive

end
