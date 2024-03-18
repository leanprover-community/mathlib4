/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth, Amelia Livingston
-/
import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Isomorphisms of `R`-coalgebras

This file defines bundled isomorphisms of `R`-coalgebras. We simply mimic the early parts of
`Mathlib/Algebra/Module/Equiv.lean`.

## Main definitions

* `CoalgEquiv R A B`: the type of `R`-coalgebra isomorphisms between `A` and `B`.

## Notations

* `A ≃ₗc[R] B` : `R`-coalgebra equivalence from `A` to `B`.
-/

set_option autoImplicit true

open BigOperators

universe u v w u₁ v₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

open Coalgebra

/-- An equivalence of coalgebras is an invertible coalgebra homomorphism. -/
structure CoalgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A ≃ₗ[R] B where

attribute [coe, nolint docBlame] CoalgEquiv.toCoalgHom
attribute [nolint docBlame] CoalgEquiv.toLinearEquiv

@[inherit_doc CoalgEquiv]
notation:50 A " ≃ₗc[" R "] " B => CoalgEquiv R A B

/-- `CoalgEquivClass F R A B` asserts `F` is a type of bundled coalgebra equivalences
from `A` to `B`.  -/
class CoalgEquivClass (F : Type*) (R A B : outParam (Type*)) [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B]
    extends CoalgHomClass F R A B, SemilinearEquivClass F (RingHom.id R) A B : Prop

namespace CoalgEquivClass

variable (F : Type*) [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [CoalgebraStruct R A] [CoalgebraStruct R B]

/- not sure if I need this, or additional instances -/
instance (priority := 100) [EquivLike F A B] [s : CoalgEquivClass F R A B] :
    LinearEquivClass F R A B :=
  { s with }

end CoalgEquivClass

namespace CoalgEquiv

section AddCommMonoid

variable [CommSemiring R]

section

variable [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

instance : Coe (A ≃ₗc[R] B) (A →ₗc[R] B) :=
  ⟨toCoalgHom⟩

/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (A ≃ₗc[R] B) → A ≃ B := fun f => f.toLinearEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₗc[R] B) → A ≃ B) :=
  fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (CoalgEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨CoalgHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
theorem toEquiv_inj {e₁ e₂ : A ≃ₗc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toCoalgHom_injective : Function.Injective (toCoalgHom : (A ≃ₗc[R] B) → A →ₗc[R] B) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| CoalgHom.congr_fun H

@[simp, norm_cast]
theorem toCoalgHom_inj {e₁ e₂ : A ≃ₗc[R] B} : (↑e₁ : A →ₗc[R] B) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

instance : EquivLike (A ≃ₗc[R] B) A B where
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

instance : FunLike (A ≃ₗc[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

instance : CoalgEquivClass (A ≃ₗc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)

@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul ugh ugh2 left_inv right_inv} :
    (⟨⟨⟨⟨to_fun, map_add⟩, map_smul⟩, ugh, ugh2⟩, inv_fun, left_inv, right_inv⟩ : A ≃ₗc[R] B)
      = to_fun := rfl

theorem coe_injective : @Function.Injective (A ≃ₗc[R] B) (A → B) CoeFun.coe :=
  DFunLike.coe_injective

end

section

variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [Module R A] [Module R B]
  [Module R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₗc[R] B)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : A →ₗc[R] B) = e :=
  rfl

@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
theorem coe_toCoalgHom : ⇑e.toCoalgHom = e :=
  rfl

theorem toFun_eq_coe : e.toFun = e := rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  DFunLike.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (A R)

/-- The identity map is a coalgebra equivalence. -/
@[refl, simps! toCoalgHom]
def refl : A ≃ₗc[R] A :=
  { CoalgHom.id R A, LinearEquiv.refl R A with }

end

@[simp]
theorem refl_toLinearEquiv : (refl R A).toLinearEquiv = LinearEquiv.refl R A := rfl

@[simp]
theorem refl_apply (x : A) : refl R A x = x :=
  rfl

/-- Coalgebra equivalences are symmetric. -/
@[symm, simps! toCoalgHom]
def symm (e : A ≃ₗc[R] B) : B ≃ₗc[R] A :=
  { e.toLinearEquiv.symm with
    counit_comp := (LinearEquiv.comp_toLinearMap_symm_eq _ _).2 e.counit_comp.symm
    map_comp_comul := by
      show (TensorProduct.congr e.toLinearEquiv e.toLinearEquiv).symm.toLinearMap ∘ₗ comul
        = comul ∘ₗ e.toLinearEquiv.symm
      rw [LinearEquiv.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc,
        LinearEquiv.eq_comp_toLinearMap_symm, ← e.map_comp_comul]
      rfl }

@[simp]
theorem symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm := rfl

/-def Simps.apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₗc[R] B) : A → B :=
  e

def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₗc[R] B) : B → A :=
  e.symm

-- can't get it to work idk why
--initialize_simps_projections CoalgEquiv (toFun → apply, invFun → symm_apply)
-/

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₗc[R] B} {e₂₃ : B ≃ₗc[R] C}

/-- Coalgebra equivalences are transitive. -/
@[trans, simps! toCoalgHom]
def trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C :=
  { e₂₃.toCoalgHom.comp e₁₂.toCoalgHom, e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv with }

@[simp]
theorem trans_toLinearEquiv :
  (e₁₂.trans e₂₃).toLinearEquiv = e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv := rfl

@[simp]
theorem coe_toEquiv_trans : e₁₂.toEquiv.trans e₂₃ = (e₁₂.trans e₂₃).toEquiv :=
  rfl

end
end AddCommMonoid
end CoalgEquiv
