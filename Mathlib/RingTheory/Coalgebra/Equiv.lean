/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
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

open BigOperators

universe u v w

variable {R A B C : Type*}

open Coalgebra

/-- An equivalence of coalgebras is an invertible coalgebra homomorphism. -/
structure CoalgEquiv (R : Type*) [CommSemiring R] (A B : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A ≃ₗ[R] B where

attribute [nolint docBlame] CoalgEquiv.toCoalgHom
attribute [nolint docBlame] CoalgEquiv.toLinearEquiv

@[inherit_doc CoalgEquiv]
notation:50 A " ≃ₗc[" R "] " B => CoalgEquiv R A B

/-- `CoalgEquivClass F R A B` asserts `F` is a type of bundled coalgebra equivalences
from `A` to `B`.  -/
class CoalgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B]
    extends CoalgHomClass F R A B, SemilinearEquivClass F (RingHom.id R) A B : Prop

namespace CoalgEquivClass

variable {F R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- Reinterpret an element of a type of coalgebra equivalences as a coalgebra equivalence. -/
@[coe]
def toCoalgEquiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) : A ≃ₗc[R] B :=
  { (f : A →ₗc[R] B), (f : A ≃ₗ[R] B) with }

/-- Reinterpret an element of a type of coalgebra equivalences as a coalgebra equivalence. -/
instance instCoeToCoalgEquiv
    [EquivLike F A B] [CoalgEquivClass F R A B] : CoeHead F (A ≃ₗc[R] B) where
  coe f := toCoalgEquiv f

end CoalgEquivClass

namespace CoalgEquiv

variable [CommSemiring R]

section

variable [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- The equivalence of types underlying a coalgebra equivalence. -/
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

@[simp, norm_cast]
theorem toCoalgHom_inj {e₁ e₂ : A ≃ₗc[R] B} : (↑e₁ : A →ₗc[R] B) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

@[simp]
theorem coe_mk {f h h₀ h₁ h₂ h₃ h₄ h₅} :
    (⟨⟨⟨⟨f, h⟩, h₀⟩, h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₗc[R] B) = f := rfl

end

section

variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [Module R A] [Module R B]
  [Module R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₗc[R] B)

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type*} [CommSemiring R] {α β : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Module R α]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₗc[R] β) : α → β := f

initialize_simps_projections CoalgEquiv (toFun → apply)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : A →ₗc[R] B) = e :=
  rfl

@[simp]
theorem toLinearEquiv_eq_coe (f : A ≃ₗc[R] B) : f.toLinearEquiv = f :=
  rfl

@[simp]
theorem toCoalgHom_eq_coe (f : A ≃ₗc[R] B) : f.toCoalgHom = f :=
  rfl

@[simp]
theorem coe_toLinearEquiv : ⇑(e : A ≃ₗ[R] B) = e :=
  rfl

@[simp]
theorem coe_toCoalgHom : ⇑(e : A →ₗc[R] B) = e :=
  rfl

theorem toLinearEquiv_toLinearMap : ((e : A ≃ₗ[R] B) : A →ₗ[R] B) = (e : A →ₗc[R] B) :=
  rfl

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
@[refl, simps!]
def refl : A ≃ₗc[R] A :=
  { CoalgHom.id R A, LinearEquiv.refl R A with }

end

@[simp]
theorem refl_toLinearEquiv : refl R A = LinearEquiv.refl R A := rfl

@[simp]
theorem refl_toCoalgHom : refl R A = CoalgHom.id R A :=
  rfl

/-- Coalgebra equivalences are symmetric. -/
@[symm]
def symm (e : A ≃ₗc[R] B) : B ≃ₗc[R] A :=
  { (e : A ≃ₗ[R] B).symm with
    counit_comp := (LinearEquiv.comp_toLinearMap_symm_eq _ _).2 e.counit_comp.symm
    map_comp_comul := by
      show (TensorProduct.congr (e : A ≃ₗ[R] B) (e : A ≃ₗ[R] B)).symm.toLinearMap ∘ₗ comul
        = comul ∘ₗ (e : A ≃ₗ[R] B).symm
      rw [LinearEquiv.toLinearMap_symm_comp_eq]
      simp only [TensorProduct.congr, toLinearEquiv_toLinearMap,
        LinearEquiv.ofLinear_toLinearMap, ← LinearMap.comp_assoc, CoalgHomClass.map_comp_comul,
        LinearEquiv.eq_comp_toLinearMap_symm] }

@[simp]
theorem symm_toLinearEquiv (e : A ≃ₗc[R] B) :
    e.symm = (e : A ≃ₗ[R] B).symm := rfl

@[simp]
theorem symm_toCoalgHom (e : A ≃ₗc[R] B) :
    ((e.symm : B →ₗc[R] A) : B →ₗ[R] A) = (e : A ≃ₗ[R] B).symm := rfl

/-- See Note [custom simps projection] -/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₗc[R] B) : B → A :=
  e.symm

initialize_simps_projections CoalgEquiv (invFun → symm_apply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₗc[R] B} {e₂₃ : B ≃ₗc[R] C}

/-- Coalgebra equivalences are transitive. -/
@[trans, simps!]
def trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C :=
  { (e₂₃ : B →ₗc[R] C).comp (e₁₂ : A →ₗc[R] B), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }

theorem trans_toLinearEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗ[R] C) = (e₁₂ : A ≃ₗ[R] B) ≪≫ₗ e₂₃ := rfl

@[simp]
theorem trans_toCoalgHom :
    (e₁₂.trans e₂₃ : A →ₗc[R] C) = e₂₃.comp e₁₂ := rfl

@[simp]
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

end
end CoalgEquiv
