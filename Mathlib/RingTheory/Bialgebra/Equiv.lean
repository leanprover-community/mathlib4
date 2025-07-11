/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Isomorphisms of `R`-bialgebras

This file defines bundled isomorphisms of `R`-bialgebras. We simply mimic the early parts of
`Mathlib/Algebra/Algebra/Equiv.lean`.

## Main definitions

* `BialgEquiv R A B`: the type of `R`-bialgebra isomorphisms between `A` and `B`.

## Notations

* `A ≃ₐc[R] B` : `R`-bialgebra equivalence from `A` to `B`.
-/

universe u v w u₁ v₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

open Bialgebra

/-- An equivalence of bialgebras is an invertible bialgebra homomorphism. -/
structure BialgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ≃ₗc[R] B, A ≃* B where

attribute [nolint docBlame] BialgEquiv.toMulEquiv
attribute [nolint docBlame] BialgEquiv.toCoalgEquiv

@[inherit_doc BialgEquiv]
notation:50 A " ≃ₐc[" R "] " B => BialgEquiv R A B

/-- `BialgEquivClass F R A B` asserts `F` is a type of bundled bialgebra equivalences
from `A` to `B`. -/
class BialgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [EquivLike F A B] : Prop
    extends CoalgEquivClass F R A B, MulEquivClass F A B

namespace BialgEquivClass

variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
  [EquivLike F A B] [BialgEquivClass F R A B]

instance (priority := 100) toBialgHomClass : BialgHomClass F R A B where
  map_add := map_add
  map_smulₛₗ := map_smul
  counit_comp := CoalgHomClass.counit_comp
  map_comp_comul := CoalgHomClass.map_comp_comul
  map_mul := map_mul
  map_one := map_one

/-- Reinterpret an element of a type of bialgebra equivalences as a bialgebra equivalence. -/
@[coe]
def toBialgEquiv (f : F) : A ≃ₐc[R] B :=
  { (f : A ≃ₗc[R] B), (f : A →ₐc[R] B) with }

/-- Reinterpret an element of a type of bialgebra equivalences as a bialgebra equivalence. -/
instance instCoeToBialgEquiv : CoeHead F (A ≃ₐc[R] B) where
  coe f := toBialgEquiv f

instance (priority := 100) toAlgEquivClass : AlgEquivClass F R A B where
  map_mul := map_mul
  map_add := map_add
  commutes := AlgHomClass.commutes

end BialgEquivClass

namespace BialgEquiv

variable [CommSemiring R]

section

variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- The bialgebra morphism underlying a bialgebra equivalence. -/
def toBialgHom (f : A ≃ₐc[R] B) : A →ₐc[R] B :=
  { f.toCoalgEquiv with
    map_one' := map_one f.toMulEquiv
    map_mul' := map_mul f.toMulEquiv }

/-- The algebra equivalence underlying a bialgebra equivalence. -/
def toAlgEquiv (f : A ≃ₐc[R] B) : A ≃ₐ[R] B :=
  { f.toCoalgEquiv with
    map_mul' := map_mul f.toMulEquiv
    map_add' := map_add f.toCoalgEquiv
    commutes' := AlgHomClass.commutes f.toBialgHom }

/-- The equivalence of types underlying a bialgebra equivalence. -/
def toEquiv : (A ≃ₐc[R] B) → A ≃ B := fun f => f.toCoalgEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₐc[R] B) → A ≃ B) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h =>
    (BialgEquiv.mk.injEq _ _ _ _).mpr (CoalgEquiv.toEquiv_injective h)

@[simp]
theorem toEquiv_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toBialgHom_injective : Function.Injective (toBialgHom : (A ≃ₐc[R] B) → A →ₐc[R] B) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| BialgHom.congr_fun H

instance : EquivLike (A ≃ₐc[R] B) A B where
  coe f := f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

instance : FunLike (A ≃ₐc[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

instance : BialgEquivClass (A ≃ₐc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')

@[simp, norm_cast]
theorem toBialgHom_inj {e₁ e₂ : A ≃ₐc[R] B} : (↑e₁ : A →ₐc[R] B) = e₂ ↔ e₁ = e₂ :=
  toBialgHom_injective.eq_iff

@[simp]
theorem coe_mk {f h h₀ h₁ h₂ h₃ h₄ h₅ h₆} :
    (⟨⟨⟨⟨⟨f, h⟩, h₀⟩, h₁, h₂⟩, h₃, h₄, h₅⟩, h₆⟩ : A ≃ₐc[R] B) = f := rfl

end

section

variable [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B]
  [Algebra R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₐc[R] B)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : A →ₐc[R] B) = e :=
  rfl

@[simp]
theorem toCoalgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toCoalgEquiv = f :=
  rfl

@[simp]
theorem toBialgHom_eq_coe (f : A ≃ₐc[R] B) : f.toBialgHom = f :=
  rfl

@[simp]
theorem toAlgEquiv_eq_coe (f : A ≃ₐc[R] B) : f.toAlgEquiv = f :=
  rfl

@[simp]
theorem coe_toCoalgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

@[simp]
theorem coe_toBialgHom : ⇑(e : A →ₐc[R] B) = e :=
  rfl

@[simp]
theorem coe_toAlgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

theorem toCoalgEquiv_toCoalgHom : ((e : A ≃ₐc[R] B) : A →ₗc[R] B) = (e : A →ₐc[R] B) :=
  rfl

theorem toBialgHom_toAlgHom : ((e : A →ₐc[R] B) : A →ₐ[R] B) = e := rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  DFunLike.congr_fun h x

end

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} [CommSemiring R] {α : Type v} {β : Type w}
    [Semiring α] [Semiring β] [Algebra R α]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ≃ₐc[R] β) : α → β := f

/-- See Note [custom simps projection] -/
def Simps.symm_apply {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₐc[R] B) : B → A :=
  e.symm

initialize_simps_projections BialgEquiv (toFun → apply, invFun → symm_apply)

variable (A R) in
/-- The identity map is a bialgebra equivalence. -/
@[refl, simps!]
def refl : A ≃ₐc[R] A :=
  { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]
theorem refl_toCoalgEquiv : refl R A = CoalgEquiv.refl R A := rfl

@[simp]
theorem refl_toBialgHom : refl R A = BialgHom.id R A :=
  rfl

/-- Bialgebra equivalences are symmetric. -/
@[symm]
def symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A :=
  { (e : A ≃ₗc[R] B).symm, (e : A ≃* B).symm with }

@[simp]
theorem symm_toCoalgEquiv (e : A ≃ₐc[R] B) :
    e.symm = (e : A ≃ₗc[R] B).symm := rfl

theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
theorem coe_toEquiv : ⇑e.toEquiv = e :=
  rfl

@[simp]
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : A ≃ₐc[R] B} {e₂₃ : B ≃ₐc[R] C}

/-- Bialgebra equivalences are transitive. -/
@[trans, simps!]
def trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C :=
  { (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C), (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]
theorem trans_toCoalgEquiv :
    (e₁₂.trans e₂₃ : A ≃ₗc[R] C) = (e₁₂ : A ≃ₗc[R] B).trans (e₂₃ : B ≃ₗc[R] C) := rfl

@[simp]
theorem trans_toBialgHom :
    (e₁₂.trans e₂₃ : A →ₐc[R] C) = (e₂₃ : B →ₐc[R] C).comp e₁₂ := rfl

@[simp]
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

/-- If an coalgebra morphism has an inverse, it is an coalgebra isomorphism. -/
def ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ : f.comp g = BialgHom.id R B)
    (h₂ : g.comp f = BialgHom.id R A) : A ≃ₐc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]
theorem coe_ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    ofBialgHom f g h₁ h₂ = f :=
  rfl

theorem ofBialgHom_symm (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    (ofBialgHom f g h₁ h₂).symm = ofBialgHom g f h₂ h₁ :=
  rfl

variable {f : A →ₐc[R] B} (hf : Function.Bijective f)

/-- Promotes a bijective coalgebra homomorphism to a coalgebra equivalence. -/
@[simps apply]
noncomputable def ofBijective : A ≃ₐc[R] B where
  toFun := f
  __ := f
  __ := AlgEquiv.ofBijective (f : A →ₐ[R] B) hf

@[simp]
theorem coe_ofBijective : (BialgEquiv.ofBijective hf : A → B) = f :=
  rfl

end
end BialgEquiv
