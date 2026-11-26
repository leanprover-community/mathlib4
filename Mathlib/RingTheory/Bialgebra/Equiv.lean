/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Isomorphisms of `R`-bialgebras

This file defines bundled isomorphisms of `R`-bialgebras. We simply mimic the early parts of
`Mathlib/Algebra/Algebra/Equiv.lean`.

## Main definitions

* `BialgEquiv R A B`: the type of `R`-bialgebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐc[R] B` : `R`-bialgebra equivalence from `A` to `B`.
-/

@[expose] public section

universe u v w u₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

open TensorProduct Coalgebra Bialgebra Function

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
def _root_.BialgEquiv.ofClass (f : F) : A ≃ₐc[R] B :=
  { CoalgEquiv.ofClass f, BialgHom.ofClass f with }

@[deprecated (since := "2026-11-22")] alias toBialgEquiv := BialgEquiv.ofClass

instance (priority := 100) toAlgEquivClass : AlgEquivClass F R A B where
  map_mul := map_mul
  map_add := map_add
  map_smulₛₗ := map_smul

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
    map_smul' := map_smul f.toBialgHom }

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

@[macro_inline]
instance : EquivLike (A ≃ₐc[R] B) A B where
  coe f := f.toFun
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

@[macro_inline]
instance : FunLike (A ≃ₐc[R] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective

instance : BialgEquivClass (A ≃ₐc[R] B) R A B where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  counit_comp := (·.counit_comp)
  map_comp_comul := (·.map_comp_comul)
  map_mul := (·.map_mul')

instance : CoeOut (A ≃ₐc[R] B) (A ≃ₐ[R] B) where coe := toAlgEquiv

@[simp]
theorem toBialgHom_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toBialgHom = e₂.toBialgHom ↔ e₁ = e₂ :=
  toBialgHom_injective.eq_iff

@[simp] lemma toCoalgEquiv_mk (e : A ≃ₗc[R] B) (h) : (mk e h).toCoalgEquiv = e := rfl

@[deprecated (since := "2026-11-22")] alias coe_mk := toCoalgEquiv_mk

@[simp]
protected lemma coe_ofClass {F : Type*} [EquivLike F A B] [BialgEquivClass F R A B] (f : F) :
    ⇑(ofClass f) = f := rfl

end

section

variable [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B]
  [Algebra R C] [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (e e' : A ≃ₐc[R] B)

@[deprecated BialgHom.coe_ofClass +typeChanged (since := "2026-11-22")]
theorem coe_coe : ⇑(.ofClass e : A →ₐc[R] B) = e :=
  rfl

theorem toCoalgEquiv_eq_ofClass (f : A ≃ₐc[R] B) : f.toCoalgEquiv = .ofClass f :=
  rfl

@[deprecated (since := "2026-11-22")] alias toCoalgEquiv_eq_coe := toCoalgEquiv_eq_ofClass

theorem toBialgHom_eq_ofClass (f : A ≃ₐc[R] B) : f.toBialgHom = .ofClass f :=
  rfl

@[deprecated (since := "2026-11-22")] alias toBialgHom_eq_coe := toBialgHom_eq_ofClass

@[simp]
theorem coe_toCoalgEquiv : ⇑e.toCoalgEquiv = e :=
  rfl

@[simp]
theorem coe_toBialgHom : ⇑e.toBialgHom = e :=
  rfl

@[simp]
theorem coe_toAlgEquiv : ⇑(e : A ≃ₐ[R] B) = e :=
  rfl

theorem toCoalgEquiv_toCoalgHom : e.toCoalgEquiv.toCoalgHom = e.toBialgHom.toCoalgHom := rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : A) : e x = e' x :=
  congr($h x)

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
@[refl, simps! apply]
def refl : A ≃ₐc[R] A :=
  { CoalgEquiv.refl R A, BialgHom.id R A with }

@[simp]
theorem refl_toCoalgEquiv : (refl R A).toCoalgEquiv = CoalgEquiv.refl R A := rfl

@[simp]
theorem refl_toBialgHom : (refl R A).toBialgHom = BialgHom.id R A :=
  rfl

/-- Bialgebra equivalences are symmetric. -/
@[symm]
def symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A :=
  { e.toCoalgEquiv.symm, (e : A ≃* B).symm with }

@[simp]
theorem symm_toCoalgEquiv (e : A ≃ₐc[R] B) :
    e.symm.toCoalgEquiv = e.toCoalgEquiv.symm := rfl

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
@[trans, simps! apply]
def trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C :=
  { e₁₂.toCoalgEquiv.trans e₂₃.toCoalgEquiv, (e₁₂ : A ≃* B).trans (e₂₃ : B ≃* C) with }

@[simp]
theorem trans_toCoalgEquiv :
    (e₁₂.trans e₂₃).toCoalgEquiv = e₁₂.toCoalgEquiv.trans e₂₃.toCoalgEquiv := rfl

@[simp]
theorem trans_toBialgHom :
    (e₁₂.trans e₂₃).toBialgHom = e₂₃.toBialgHom.comp e₁₂.toBialgHom := rfl

@[simp]
theorem coe_toEquiv_trans : (e₁₂ : A ≃ B).trans e₂₃ = (e₁₂.trans e₂₃ : A ≃ C) :=
  rfl

@[simp]
lemma apply_symm_apply (e : A ≃ₐc[R] B) : ∀ x, e (e.symm x) = x := e.toEquiv.apply_symm_apply

@[simp]
lemma symm_apply_apply (e : A ≃ₐc[R] B) : ∀ x, e.symm (e x) = x := e.toEquiv.symm_apply_apply

@[simp] lemma comp_symm (e : A ≃ₐc[R] B) : e.toBialgHom.comp e.symm.toBialgHom = .id R B :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.comp_symm

@[simp] lemma symm_comp (e : A ≃ₐc[R] B) : e.symm.toBialgHom.comp e.toBialgHom = .id R A :=
  BialgHom.coe_toAlgHom_injective e.toAlgEquiv.symm_comp

lemma toRingEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃+* B) : A →+* B) = e := rfl
@[simp] lemma toAlgEquiv_toRingHom (e : A ≃ₐc[R] B) : ((e : A ≃ₐ[R] B) : A →+* B) = e := rfl

/-- If a bialgebra morphism has an inverse, it is a bialgebra isomorphism. -/
def ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ : f.comp g = BialgHom.id R B)
    (h₂ : g.comp f = BialgHom.id R A) : A ≃ₐc[R] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := BialgHom.ext_iff.1 h₂
  right_inv := BialgHom.ext_iff.1 h₁

@[simp]
theorem coe_ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    ⇑(ofBialgHom f g h₁ h₂) = f := rfl

@[simp]
theorem toBialgHom_ofBialgHom (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    (ofBialgHom f g h₁ h₂).toBialgHom = f :=
  rfl

theorem ofBialgHom_symm (f : A →ₐc[R] B) (g : B →ₐc[R] A) (h₁ h₂) :
    (ofBialgHom f g h₁ h₂).symm = ofBialgHom g f h₂ h₁ :=
  rfl

end

variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra equiv from an algebra equiv respecting counit and comultiplication. -/
@[simps apply] def ofAlgEquiv (f : A ≃ₐ[R] B)
    (counit_comp : (Bialgebra.counitAlgHom R B).comp f = Bialgebra.counitAlgHom R A)
    (map_comp_comul : (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R B).comp f) : A ≃ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := congr($(counit_comp).toLinearMap)
  map_comp_comul := congr($(map_comp_comul).toLinearMap)

@[simp]
lemma toLinearMap_ofAlgEquiv (f : A ≃ₐ[R] B) (counit_comp map_comp_comul) :
    (ofAlgEquiv f counit_comp map_comp_comul : A →ₗ[R] B) = f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Promotes a bijective bialgebra homomorphism to a bialgebra equivalence. -/
@[simps! apply]
noncomputable def ofBijective (f : A →ₐc[R] B) (hf : Bijective f) : A ≃ₐc[R] B :=
  .ofAlgEquiv (.ofBijective (f : A →ₐ[R] B) hf) (by ext; simp) (by ext; simp)

@[simp]
lemma coe_ofBijective (f : A →ₐc[R] B) (hf : Bijective f) : (ofBijective f hf : A → B) = f := rfl

@[simp]
lemma toEquiv_ofBijective (f : A →ₐc[R] B) (hf) : (ofBijective f hf).toEquiv = .ofBijective f hf :=
  rfl

end BialgEquiv
