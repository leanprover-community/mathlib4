/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Homomorphisms of `R`-coalgebras

This file defines bundled homomorphisms of `R`-coalgebras. We simply mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `CoalgHom R A B`: the type of `R`-coalgebra morphisms from `A` to `B`.
* `Coalgebra.counitCoalgHom R A : A →ₗc[R] R`: the counit of a coalgebra as a coalgebra
homomorphism.

## Notations

* `A →ₗc[R] B` : `R`-algebra homomorphism from `A` to `B`.

-/

set_option autoImplicit true
open TensorProduct Coalgebra

universe u v w u₁ v₁

/-- Given `R`-modules `A, B` with comultiplcation maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-coalgebra homomorphism `A →ₗc[R] B` is an `R`-linear map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
structure CoalgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

@[inherit_doc CoalgHom]
infixr:25 " →ₗc " => CoalgHom _

@[inherit_doc]
notation:25 A " →ₗc[" R "] " B => CoalgHom R A B

/-- `CoalgHomClass F R A B` asserts `F` is a type of bundled coalgebra homomorphisms
from `A` to `B`.  -/
class CoalgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
    extends SemilinearMapClass F (RingHom.id R) A B : Prop where
  counit_comp : ∀ f : F, counit ∘ₗ LinearMapClass.linearMap f = counit
  map_comp_comul : ∀ f : F, TensorProduct.map (LinearMapClass.linearMap f)
    (LinearMapClass.linearMap f) ∘ₗ comul = comul ∘ₗ LinearMapClass.linearMap f

namespace CoalgHomClass

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]

/-- Turn an element of a type `F` satisfying `CoalgHomClass F R A B` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `A →ₗc[R] B`. -/
@[coe]
def toCoalgHom {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) : A →ₗc[R] B :=
  { LinearMapClass.linearMap f with
      toFun := f
      counit_comp := CoalgHomClass.counit_comp f
      map_comp_comul := CoalgHomClass.map_comp_comul f }

instance coeTC {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] : CoeTC F (A →ₗc[R] B) :=
  ⟨CoalgHomClass.toCoalgHom⟩

end CoalgHomClass

namespace CoalgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section AddCommMonoid

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]

variable [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]


instance funLike : FunLike (A →ₗc[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

instance coalgHomClass : CoalgHomClass (A →ₗc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/-
/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [AddCommMonoid α] [AddCommMonoid β]
    [Module R α] [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₗc[R] β) : α → β := f
    -/

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) :
    ⇑(f : A →ₗc[R] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →ₗc[R] B) : f.toFun = f :=
  rfl

attribute [coe] CoalgHom.toLinearMap

instance coeOutLinearMap : CoeOut (A →ₗc[R] B) (A →ₗ[R] B) :=
  ⟨CoalgHom.toLinearMap⟩

/-- The `AddMonoidHom` underlying a coalgebra homomorphism. -/
@[coe]
def toAddMonoidHom' (f : A →ₗc[R] B) : A →+ B := (f : A →ₗ[R] B)

instance coeOutAddMonoidHom : CoeOut (A →ₗc[R] B) (A →+ B) :=
  ⟨CoalgHom.toAddMonoidHom'⟩

@[simp]
theorem coe_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ ) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  rfl

@[norm_cast]
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A →ₗ[R] B) = f :=
  rfl

/-@[simp]
theorem toLinearMap_eq_coe (f : A →ₗc[R] B) : f.toLinearMap = f :=
  rfl-/

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →ₗc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₗc[R] B) : ⇑(f : A →+ B) = f :=
  rfl

variable (φ : A →ₗc[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₗc[R] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₗc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_linearMap_injective : Function.Injective ((↑) : (A →ₗc[R] B) → A →ₗ[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₗ[R] B) : A → B) = ((φ₂ : A →ₗ[R] B) : A → B) from congr_arg _ H

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₗc[R] B) → A →+ B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₗc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : A →ₗc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →ₗc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →ₗc[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff

@[ext high]
theorem ext_of_ring {f g : R →ₗc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
theorem mk_coe {f : A →ₗc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  ext fun _ => rfl

@[simp]
theorem counit_comp_apply (x : A) : counit (φ x) = counit (R := R) x :=
  LinearMap.congr_fun φ.counit_comp _

@[simp]
theorem map_comp_comul_apply (x : A) :
    TensorProduct.map φ φ (comul x) = comul (R := R) (φ x) :=
  LinearMap.congr_fun φ.map_comp_comul _

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _

protected theorem map_zero : φ 0 = 0 :=
  map_zero _

protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _

section

variable (R A)

/-- Identity map as a `CoalgHom`. -/
@[simps! toLinearMap] protected def id : A →ₗc[R] A :=
{ LinearMap.id with
  counit_comp := by ext; rfl
  map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

@[simp]
theorem coe_id : ⇑(CoalgHom.id R A) = id :=
  rfl

end

theorem id_apply (p : A) : CoalgHom.id R A p = p :=
  rfl

/-- Composition of coalgebra homomorphisms. -/
@[simps! toLinearMap] def comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : A →ₗc[R] C :=
  { φ₁.toLinearMap ∘ₗ φ₂ with
    counit_comp := by ext; simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply,
      counit_comp_apply]
    map_comp_comul := by ext; simp only [map_comp, LinearMap.coe_comp, Function.comp_apply,
      map_comp_comul_apply, coe_toLinearMap] }

@[simp]
theorem coe_comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

@[simp]
theorem comp_id : φ.comp (CoalgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (CoalgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : C →ₗc[R] D) (φ₂ : B →ₗc[R] C) (φ₃ : A →ₗc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

/-theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (CoalgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl-/

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₗc[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := CoalgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl

@[simp]
theorem one_apply (x : A) : (1 : A →ₗc[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end AddCommMonoid

section AddCommGroup

variable [CommSemiring R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

variable [CoalgebraStruct R A] [CoalgebraStruct R B] (φ : A →ₗc[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

end AddCommGroup

end CoalgHom

namespace Coalgebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- The counit of a coalgebra as a `CoalgHom`. -/
@[simps! toLinearMap] def counitCoalgHom : A →ₗc[R] R :=
  { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.coe_comp, Function.comp_apply,
        rTensor_counit_comul, LinearMap.lTensor_tmul] }

variable {R}

instance subsingleton_to_ring : Subsingleton (A →ₗc[R] R) :=
  ⟨fun f g => CoalgHom.ext fun x => by
    have hf := LinearMap.ext_iff.1 f.counit_comp x
    have hg := LinearMap.ext_iff.1 g.counit_comp x
    simp_all only [LinearMap.coe_comp, CoalgHom.coe_toLinearMap, Function.comp_apply,
      CommSemiring.counit_apply, hf, hg]⟩

@[ext high]
theorem ext_to_ring (f g : A →ₗc[R] R) : f = g := Subsingleton.elim _ _

end Coalgebra
