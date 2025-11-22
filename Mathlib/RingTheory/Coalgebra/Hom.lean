/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Homomorphisms of `R`-coalgebras

This file defines bundled homomorphisms of `R`-coalgebras. We largely mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `CoalgHom R A B`: the type of `R`-coalgebra morphisms from `A` to `B`.
* `Coalgebra.counitCoalgHom R A : A →ₗc[R] R`: the counit of a coalgebra as a coalgebra
  homomorphism.

## Notation

* `A →ₗc[R] B` : `R`-coalgebra homomorphism from `A` to `B`.

-/

@[expose] public section

open TensorProduct Coalgebra

universe u v w

/-- Given `R`-modules `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-coalgebra homomorphism `A →ₗc[R] B` is an `R`-linear map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
structure CoalgHom (R A B : Type*) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

@[inherit_doc CoalgHom]
infixr:25 " →ₗc " => CoalgHom _

@[inherit_doc]
notation:25 A " →ₗc[" R "] " B => CoalgHom R A B

/-- `CoalgHomClass F R A B` asserts `F` is a type of bundled coalgebra homomorphisms
from `A` to `B`. -/
class CoalgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] : Prop
    extends SemilinearMapClass F (RingHom.id R) A B where
  counit_comp : ∀ f : F, counit ∘ₗ (f : A →ₗ[R] B) = counit
  map_comp_comul : ∀ f : F, TensorProduct.map (f : A →ₗ[R] B)
    (f : A →ₗ[R] B) ∘ₗ comul = comul ∘ₗ (f : A →ₗ[R] B)

attribute [simp] CoalgHomClass.counit_comp CoalgHomClass.map_comp_comul

namespace CoalgHomClass

variable {R A B F : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [CoalgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `CoalgHomClass F R A B` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `A →ₗc[R] B`. -/
@[coe]
def toCoalgHom (f : F) : A →ₗc[R] B :=
  { (f : A →ₗ[R] B) with
    toFun := f
    counit_comp := CoalgHomClass.counit_comp f
    map_comp_comul := CoalgHomClass.map_comp_comul f }

instance instCoeToCoalgHom : CoeHead F (A →ₗc[R] B) :=
  ⟨CoalgHomClass.toCoalgHom⟩

@[simp]
theorem counit_comp_apply (f : F) (x : A) : counit (R := R) (f x) = counit (R := R) x :=
  LinearMap.congr_fun (counit_comp f) _

@[simp]
theorem map_comp_comul_apply (f : F) (x : A) :
    TensorProduct.map f f (σ₁₂ := .id _) (comul x) = comul (R := R) (f x) :=
  LinearMap.congr_fun (map_comp_comul f) _

end CoalgHomClass

namespace CoalgHom

variable {R A B C D : Type*}

section

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

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

/-- See Note [custom simps projection] -/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [AddCommMonoid α] [Module R α] [AddCommMonoid β]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₗc[R] β) : α → β := f

initialize_simps_projections CoalgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) :
    ⇑(f : A →ₗc[R] B) = f :=
  rfl

@[simp]
theorem coe_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A →ₗ[R] B) = f :=
  rfl

@[simp]
theorem toLinearMap_eq_coe (f : A →ₗc[R] B) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →ₗc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[norm_cast]
theorem coe_toAddMonoidHom (f : A →ₗc[R] B) : ⇑(f : A →+ B) = f :=
  rfl

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

@[ext high]
theorem ext_of_ring {f g : R →ₗc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
theorem mk_coe {f : A →ₗc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  ext fun _ => rfl

/-- Copy of a `CoalgHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : A →ₗc[R] B :=
  { toLinearMap := (f : A →ₗ[R] B).copy f' h
    counit_comp := by ext; simp_all
    map_comp_comul := by simp only [(f : A →ₗ[R] B).copy_eq f' h,
      CoalgHomClass.map_comp_comul] }

@[simp]
theorem coe_copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (R A)

/-- Identity map as a `CoalgHom`. -/
@[simps!] protected def id : A →ₗc[R] A :=
  { LinearMap.id with
    counit_comp := by ext; rfl
    map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

variable {R A}

@[simp, norm_cast]
theorem coe_id : ⇑(CoalgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toLinearMap : (CoalgHom.id R A : A →ₗ[R] A) = LinearMap.id := rfl

/-- Composition of coalgebra homomorphisms. -/
@[simps!] def comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : A →ₗc[R] C :=
  { (φ₁ : B →ₗ[R] C) ∘ₗ (φ₂ : A →ₗ[R] B) with
    counit_comp := by ext; simp
    map_comp_comul := by ext; simp [map_comp] }

@[simp]
theorem coe_comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

@[simp]
theorem comp_toLinearMap (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₗ[R] C) ∘ₗ (φ₂ : A →ₗ[R] B) := rfl

variable (φ : A →ₗc[R] B)

@[simp]
theorem comp_id : φ.comp (CoalgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (CoalgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : C →ₗc[R] D) (φ₂ : B →ₗc[R] C) (φ₃ : A →ₗc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₗc[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := CoalgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
theorem one_apply (x : A) : (1 : A →ₗc[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end

end CoalgHom

namespace Coalgebra

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

/-- The counit of a coalgebra as a `CoalgHom`. -/
noncomputable def counitCoalgHom : A →ₗc[R] R :=
  { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, rTensor_counit_comul, LinearMap.lTensor_tmul] }

@[simp]
theorem counitCoalgHom_apply (x : A) : counitCoalgHom R A x = counit (R := R) x := rfl

@[simp]
theorem counitCoalgHom_toLinearMap :
    counitCoalgHom R A = counit (R := R) (A := A) := rfl

variable {R}

instance subsingleton_to_ring : Subsingleton (A →ₗc[R] R) :=
  ⟨fun f g => CoalgHom.ext fun x => by
    have hf := CoalgHomClass.counit_comp_apply f x
    have hg := CoalgHomClass.counit_comp_apply g x
    simp_all only [CommSemiring.counit_apply]⟩

@[ext high]
theorem ext_to_ring (f g : A →ₗc[R] R) : f = g := Subsingleton.elim _ _

variable {A B}
/--
If `φ : A → B` is a coalgebra map and `a = ∑ xᵢ ⊗ yᵢ`, then `φ a = ∑ φ xᵢ ⊗ φ yᵢ`
-/
@[simps]
def Repr.induced {a : A} (repr : Repr R a)
    {F : Type*} [FunLike F A B] [CoalgHomClass F R A B]
    (φ : F) : Repr R (φ a) where
  index := repr.index
  left := φ ∘ repr.left
  right := φ ∘ repr.right
  eq := (congr($((CoalgHomClass.map_comp_comul φ).symm) a).trans <|
      by rw [LinearMap.comp_apply, ← repr.eq, map_sum]; rfl).symm

end Coalgebra
