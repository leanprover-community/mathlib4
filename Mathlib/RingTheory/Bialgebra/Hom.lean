/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Homomorphisms of `R`-bialgebras

This file defines bundled homomorphisms of `R`-bialgebras. We simply mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `BialgHom R A B`: the type of `R`-bialgebra morphisms from `A` to `B`.
* `Bialgebra.counitBialgHom R A : A →ₐc[R] R`: the counit of a bialgebra as a bialgebra
homomorphism.

## Notations

* `A →ₐc[R] B` : `R`-algebra homomorphism from `A` to `B`.

-/

open TensorProduct Bialgebra

universe u v w u₁ v₁

/-- Given `R`-algebras `A, B` with comultiplcation maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-bialgebra homomorphism `A →ₐc[R] B` is an `R`-linear map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
structure BialgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A →ₐ[R] B

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

/-- `BialgHomClass F R A B` asserts `F` is a type of bundled bialgebra homomorphisms
from `A` to `B`.  -/
class BialgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
    extends CoalgHomClass F R A B, AlgHomClass F R A B

namespace BialgHomClass

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]

/-- Turn an element of a type `F` satisfying `BialgHomClass F R A B` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `A →ₐc[R] B`. -/
@[coe]
def toBialgHom {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) : A →ₐc[R] B :=
  { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f
    counit_comp := BialgHomClass.counit_comp f
    map_comp_comul := BialgHomClass.map_comp_comul f }

instance coeTC {F : Type*} [FunLike F A B] [BialgHomClass F R A B] : CoeTC F (A →ₐc[R] B) :=
  ⟨BialgHomClass.toBialgHom⟩

end BialgHomClass

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]

variable [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

instance funLike : FunLike (A →ₐc[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

instance bialgHomClass : BialgHomClass (A →ₐc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β]
    [Algebra R α] [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₐc[R] β) : α → β := f

initialize_simps_projections BialgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐc[R] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →ₐc[R] B) : f.toFun = f :=
  rfl

/-attribute [coe] BialgHom.toLinearMap

instance coeOutLinearMap : CoeOut (A →ₐc[R] B) (A →ₗ[R] B) :=
  ⟨BialgHom.toLinearMap⟩

/-- The `AddMonoidHom` underlying a coalgebra homomorphism. -/
@[coe]
def toAddMonoidHom' (f : A →ₐc[R] B) : A →+ B := (f : A →ₗ[R] B)

instance coeOutAddMonoidHom : CoeOut (A →ₐc[R] B) (A →+ B) :=
  ⟨BialgHom.toAddMonoidHom'⟩
-/

@[simp]
theorem coe_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ ) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₐc[R] B) = f :=
  rfl

@[norm_cast]
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →ₐc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₐc[R] B) : ⇑(f : A →+ B) = f :=
  rfl

variable (φ : A →ₐc[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐc[R] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_coalgHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₗc[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₗ[R] B) : A → B) = ((φ₂ : A →ₗ[R] B) : A → B) from congr_arg _ H

theorem coe_algHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₐ[R] B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₐc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : A →ₐc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →ₐc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →ₐc[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff

@[ext high]
theorem ext_of_ring {f g : R →ₐc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
theorem mk_coe {f : A →ₐc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₐc[R] B) = f :=
  ext fun _ => rfl

@[simp]
theorem counit_comp_apply (x : A) : counit (φ x) = counit (R := R) x :=
  LinearMap.congr_fun φ.counit_comp _

@[simp]
theorem map_comp_comul_apply (x : A) :
    TensorProduct.map φ φ (comul x) = comul (R := R) (φ x) :=
  LinearMap.congr_fun φ.map_comp_comul _

theorem counitAlgHom_comp : (φ : A →ₐ[R] B).comp (counitAlgHom R B) = counitAlgHom R A := by
  ext; exact LinearMap.congr_fun φ.counit_comp _

theorem map_comp_comulAlgHom :
    (comulAlgHom R B).comp (Algebra.TensorProduct.map φ φ) = comulAlgHom R A := by
  ext; exact LinearMAp.congr_fun φ.map_comp_comul _

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _

protected theorem map_mul (r s : A) : φ (r * s) = φ r * φ s :=
  map_mul  _ _ _

protected theorem map_zero : φ 0 = 0 :=
  map_zero _

protected theorem map_one : φ 1 = 1 :=
  map_one _

protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _

section

variable (R A)

/-- Identity map as a `BialgHom`. -/
@[simps! toCoalgHom] protected def id : A →ₐc[R] A :=
{ CoalgHom.id R A with
  map_mul := fun _ _ => rfl
  map_one := fun _ _ }

@[simp]
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

end

theorem id_apply (p : A) : BialgHom.id R A p = p :=
  rfl

/-- Composition of bialgebra homomorphisms. -/
@[simps! toLinearMap] def comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : A →ₐc[R] C :=
  { φ₁.toLinearMap ∘ₗ φ₂ with
    counit_comp := by ext; simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply,
      counit_comp_apply]
    map_comp_comul := by ext; simp only [map_comp, LinearMap.coe_comp, Function.comp_apply,
      map_comp_comul_apply, coe_toLinearMap] }

@[simp]
theorem coe_comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

@[simp]
theorem comp_id : φ.comp (BialgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (BialgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : C →ₐc[R] D) (φ₂ : B →ₐc[R] C) (φ₃ : A →ₐc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

/-theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (BialgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl-/

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐc[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := BialgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl

@[simp]
theorem one_apply (x : A) : (1 : A →ₐc[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end Semiring

section AddCommGroup

variable [CommSemiring R] [AddCommGroup A] [AddCommGroup B] [Algebra R A] [Algebra R B]

variable [CoalgebraStruct R A] [CoalgebraStruct R B] (φ : A →ₐc[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

end AddCommGroup

end BialgHom

namespace Bialgebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Bialgebra R A]

/-- The counit of a bialgebra as a `BialgHom`. -/
@[simps! toLinearMap] def counitBialgHom : A →ₐc[R] R :=
  { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.coe_comp, Function.comp_apply,
        rTensor_counit_comul, LinearMap.lTensor_tmul] }

variable {R}

instance subsingleton_to_ring : Subsingleton (A →ₐc[R] R) :=
  ⟨fun f g => BialgHom.ext fun x => by
    have hf := LinearMap.ext_iff.1 f.counit_comp x
    have hg := LinearMap.ext_iff.1 g.counit_comp x
    simp_all only [LinearMap.coe_comp, BialgHom.coe_toLinearMap, Function.comp_apply,
      CommSemiring.counit_apply, hf, hg]⟩

@[ext high]
theorem ext_to_ring (f g : A →ₐc[R] R) : f = g := Subsingleton.elim _ _

end Bialgebra
