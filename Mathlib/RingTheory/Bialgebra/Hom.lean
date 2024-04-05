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

open TensorProduct Bialgebra BigOperators

universe u v w u₁ v₁

/-- Given `R`-algebras `A, B` with comultiplcation maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-bialgebra homomorphism `A →ₐc[R] B` is an `R`-linear map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
structure BialgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A →ₐ[R] B

/-- Reinterpret a `BialgHom` as an `AlgHom` -/
add_decl_doc BialgHom.toAlgHom

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

/-- `BialgHomClass F R A B` asserts `F` is a type of bundled bialgebra homomorphisms
from `A` to `B`.  -/
class BialgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
    extends CoalgHomClass F R A B, AlgHomClass F R A B : Prop

namespace BialgHomClass

variable {R A B F : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [BialgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `BialgHomClass F R A B` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `A →ₐc[R] B`. -/
@[coe]
def toBialgHom {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) : A →ₐc[R] B :=
  { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }

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
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp_all

instance bialgHomClass : BialgHomClass (A →ₐc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'
  map_zero := fun f => f.map_zero'
  commutes := fun f => f.commutes'

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Algebra R α] [Semiring β]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₐc[R] β) : α → β := f

initialize_simps_projections BialgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐc[R] B) = f :=
  rfl

-- removed `simp`
theorem toFun_eq_coe (f : A →ₐc[R] B) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk {f : A →ₗc[R] B} (h h₁ h₂ h₃) : ((⟨f, h, h₁, h₂, h₃⟩ : A →ₐc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    ⇑(⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅, h₆, h₇⟩ : A →ₐc[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toCoalgHom_mk {f : A →ₗc[R] B} (h h₁ h₂ h₃) :
    ((⟨f, h, h₁, h₂, h₃⟩ : A →ₐc[R] B) : A →ₗc[R] B) = f := by
  rfl

/- which of the next 3 should exist? 1st and 3rd can be proved by `simp` and `norm_cast`.
for the 2nd, maybe the `LinearMap` version of e.g. `AlgHom.coe_coe` is missing. -/
@[simp, norm_cast]
theorem coe_toCoalgHom (f : A →ₐc[R] B) : ⇑(f : A →ₗc[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →ₐc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAlgHom (f : A →ₐc[R] B) : ⇑(f : A →ₐ[R] B) = f :=
  rfl

@[simp]
theorem toAlgHom_toLinearMap (f : A →ₐc[R] B) :
    ((f : A →ₐ[R] B) : A →ₗ[R] B) = f := by
  rfl

variable (φ : A →ₐc[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐc[R] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_coalgHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₗc[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₗc[R] B) : A → B) = ((φ₂ : A →ₗc[R] B) : A → B) from congr_arg _ H

theorem coe_algHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₐ[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₐ[R] B) : A → B) = ((φ₂ : A →ₐ[R] B) : A → B) from congr_arg _ H

theorem coe_linearMap_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₗ[R] B) :=
  CoalgHom.coe_linearMap_injective.comp coe_coalgHom_injective

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
theorem mk_coe {f : A →ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇) :
    (⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅, h₆, h₇⟩ : A →ₐc[R] B) = f :=
  rfl

@[simp]
theorem counit_comp : Coalgebra.counit ∘ₗ (φ : A →ₗ[R] B) = Coalgebra.counit :=
  φ.counit_comp'

@[simp]
theorem map_comp_comul :
    TensorProduct.map φ φ ∘ₗ Coalgebra.comul = Coalgebra.comul ∘ₗ (φ : A →ₗ[R] B) :=
  φ.map_comp_comul'

@[simp]
theorem counitAlgHom_comp {A : Type v} {B : Type w} [Semiring A]
    [Semiring B] [Bialgebra R A] [Bialgebra R B] (φ : A →ₐc[R] B) :
    (counitAlgHom R B).comp (φ : A →ₐ[R] B) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (counit_comp φ)

@[simp]
theorem map_comp_comulAlgHom {A : Type v} {B : Type w} [Semiring A]
    [Semiring B] [Bialgebra R A] [Bialgebra R B] (φ : A →ₐc[R] B) :
    (Algebra.TensorProduct.map φ φ).comp (comulAlgHom R A) = (comulAlgHom R B).comp φ :=
  AlgHom.toLinearMap_injective (map_comp_comul φ)

@[simp]
theorem counit_comp_apply (x : A) : Coalgebra.counit (φ x) = Coalgebra.counit (R := R) x :=
  LinearMap.congr_fun φ.counit_comp _

@[simp]
theorem map_comp_comul_apply (x : A) :
    TensorProduct.map φ φ (Coalgebra.comul x) = Coalgebra.comul (R := R) (φ x) :=
  LinearMap.congr_fun φ.map_comp_comul _

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

protected theorem map_sum {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
  map_sum _ _ _

protected theorem map_finsupp_sum {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.sum g) = f.sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _

section

variable (R A)

/-- Identity map as a `BialgHom`. -/
@[simps!] protected def id : A →ₐc[R] A :=
{ CoalgHom.id R A, AlgHom.id R A with }

variable {R A}

@[simp]
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toCoalgHom : BialgHom.id R A = CoalgHom.id R A :=
  rfl

end

/-- Composition of bialgebra homomorphisms. -/
@[simps!] def comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : A →ₐc[R] C :=
  { (φ₁ : B →ₗc[R] C).comp (φ₂ : A →ₗc[R] B), (φ₁ : B →ₐ[R] C).comp (φ₂ : A →ₐ[R] B) with }

@[simp]
theorem coe_comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

@[simp]
theorem comp_toCoalgHom (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₗc[R] C).comp (φ₂ : A →ₗc[R] B) :=
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

section Ring

variable [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable [CoalgebraStruct R A] [CoalgebraStruct R B] (φ : A →ₐc[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

end Ring

end BialgHom

namespace Bialgebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The counit of a bialgebra as a `BialgHom`. -/
def counitBialgHom : A →ₐc[R] R :=
  { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]
theorem counitBialgHom_apply (x : A) :
    counitBialgHom R A x = Coalgebra.counit x := rfl

@[simp]
theorem counitBialgHom_toCoalgHom :
    counitBialgHom R A = Coalgebra.counitCoalgHom R A := rfl

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
