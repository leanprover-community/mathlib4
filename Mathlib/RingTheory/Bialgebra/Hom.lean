/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Homomorphisms of `R`-bialgebras

This file defines bundled homomorphisms of `R`-bialgebras. We simply mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `BialgHom R A B`: the type of `R`-bialgebra morphisms from `A` to `B`.
* `Bialgebra.counitBialgHom R A : A →ₐc[R] R`: the counit of a bialgebra as a bialgebra
  homomorphism.

## Notation

* `A →ₐc[R] B` : `R`-bialgebra homomorphism from `A` to `B`.

-/

@[expose] public section

open TensorProduct Bialgebra Coalgebra Function

universe u v w

/-- Given `R`-algebras `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-bialgebra homomorphism `A →ₐc[R] B` is an `R`-algebra map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
structure BialgHom (R A B : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A →* B

/-- Reinterpret a `BialgHom` as a `MonoidHom` -/
add_decl_doc BialgHom.toMonoidHom

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

/-- `BialgHomClass F R A B` asserts `F` is a type of bundled bialgebra homomorphisms
from `A` to `B`. -/
class BialgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] : Prop
    extends CoalgHomClass F R A B, MonoidHomClass F A B

namespace BialgHomClass

variable {R A B F : Type*}

section

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [BialgHomClass F R A B]

instance (priority := 100) toAlgHomClass : AlgHomClass F R A B where
  map_mul := map_mul
  map_one := map_one
  map_add := map_add
  map_zero := map_zero
  commutes := fun c r => by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

/-- Turn an element of a type `F` satisfying `BialgHomClass F R A B` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `A →ₐc[R] B`. -/
@[coe]
def toBialgHom (f : F) : A →ₐc[R] B :=
  { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }

instance instCoeToBialgHom :
    CoeHead F (A →ₐc[R] B) :=
  ⟨BialgHomClass.toBialgHom⟩

end
section
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]
  [FunLike F A B] [BialgHomClass F R A B]

@[simp]
theorem counitAlgHom_comp (f : F) :
    (counitAlgHom R B).comp (AlgHomClass.toAlgHom f) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
theorem map_comp_comulAlgHom (f : F) :
    (Algebra.TensorProduct.map (AlgHomClass.toAlgHom f) (AlgHomClass.toAlgHom f)).comp
      (comulAlgHom R A) = (comulAlgHom R B).comp (AlgHomClass.toAlgHom f) :=
  AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

end
end BialgHomClass

namespace BialgHom

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

section AlgebraCoalgebra

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

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

/-- See Note [custom simps projection] -/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [Semiring α] [Algebra R α] [Semiring β]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₐc[R] β) : α → β := f

initialize_simps_projections BialgHom (toFun → apply, as_prefix toCoalgHom)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐc[R] B) = f :=
  rfl

@[simp]
theorem coe_mk {f : A →ₗc[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A →ₐc[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_coalgHom_mk {f : A →ₗc[R] B} (h h₁) :
    ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A →ₗc[R] B) = f := by
  rfl

@[simp, norm_cast]
theorem coe_toCoalgHom (f : A →ₐc[R] B) : ⇑(f : A →ₗc[R] B) = f :=
  rfl

lemma toCoalgHom_apply (f : A →ₐc[R] B) (a : A) : f.toCoalgHom a = f a := rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →ₐc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

/-- Turn a bialgebra homomorphism into an algebra homomorphism. -/
@[coe]
def toAlgHom (f : A →ₐc[R] B) : A →ₐ[R] B where
  __ := f
  map_zero' := f.map_zero
  commutes' := by
    simp [Algebra.algebraMap_eq_smul_one, toCoalgHom_apply]

instance : Coe (A →ₐc[R] B) (A →ₐ[R] B) := ⟨toAlgHom⟩

@[simp, norm_cast]
theorem coe_toAlgHom (f : A →ₐc[R] B) : ⇑(f : A →ₐ[R] B) = f :=
  rfl

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

@[ext high]
theorem ext_of_ring {f g : R →ₐc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
theorem mk_coe {f : A →ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A →ₐc[R] B) = f :=
  rfl

/-- Copy of a `BialgHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : A →ₐc[R] B) (f' : A → B) (h : f' = ⇑f) : A →ₐc[R] B :=
  { toCoalgHom := (f : A →ₗc[R] B).copy f' h
    map_one' := by simp_all
    map_mul' := by intros; simp_all }

@[simp]
theorem coe_copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

section

variable (R A)

/-- Identity map as a `BialgHom`. -/
@[simps!] protected def id : A →ₐc[R] A :=
  { CoalgHom.id R A, AlgHom.id R A with }

variable {R A}

@[simp, norm_cast]
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toCoalgHom : BialgHom.id R A = CoalgHom.id R A :=
  rfl

@[simp]
theorem id_toAlgHom : BialgHom.id R A = AlgHom.id R A :=
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
theorem comp_toAlgHom (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₐ[R] C).comp (φ₂ : A →ₐ[R] B) :=
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

instance : One (A →ₐc[R] A) where one := BialgHom.id R A
instance : Mul (A →ₐc[R] A) where mul := comp
instance : Pow (A →ₐc[R] A) ℕ where
  pow f n := npowRec n f |>.copy f^[n] (Nat.rec rfl (fun _ => congrArg (· ∘ f)) n)

@[simps! -isSimp toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐc[R] A) where
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  npow n f := f ^ n

@[simp]
theorem one_apply (x : A) : (1 : A →ₐc[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end AlgebraCoalgebra

variable [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
@[simps!]
def ofAlgHom (f : A →ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A)
    (map_comp_comul :
      (Algebra.TensorProduct.map f f).comp (comulAlgHom _ _) = (comulAlgHom _ _).comp f) :
    A →ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := congr(($counit_comp).toLinearMap)
  map_comp_comul := congr(($map_comp_comul).toLinearMap)

@[simp]
theorem counitAlgHom_comp (f : A →ₐc[R] B) :
    (counitAlgHom R B).comp f = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
theorem map_comp_comulAlgHom (f : A →ₐc[R] B) :
    (Algebra.TensorProduct.map f f).comp (comulAlgHom R A) = (comulAlgHom R B).comp f :=
  AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

end BialgHom

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R A) in
/-- The unit of a bialgebra as a `BialgHom`. -/
noncomputable def unitBialgHom : R →ₐc[R] A :=
  .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

variable (R A) in
/-- The counit of a bialgebra as a `BialgHom`. -/
noncomputable def counitBialgHom : A →ₐc[R] R :=
  { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]
theorem counitBialgHom_apply (x : A) :
    counitBialgHom R A x = Coalgebra.counit x := rfl

@[simp]
theorem counitBialgHom_toCoalgHom :
    counitBialgHom R A = Coalgebra.counitCoalgHom R A := rfl

@[simp] lemma counitBialgHom_self : counitBialgHom R R = .id R R := rfl

instance subsingleton_to_ring : Subsingleton (A →ₐc[R] R) :=
  ⟨fun _ _ => BialgHom.coe_coalgHom_injective (Subsingleton.elim _ _)⟩

@[ext high]
theorem ext_to_ring (f g : A →ₐc[R] R) : f = g := Subsingleton.elim _ _

end Bialgebra
