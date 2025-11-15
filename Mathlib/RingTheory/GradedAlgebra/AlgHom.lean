/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `R`-linear homomorphisms of graded algebras

This file defines bundled `R`-linear homomorphisms of graded algebras.

## Main definitions

* `GradedAlgHom R 𝒜 ℬ`: the type of `R`-linear homomorphisms of graded algebras `𝒜` to `ℬ`.

## Notation

* `𝒜 →ₐᵍ[R] ℬ` : `R`-linear graded homomorphism from `𝒜` to `ℬ`.
-/

/-- An `R`-linear homomorphism of graded algebras, denoted `𝒜 →ₐᵍ[R] ℬ`. -/
structure GradedAlgHom (R : Type*) {S T A B ι : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule S A) (ℬ : ι → Submodule T B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A →ₐ[R] B, 𝒜 →+*ᵍ ℬ

/-- Reinterpret a graded algebra homomorphism as a graded ring homomorphism. -/
add_decl_doc GradedAlgHom.toGradedRingHom

@[inherit_doc]
notation:25 𝒜 " →ₐᵍ[" R "] " ℬ => GradedAlgHom R 𝒜 ℬ

namespace GradedAlgHom

variable {R S T U V A B C D ι : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] [CommSemiring U] [CommSemiring V]
  [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
  [Algebra R U] [Algebra U C] [Algebra R C] [IsScalarTower R U C]
  [Algebra R V] [Algebra V D] [Algebra R D] [IsScalarTower R V D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule S A} {ℬ : ι → Submodule T B} {𝒞 : ι → Submodule U C} {𝒟 : ι → Submodule V D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

section ofClass
variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `[GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]` into an
actual `GradedAlgHom`. This is declared as the default coercion from `F` to `𝒜 →ₐᵍ[R] ℬ`. -/
@[coe]
def ofClass (f : F) : 𝒜 →ₐᵍ[R] ℬ :=
  { (f : A →ₐ[R] B), (f : 𝒜 →+*ᵍ ℬ) with }

instance coeTC : CoeTC F (𝒜 →ₐᵍ[R] ℬ) :=
  ⟨ofClass⟩

end ofClass

instance gradedFunLike : GradedFunLike (𝒜 →ₐᵍ[R] ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem'
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr

instance algHomClass : AlgHomClass (𝒜 →ₐᵍ[R] ℬ) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

@[simp] lemma toAlgHom_ofClass {F : Type*} [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]
    (f : F) : (ofClass f : A →ₐ[R] B) = f := rfl

@[simp] lemma toGradedRingHom_ofClass {F : Type*} [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]
    (f : F) : (ofClass f : 𝒜 →+*ᵍ ℬ) = f := rfl

initialize_simps_projections GradedAlgHom (toFun → apply)

@[simp] protected theorem coe_coe {F : Type*} [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B] (f : F) :
    ⇑(f : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

@[simp] theorem toFun_eq_coe (f : 𝒜 →ₐᵍ[R] ℬ) : f.toFun = f := rfl

@[simp] theorem coe_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅ h₆) :
    ⇑(⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 →ₐᵍ[R] ℬ) = f :=
  rfl

@[simp, norm_cast]
theorem coe_algHom_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A →ₐ[R] B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp] theorem toAlgHom_eq_coe (f : 𝒜 →ₐᵍ[R] ℬ) : f.toAlgHom = f := rfl

@[simp] theorem toGRingHom_eq_coe (f : 𝒜 →ₐᵍ[R] ℬ) : f.toGradedRingHom = f := rfl

@[simp] theorem toAlgHom_toAddMonoidHom (f : 𝒜 →ₐᵍ[R] ℬ) : ((f : A →ₐ[R] B) : A →+ B) = f := rfl

@[simp] theorem toAlgHom_toMonoidHom (f : 𝒜 →ₐᵍ[R] ℬ) : ((f : A →ₐ[R] B) : A →* B) = f := rfl

@[simp] theorem toGRingHom_toAddMonoidHom (f : 𝒜 →ₐᵍ[R] ℬ) : ((f : 𝒜 →+*ᵍ ℬ) : A →+ B) = f := rfl

@[simp] theorem toGRingHom_toMonoidHom (f : 𝒜 →ₐᵍ[R] ℬ) : ((f : 𝒜 →+*ᵍ ℬ) : A →* B) = f := rfl

/-- Restrict the base ring to a "smaller" ring. -/
@[coe, simps!] def restrictScalars (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra R₀ A] [Algebra R₀ B]
    [IsScalarTower R₀ S A] [IsScalarTower R₀ R A] [IsScalarTower R₀ T B] [IsScalarTower R₀ R B]
    (f : 𝒜 →ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R₀] ℬ :=
  { f.toAlgHom.restrictScalars R₀, f with }

variable (f : 𝒜 →ₐᵍ[R] ℬ)

theorem coe_fn_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → (A → B)) :=
  DFunLike.coe_injective

theorem coe_fn_inj {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} : (f₁ : A → B) = f₂ ↔ f₁ = f₂ :=
  DFunLike.coe_fn_eq

theorem coe_algHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₐ[R] B) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

theorem coe_gRingHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → 𝒜 →+*ᵍ ℬ) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

theorem coe_linearMap_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₗ[R] B) :=
  AlgHom.toLinearMap_injective.comp coe_algHom_injective

theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+* B) :=
  AlgHom.coe_ringHom_injective.comp coe_algHom_injective

theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →* B) :=
  AlgHom.coe_monoidHom_injective.comp coe_algHom_injective

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+ B) :=
  AlgHom.coe_addMonoidHom_injective.comp coe_algHom_injective

section restrictScalars
variable {R₀ : Type*} [CommSemiring R₀] [Algebra R₀ R]
  [Algebra R₀ S] [Algebra R₀ T] [Algebra R₀ A] [Algebra R₀ B]
  [IsScalarTower R₀ S A] [IsScalarTower R₀ R A] [IsScalarTower R₀ T B] [IsScalarTower R₀ R B]

lemma coe_restrictScalars : ⇑(f.restrictScalars R₀) = f := rfl

lemma restrictScalars_coe_algHom : (f : A →ₐ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

lemma restrictScalars_coe_linearMap :
    (f : A →ₗ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

lemma restrictScalars_injective :
    Function.Injective (restrictScalars R₀ : (𝒜 →ₐᵍ[R] ℬ) → (𝒜 →ₐᵍ[R₀] ℬ)) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

end restrictScalars

/-- Consider using `congr($H x)` instead. -/
protected theorem congr_fun {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} (H : f₁ = f₂) (x : A) : f₁ x = f₂ x :=
  DFunLike.congr_fun H x

/-- Consider using `congr(f $h)` instead. -/
protected theorem congr_arg (f : 𝒜 →ₐᵍ[R] ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
theorem ext {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} (H : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ H

@[simp]
theorem mk_coe {f : 𝒜 →ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 →ₐᵍ[R] ℬ) = f :=
  rfl

@[simp]
theorem commutes (r : R) : f (algebraMap R A r) = algebraMap R B r :=
  f.commutes' r

theorem comp_ofId : (f : A →ₐ[R] B).comp (Algebra.ofId R A) = Algebra.ofId R B :=
  AlgHom.ext f.commutes

/-- If a `GradedRingHom` is `R`-linear, then it is a `GradedAlgHom`. -/
def mk' (f : 𝒜 →+*ᵍ ℬ) (h : ∀ (c : R) (x), f (c • x) = c • f x) : 𝒜 →ₐᵍ[R] ℬ :=
  { AlgHom.mk' _ h, f with }

@[simp]
theorem coe_mk' (f : 𝒜 →+*ᵍ ℬ) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section
variable (R 𝒜)

/-- Identity map as a `GradedAlgHom`. -/
@[simps!] protected def id : 𝒜 →ₐᵍ[R] 𝒜 :=
  { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]
theorem coe_id : ⇑(GradedAlgHom.id R 𝒜) = id := rfl

@[simp]
theorem id_toAlgHom : (GradedAlgHom.id R 𝒜 : A →ₐ[R] A) = AlgHom.id R A := rfl

end

/-- If `g` and `f` are `R`-linear graded algebra homomorphisms with the domain of `g` equal to
the codomain of `f`, then `g.comp f` is the graded algebra homomorphism `x ↦ g (f x)`.
-/
@[simps!] def comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R] 𝒞 :=
  { (g : B →ₐ[R] C).comp (f : A →ₐ[R] B), (g : ℬ →+*ᵍ 𝒞).comp (f : 𝒜 →+*ᵍ ℬ) with }

@[simp]
theorem coe_comp (g : B →ₐ[R] C) (f : 𝒜 →ₐᵍ[R] ℬ) : ⇑(g.comp f) = g ∘ f := rfl

theorem comp_toGRingHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f : 𝒜 →+*ᵍ 𝒞) = (g : ℬ →+*ᵍ 𝒞).comp f := rfl

theorem comp_toAlgHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f : A →ₐ[R] C) = (g : B →ₐ[R] C).comp f := rfl

@[simp]
theorem comp_id : f.comp (.id R 𝒜) = f := rfl

@[simp]
theorem id_comp : (GradedAlgHom.id R ℬ).comp f = f := rfl

theorem comp_assoc (fCD : 𝒞 →ₐᵍ[R] 𝒟) (fBC : ℬ →ₐᵍ[R] 𝒞) (fAB : 𝒜 →ₐᵍ[R] ℬ) :
    (fCD.comp fBC).comp fAB = fCD.comp (fBC.comp fAB) := rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
instance End : Monoid (𝒜 →ₐᵍ[R] 𝒜) where
  mul := comp
  one := .id R 𝒜
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

@[simp] theorem coe_one : ⇑(1 : 𝒜 →ₐᵍ[R] 𝒜) = id := rfl

@[simp] theorem coe_mul (f g : 𝒜 →ₐᵍ[R] 𝒜) : ⇑(f * g) = f ∘ g := rfl

@[simp] theorem coe_pow (f : 𝒜 →ₐᵍ[R] 𝒜) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]

lemma cancel_right {g₁ g₂ : ℬ →ₐᵍ[R] 𝒞} {f : 𝒜 →ₐᵍ[R] ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ coe_algHom_injective <| (AlgHom.cancel_right hf).1 congr($h), fun h ↦ h ▸ rfl⟩

lemma cancel_left {g₁ g₂ : 𝒜 →ₐᵍ[R] ℬ} {f : ℬ →ₐᵍ[R] 𝒞} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h ↦ coe_algHom_injective <| (AlgHom.cancel_left hf).1 congr($h), fun h ↦ h ▸ rfl⟩

/-- `toAlgHom` as a `MonoidHom`. -/
@[simps] def toEnd : (𝒜 →ₐᵍ[R] 𝒜) →* (A →ₐ[R] A) where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Subsingleton B]

instance uniqueOfRight : Unique (𝒜 →ₐᵍ[R] ℬ) where
  default := { (default : A →ₐ[R] B) with map_mem' hx := by aesop }
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma default_apply (x : A) : (default : 𝒜 →ₐᵍ[R] ℬ) x = 0 :=
  rfl

end

end GradedAlgHom
