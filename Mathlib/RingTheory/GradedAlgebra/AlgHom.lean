/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `R`-linear homomorphisms of graded algebras

This file defines bundled `R`-linear homomorphisms of graded `R`-algebras.

## Main definitions

* `GradedAlgHom R 𝒜 ℬ`: the type of `R`-linear homomorphisms of `R`-graded algebras `𝒜` to `ℬ`.

## Notation

* `𝒜 →ₐᵍ[R] ℬ` : `R`-linear graded homomorphism from `𝒜` to `ℬ`.
-/

@[expose] public section

/-- An `R`-linear homomorphism of graded algebras, denoted `𝒜 →ₐᵍ[R] ℬ`. -/
structure GradedAlgHom (R : Type*) {A B ι : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A →ₐ[R] B, 𝒜 →+*ᵍ ℬ

/-- Reinterpret a graded algebra homomorphism as a graded ring homomorphism. -/
add_decl_doc GradedAlgHom.toGradedRingHom

@[inherit_doc]
notation:25 𝒜 " →ₐᵍ[" R "] " ℬ => GradedAlgHom R 𝒜 ℬ

namespace GradedAlgHom

variable {R S T U V A B C D ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} {𝒞 : ι → Submodule R C} {𝒟 : ι → Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

section ofClass
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]` into an actual `GradedAlgHom`.

In future mathlib this will be deprioritised in favour of using structural projections. -/
def ofClass (f : F) : 𝒜 →ₐᵍ[R] ℬ :=
  { (AlgHomClass.toAlgHom f : A →ₐ[R] B), (.ofClass f : 𝒜 →+*ᵍ ℬ) with }

end ofClass

instance : FunLike (𝒜 →ₐᵍ[R] ℬ) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr

instance : GradedFunLike (𝒜 →ₐᵍ[R] ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem

instance : AlgHomClass (𝒜 →ₐᵍ[R] ℬ) R A B where
  map_add f := f.map_add
  map_zero f := f.map_zero
  map_mul f := f.map_mul
  map_one f := f.map_one
  commutes f := f.commutes

attribute [coe] GradedAlgHom.toAlgHom

instance : CoeOut (𝒜 →ₐᵍ[R] ℬ) (A →ₐ[R] B) := ⟨toAlgHom⟩

@[simp] lemma toAlgHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : (ofClass f : A →ₐ[R] B) = AlgHomClass.toAlgHom f := rfl

@[simp] lemma toGradedRingHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) :
    ((ofClass f).toGradedRingHom : 𝒜 →+*ᵍ ℬ) = GradedRingHom.ofClass f := rfl

initialize_simps_projections GradedAlgHom (toFun → apply)

@[simp] theorem coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : ⇑(.ofClass f : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

@[simp] theorem coe_toAlgHom (f : 𝒜 →ₐᵍ[R] ℬ) : ⇑f.toAlgHom = f := rfl

@[simp] theorem coe_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A → B) = f := rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅ h₆) :
    ⇑(⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 →ₐᵍ[R] ℬ) = f := rfl

theorem coe_algHom_mk {f : A →ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 →ₐᵍ[R] ℬ) : A →ₐ[R] B) = f := by
  dsimp only

variable (f : 𝒜 →ₐᵍ[R] ℬ)

theorem coe_fn_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → (A → B)) :=
  DFunLike.coe_injective

theorem coe_fn_inj {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} : (f₁ : A → B) = f₂ ↔ f₁ = f₂ :=
  DFunLike.coe_fn_eq

theorem coe_algHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₐ[R] B) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

theorem toGradedRingHom_injective : Function.Injective (toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ)) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

theorem coe_linearMap_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →ₗ[R] B) :=
  AlgHom.toLinearMap_injective.comp coe_algHom_injective

theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+* B) :=
  AlgHom.coe_ringHom_injective.comp coe_algHom_injective

theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →* B) :=
  AlgHom.coe_monoidHom_injective.comp coe_algHom_injective

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 →ₐᵍ[R] ℬ) → A →+ B) :=
  AlgHom.coe_addMonoidHom_injective.comp coe_algHom_injective

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

section id
variable (R 𝒜)

/-- Identity map as a `GradedAlgHom`. -/
@[simps!] protected def id : 𝒜 →ₐᵍ[R] 𝒜 :=
  { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]
theorem coe_id : ⇑(GradedAlgHom.id R 𝒜) = id := rfl

@[simp]
theorem id_toAlgHom : (GradedAlgHom.id R 𝒜 : A →ₐ[R] A) = AlgHom.id R A := rfl

end id

/-- If `g` and `f` are `R`-linear graded algebra homomorphisms with the domain of `g` equal to
the codomain of `f`, then `g.comp f` is the graded algebra homomorphism `x ↦ g (f x)`.
-/
@[simps!] def comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R] 𝒞 :=
  { (g : B →ₐ[R] C).comp (f : A →ₐ[R] B),
    (g.toGradedRingHom : ℬ →+*ᵍ 𝒞).comp (f.toGradedRingHom : 𝒜 →+*ᵍ ℬ) with }

@[simp]
theorem coe_comp (g : B →ₐ[R] C) (f : 𝒜 →ₐᵍ[R] ℬ) : ⇑(g.comp f) = g ∘ f := rfl

theorem comp_toGradedRingHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f).toGradedRingHom = g.toGradedRingHom.comp f.toGradedRingHom := rfl

theorem comp_toAlgHom (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) :
    (g.comp f : A →ₐ[R] C) = (g : B →ₐ[R] C).comp f := rfl

@[simp]
theorem comp_id : f.comp (.id R 𝒜) = f := rfl

@[simp]
theorem id_comp : (GradedAlgHom.id R ℬ).comp f = f := rfl

theorem comp_assoc (fCD : 𝒞 →ₐᵍ[R] 𝒟) (fBC : ℬ →ₐᵍ[R] 𝒞) (fAB : 𝒜 →ₐᵍ[R] ℬ) :
    (fCD.comp fBC).comp fAB = fCD.comp (fBC.comp fAB) := rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
instance : Monoid (𝒜 →ₐᵍ[R] 𝒜) where
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

/-- We enrich the existing function `toAlgHom` with the structure of a `MonoidHom`, to produce a
bundled function that we now call `toEnd`. -/
@[simps] def toEnd : (𝒜 →ₐᵍ[R] 𝒜) →* (A →ₐ[R] A) where
  toFun := toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Subsingleton B]

instance : Unique (𝒜 →ₐᵍ[R] ℬ) where
  default := { (default : A →ₐ[R] B) with map_mem hx := by aesop }
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma default_apply (x : A) : (default : 𝒜 →ₐᵍ[R] ℬ) x = 0 :=
  rfl

end

section restrictScalars

/-- Restrict the base ring to a "smaller" ring. -/
@[coe, simps!] def restrictScalars (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 →ₐᵍ[R] ℬ) : (𝒜 · |>.restrictScalars R₀) →ₐᵍ[R₀] (ℬ · |>.restrictScalars R₀) :=
  { f.toAlgHom.restrictScalars R₀, f with }

variable (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 →ₐᵍ[R] ℬ)

@[simp] lemma coe_restrictScalars : ⇑(f.restrictScalars R₀) = f := rfl

@[simp] lemma restrictScalars_coe_algHom :
    (f : A →ₐ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

@[simp] lemma restrictScalars_coe_linearMap :
    (f : A →ₗ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

lemma restrictScalars_injective :
    Function.Injective (restrictScalars R₀ : (𝒜 →ₐᵍ[R] ℬ) → _) :=
  fun _ _ h ↦ coe_fn_injective congr($h)

end restrictScalars

end GradedAlgHom
