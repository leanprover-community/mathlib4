/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notation

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

@[expose] public section

universe u v w x y z

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`). -/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

/-- Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`. -/
structure AlgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends RingHom A B, A →ₛₗ[φ] B

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

/-- Reinterpret an `AlgHom` as a `LinearMap` -/
add_decl_doc AlgHom.toLinearMap

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => AlgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => AlgHom φ A B

@[inherit_doc AlgHom]
infixr:25 " →ₐ " => AlgHom (RingHom.id _)

@[inherit_doc]
notation:25 A " →ₐ[" R "] " B => AlgHom (RingHom.id R) A B

/-- The algebra morphism underlying `algebraMap` -/
def Algebra.algHom (R A B : Type*)
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    A →ₐ[R] B where
  toRingHom := algebraMap A B
  map_smul' r x := by simp [algebraMap_eq_smul_one, smul_assoc]

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`. -/
abbrev AlgHomClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [FunLike F A B] : Prop :=
  SemialgHomClass F (RingHom.id R) A B

protected lemma AlgHomClass.map_smul {F : Type*} {R A B : outParam Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (r : R) (x : A) : f (r • x) = r • f x := by rw [map_smul]

protected lemma AlgHomClass.commutes {F : Type*} {R A B : outParam Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (r : R) : f (algebraMap R A r) = algebraMap R B r := by
  simp [Algebra.algebraMap_eq_smul_one]

-- For now, don't replace `AlgHom.commutes` and `AlgHomClass.commutes` with the more generic lemma.
-- The file `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean` slows down by
-- 15% if we would do so (see benchmark on PR https://github.com/leanprover-community/mathlib4/pull/18040).
-- attribute [simp] AlgHomClass.commutes

namespace SemialgHomClass

variable (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

variable {F} {A B} {φ} (f : F)

@[coe]
def semialgHom : A →ₛₐ[φ] B where
  toFun := f
  map_add' := map_add f
  map_one' := map_one f
  map_mul' := map_mul f
  map_zero' := map_zero f
  map_smul' := map_smulₛₗ f

/-- Reinterpret an element of a type of semialgebra maps as a semialgebra map. -/
instance : CoeTC F (A →ₛₐ[φ] B) where
  coe f := semialgHom f

end SemialgHomClass

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- -- see Note [lower instance priority]
-- instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
--   { ‹AlgHomClass F R A B› with
--     map_smulₛₗ := fun f r x => by
--       simp only [Algebra.smul_def, map_mul, RingHom.id_apply] }

/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B where
  __ := (f : A →+* B)
  toFun := f
  map_smul' := AlgHomClass.map_smul f

instance coeTC {F : Type*} [FunLike F A B] [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B) :=
  ⟨AlgHomClass.toAlgHom⟩

end AlgHomClass

namespace AlgHom

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x} {C : Type y} {D : Type z}

section Semiring

variable [CommSemiring R] [CommSemiring S][Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable {φ : R →+* S}
variable [Algebra R A] [Algebra S B] [Algebra S D]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩
    rcases g
    congr

instance semialgHomClas : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_smulₛₗ f := f.map_smul'

-- instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
--   map_add f := f.map_add'
--   map_zero f := f.map_zero'
--   map_mul f := f.map_mul'
--   map_one f := f.map_one'
--   map_smulₛₗ f := f.map_smul'

lemma _root_.Algebra.algHom_apply (R A B : Type*) [CommSemiring R] [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (x : A) :
    Algebra.algHom R A B x = algebraMap A B x := rfl

@[simp] lemma _root_.AlgHomClass.toLinearMap_toAlgHom {R A B F : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (AlgHomClass.toAlgHom f : A →ₗ[R] B) = f := rfl

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} {α : Type w} {β : Type x}
    [Semiring α] [Semiring β] [Algebra R α] [Algebra S β] (f : α →ₛₐ[φ] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [SemialgHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₐ[φ] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →ₛₐ[φ] B) : f.toFun = f :=
  rfl

/-- Turn an algebra homomorphism into the corresponding multiplicative monoid homomorphism. -/
@[coe]
def toMonoidHom' (f : A →ₛₐ[φ] B) : A →* B := (f : A →+* B)

instance coeOutMonoidHom : CoeOut (A →ₛₐ[φ] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩

/-- Turn an algebra homomorphism into the corresponding additive monoid homomorphism. -/
@[coe]
def toAddMonoidHom' (f : A →ₛₐ[φ] B) : A →+ B := (f : A →+* B)

instance coeOutAddMonoidHom : CoeOut (A →ₛₐ[φ] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩

@[simp]
theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁) (h₂) (h₃) (h₄) (h₅) :
    ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₛₐ[φ] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₛₐ[φ] B) : A →+* B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_toRingHom (f : A →ₛₐ[φ] B) : ⇑(f : A →+* B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toMonoidHom (f : A →ₛₐ[φ] B) : ⇑(f : A →* B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₛₐ[φ] B) : ⇑(f : A →+ B) = f :=
  rfl

@[simp]
theorem toRingHom_toMonoidHom (f : A →ₛₐ[φ] B) : ((f : A →+* B) : A →* B) = f :=
  rfl

@[simp]
theorem toRingHom_toAddMonoidHom (f : A →ₛₐ[φ] B) : ((f : A →+* B) : A →+ B) = f :=
  rfl

variable (f : A →ₛₐ[φ] B)

theorem coe_fn_injective : @Function.Injective (A →ₛₐ[φ] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {f₁ f₂ : A →ₛₐ[φ] B} : (f₁ : A → B) = f₂ ↔ f₁ = f₂ :=
  DFunLike.coe_fn_eq

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₛₐ[φ] B) → A →+* B) := fun f₁ f₂ H =>
  coe_fn_injective <| show ((f₁ : A →+* B) : A → B) = ((f₂ : A →+* B) : A → B) from congr_arg _ H

theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₛₐ[φ] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₛₐ[φ] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective

protected theorem congr_fun {f₁ f₂ : A →ₛₐ[φ] B} (H : f₁ = f₂) (x : A) : f₁ x = f₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (f : A →ₛₐ[φ] B) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
theorem ext {f₁ f₂ : A →ₛₐ[φ] B} (H : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ H

@[simp]
theorem mk_coe {f : A →ₛₐ[φ] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₛₐ[φ] B) = f :=
  rfl

@[simp] lemma addHomMk_coe (f : A →ₛₐ[φ] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
theorem commutes (r : R) : f (algebraMap R A r) = algebraMap S B (φ r) := by
  simp [Algebra.algebraMap_eq_smul_one, map_smulₛₗ]

theorem comp_algebraMap : (f : A →+* B).comp (algebraMap R A) = (algebraMap S B).comp φ :=
  RingHom.ext <| f.commutes

/-- If a `RingHom : A →+* B` that factors through `algebraMap R A`, then it is an `AlgHom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R), f (algebraMap R A c) = algebraMap S B (φ c)) : A →ₛₐ[φ] B :=
  { f with
    toFun := f
    map_smul' _ _  := by simp [Algebra.smul_def, h] }

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R), f (algebraMap R A c) = algebraMap S B (φ c)) :
    ⇑(mk' f h) = f := rfl

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with map_smul' _ _ := rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

variable {T : Type*} [CommSemiring T] [Algebra T C] {ψ : S →+* T} {ρ : R →+* T}
    [RingHomCompTriple φ ψ ρ]

/-- If `φ₁` and `φ₂` are `R`-algebra homomorphisms with the
domain of `φ₁` equal to the codomain of `φ₂`, then
`φ₁.comp φ₂` is the algebra homomorphism `x ↦ φ₁ (φ₂ x)`.
-/
def comp (f : B →ₛₐ[ψ] C) (g : A →ₛₐ[φ] B) : A →ₛₐ[ρ] C where
  toRingHom := f.toRingHom.comp g
  map_smul' _ _ := by simp [Function.comp_apply, map_smulₛₗ _, RingHomCompTriple.comp_apply]

@[simp]
theorem coe_comp (f : B →ₛₐ[ψ] C) (g : A →ₛₐ[φ] B) : ⇑(f.comp g) = f ∘ g :=
  rfl

theorem comp_apply (f : B →ₛₐ[ψ] C) (g : A →ₛₐ[φ] B) (p : A) : f.comp g p = f (g p) :=
  rfl

theorem comp_toRingHom (f : B →ₛₐ[ψ] C) (g : A →ₛₐ[φ] B) :
    (f.comp g : A →+* C) = (f : B →+* C).comp ↑g :=
  rfl

@[simp]
theorem comp_id : f.comp (AlgHom.id R A) = f :=
  rfl

@[simp]
theorem id_comp : (AlgHom.id S B).comp f = f :=
  rfl

theorem comp_assoc {U : Type*} [CommSemiring U] [Algebra U D] {ν : T →+* U} {η : S →+* U} {ω : R →+* U}
    [RingHomCompTriple ψ ν η] [RingHomCompTriple ρ ν ω] [RingHomCompTriple φ η ω]
    (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] C) (h : C →ₛₐ[ν] D) :
    ((h.comp g : B →ₛₐ[η] D).comp f : A →ₛₐ[ω] D) = h.comp (g.comp f) :=
  rfl

-- instance {φ₁ : B →ₐ[R] C} {φ₂ : A →ₐ[R] B} :
--     RingHomCompTriple φ₂.toRingHom φ₁.toRingHom (φ₁.comp φ₂).toRingHom := ⟨rfl⟩

-- /-- R-Alg ⥤ R-Mod -/
-- def toLinearMap : A →ₗ[R] B where
--   toFun := φ
--   map_add' := map_add _
--   map_smul' := map_smul _

@[simp]
theorem toLinearMap_apply (p : A) : f.toLinearMap p = f p :=
  rfl

@[simp]
lemma coe_toLinearMap : ⇑f.toLinearMap = f := rfl

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₛₗ[φ] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem comp_toLinearMap (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] C) :
    (g.comp f) = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  rfl

@[simp] lemma linearMapMk_toAddHom (f : A →ₛₐ[φ] B) :
    LinearMap.mk f (map_smulₛₗ f) = f.toLinearMap :=
  rfl

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps!]
def ofLinearMap (f : A →ₛₗ[φ] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₛₐ[φ] B where
  __ := f
  map_one' := map_one
  map_mul' := map_mul
  map_zero' := by simp

@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap f.toLinearMap map_one map_mul = f :=
  rfl

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₛₗ[φ] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f :=
  rfl

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  rfl

theorem map_smul_of_tower [Algebra R B] {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R]
    {f : A →ₐ[R] B} (r : R')
    (x : A) : f (r • x) = r • f x :=
  f.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

@[simp] theorem coe_pow (φ : A →ₐ[R] A) (n : ℕ) : ⇑(φ ^ n) = φ^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]

theorem algebraMap_eq_apply (f : A →ₛₐ[φ] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap S B (φ y) = f x :=
  h ▸ (f.commutes _).symm

lemma cancel_right {g₁ g₂ : B →ₛₐ[ψ] C} {f : A →ₛₐ[φ] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

lemma cancel_left {g₁ g₂ : A →ₛₐ[φ] B} {f : B →ₛₐ[ψ] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

/-- `AlgHom.toLinearMap` as a `MonoidHom`. -/
@[simps] def toEnd : (A →ₐ[R] A) →* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end Semiring
end AlgHom

namespace AlgHomClass

@[simp]
lemma toRingHom_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    RingHomClass.toRingHom (AlgHomClass.toAlgHom f) = RingHomClass.toRingHom f := rfl

end AlgHomClass

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    map_smul' _ _ := by simp }

@[simp]
lemma toNatAlgHom_coe [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑f.toNatAlgHom = ⇑f := rfl

lemma toNatAlgHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with map_smul' _ _ := by simp }

@[simp]
lemma toIntAlgHom_coe [Ring R] [Ring S] (f : R →+* S) :
    ⇑f.toIntAlgHom = ⇑f := rfl

lemma toIntAlgHom_apply [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f.toIntAlgHom x = f x := rfl

lemma toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

end RingHom

namespace Algebra

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `AlgebraMap` as an `AlgHom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with map_smul' _ _ := by simp [Algebra.smul_def] }

variable {R}

@[simp] lemma ofId_self : ofId R R = .id R R := rfl

@[simp] lemma toRingHom_ofId : ofId R A = algebraMap R A := rfl

@[simp]
theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl

/-- This is a special case of a more general instance that we define in a later file. -/
instance subsingleton_id : Subsingleton (R →ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ ↦ by simpa using (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals created when chaining heterobasic ext lemmas. -/
@[ext high]
theorem ext_id (f g : R →ₐ[R] A) : f = g := Subsingleton.elim _ _

@[simp]
theorem comp_ofId (φ : A →ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B := by ext

section MulDistribMulAction

instance : MulDistribMulAction (A →ₐ[R] A) Aˣ where
  smul f := Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[simp]
theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

end MulDistribMulAction

variable (M : Submonoid R) {B : Type w} [Semiring B] [Algebra R B] {A}

lemma algebraMapSubmonoid_map_eq (f : A →ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes, RingHom.id_apply]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, RingHom.id_apply, and_true]
    use r

lemma algebraMapSubmonoid_le_comap (f : A →ₐ[R] B) :
    algebraMapSubmonoid A M ≤ (algebraMapSubmonoid B M).comap f.toRingHom := by
  rw [← algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribSMul.toLinearMap`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    map_smul' := by simp [Algebra.smul_def] }

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
  [Subsingleton T]

instance uniqueOfRight : Unique (S →ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ ↦ (Subsingleton.elim _ _))
  uniq _ := AlgHom.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma AlgHom.default_apply (x : S) : (default : S →ₐ[R] T) x = 0 :=
  rfl

end

-- section semialghom

-- /-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
-- an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
-- making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`). -/
-- structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
--     (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
--     extends A →ₛₗ[φ] B, RingHom A B

-- @[inherit_doc SemialgHom]
-- infixr:25 " →ₛₐ " => SemialgHom _

-- @[inherit_doc]
-- notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

-- variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
--     (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

-- instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
--   coe f := f.toFun
--   coe_injective' f g h := by
--     cases f
--     cases g
--     congr
--     exact DFunLike.coe_injective' h

-- variable {φ} {A} {B} in
-- lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
--   LinearMap.map_smul' ψ.toLinearMap m x

-- @[simp]
-- theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : A →ₛₐ[φ] B) : A → B) = f :=
--   rfl

-- end semialghom

-- section semialghomclass

-- class SemialgHomClass (F : Type*) {R S : outParam Type*}
--   [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
--   [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
--   [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

-- variable (F : Type*) {R S : Type*}
--   [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
--   [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
--   [FunLike F A B] [SemialgHomClass F φ A B]

-- instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
--   map_add ψ := ψ.map_add
--   map_smulₛₗ ψ := ψ.map_smulₛₗ
--   map_mul ψ := ψ.map_mul
--   map_one ψ := ψ.map_one
--   map_zero ψ := ψ.map_zero

-- variable {F} {φ} {A} {B} in
-- /-- Turn an element of `F` which satisfies `SemialgHomClass F φ A B` to a `SemialgHom`. -/
-- def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
--   { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

-- instance : CoeTC F (A →ₛₐ[φ] B) :=
--   ⟨SemialgHomClass.toSemialgHom⟩

-- @[simp]
-- theorem SemialgHom.coe_coe (f : F) : ⇑(f : A →ₛₐ[φ] B) = f :=
--   rfl

-- end semialghomclass

-- section semialghom

-- variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
--     {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

-- lemma SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
--     ψ (algebraMap R A r) = algebraMap S B (φ r) := by
--   have := ψ.map_smul r 1
--   rw [Algebra.smul_def, mul_one, map_one] at this
--   rw [this, Algebra.smul_def, mul_one]

-- theorem SemialgHom.toLinearMap_eq_coe (f : A →ₛₐ[φ] B) : f.toLinearMap = f :=
--   rfl

-- theorem SemialgHom.toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
--   rfl

-- theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
--     [Algebra R A] [Algebra S B] (f : A →ₛₐ[φ] B) (a : A) :
--     letI := f.toAlgebra
--     algebraMap A B a = f a := rfl

-- /-- The composition of two semi-algebra maps. -/
-- def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
--     [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
--     (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
--     A →ₛₐ[ξ] C where
--   __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
--   __ := RingHom.comp g.toRingHom f.toRingHom

-- /-- An algebra map defines a semi-algebra map using `RingHom.id` -/
-- def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
--     [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
--     A →ₛₐ[RingHom.id R] B where
--   __ := f
--   map_smul' _ _ := by simp

-- /-- The composition `(B →ₛₐ[ψ] C) ∘ (A →ₐ[S] B) → `A →ₛₐ[ψ] C` of a semi-algebra map with an
-- algebra map to give a semi-algebra map. -/
-- def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
--     [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
--     A →ₛₐ[ψ] C :=
--   g.comp f.toSemialgHom

-- -- /-- The product of two semi-algebra maps on the same domain. -/
-- -- def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : A →ₛₐ[φ] B)
-- --     (g : A →ₛₐ[φ] C) :
-- --     A →ₛₐ[φ] B × C where
-- --   __ := RingHom.prod f.toRingHom g.toRingHom
-- --   map_smul' r x := by simp

-- -- /-- The product of two semi-algebra maps on separate domains. -/
-- -- def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
-- --     [Algebra S C] [Algebra S D] [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
-- --     A × B →ₛₐ[φ] C × D :=
-- --   (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

-- /-- Restrict the scalars of semialgebra map `f : A →ₛₐ[ψ] B` where `ψ : R' →ₛₐ[φ] S'`, to
-- `φ : R →+* S`. -/
-- @[simps!]
-- def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
--     [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
--     (ψ : R' →ₛₐ[φ] S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
--     [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
--     (f : A →ₛₐ[ψ.toRingHom] B) : A →ₛₐ[φ] B where
--   __ := f.toRingHom
--   map_smul' r a := by
--     have := f.map_smul (algebraMap R R' r) a
--     simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]

-- end semialghom
