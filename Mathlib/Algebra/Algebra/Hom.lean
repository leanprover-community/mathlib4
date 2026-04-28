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

* `AlgHom φ A B`: the type of `φ`-semialgebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notation

* `A →ₛₐ[φ] B` : `φ`-semialgebra homomorphism from `A` to `B`.
* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

@[expose] public section

universe uR uS uA uB

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `AlgHom φ A B` (with notation `A →ₛₐ[φ] B`) is the ring homomorphisms
`f : A →+* B` such that `f (algebraMap R A r) = algebraMap S B (φ r)` for all `r : R`.
If `φ` is the identity map then this is the usual homomorphism in the category of `R`-algebras
(with notation `A →ₐ[R] B`). -/
structure AlgHom {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends RingHom A B where
  commutes' (r : R) : toFun (algebraMap R A r) = algebraMap S B (φ r)

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

/-- `A →ₛₐ[φ] B` is the type of `φ`-semialgebra maps from `A` to `B`. -/
infixr:25 " →ₛₐ " => AlgHom _

/-- `A →ₛₐ[φ] B` is the type of `φ`-semialgebra maps from `A` to `B`. -/
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => AlgHom φ A B

/-- `A →ₐ[R] B` is the type of `R`-algebra maps from `A` to `B`. -/
infixr:25 " →ₐ " => AlgHom (RingHom.id _)

/-- `A →ₐ[R] B` is the type of `R`-algebra maps from `A` to `B`. -/
notation:25 A " →ₐ[" R "] " B => AlgHom (RingHom.id R) A B

/-- The algebra morphism underlying `algebraMap` -/
def Algebra.algHom (R A B : Type*)
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    A →ₐ[R] B where
  toRingHom := algebraMap A B
  commutes' r := by simp [algebraMap_eq_smul_one, smul_assoc]

/-- `SemialgHomClass F R A B` asserts `F` is a type of bundled semialgebra homomorphisms
from `A` to `B`. -/
class SemialgHomClass (F : Type*) {R S : outParam Type*}
    [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [FunLike F A B] extends RingHomClass F A B where
  commutes {F φ A B} (f : F) (r : R) : f (algebraMap R A r) = algebraMap S B (φ r)

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`. -/
abbrev AlgHomClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [FunLike F A B] : Prop :=
  SemialgHomClass F (RingHom.id R) A B

protected lemma AlgHomClass.map_smul {F : Type*} {R A B : outParam Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (r : R) (x : A) : f (r • x) = r • f x := by
  simp [Algebra.smul_def, SemialgHomClass.commutes]

protected lemma AlgHomClass.commutes {F : Type*} {R A B : outParam Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (r : R) : f (algebraMap R A r) = algebraMap R B r := SemialgHomClass.commutes f r

-- For now, don't replace `AlgHom.commutes` and `AlgHomClass.commutes` with the more generic lemma.
-- The file `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean` slows down by
-- 15% if we would do so (see benchmark on PR https://github.com/leanprover-community/mathlib4/pull/18040).
-- attribute [simp] AlgHomClass.commutes

instance {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] :
    FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩
    rcases g
    congr

instance {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] :
    SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

namespace SemialgHomClass

variable (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

variable {F} {A B} {φ} (f : F)

/-- Turn an element of a type `F` satisfying `SemialgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def toAlgHom : A →ₛₐ[φ] B where
  __ := (f : A →+* B)
  commutes' := commutes f

/-- Reinterpret an element of a type of semialgebra maps as a semialgebra map. -/
instance : CoeHead F (A →ₛₐ[φ] B) where
  coe f := toAlgHom f

instance (priority := 100) semilinearMapClass : SemilinearMapClass F φ A B where
    map_smulₛₗ _ _ _ := by simp only [Algebra.smul_def, map_mul, commutes]

@[simp]
lemma toRingHom_toAlgHom {R S A B : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] {F : Type*} [FunLike F A B]
    [SemialgHomClass F φ A B] (f : F) :
    RingHomClass.toRingHom (SemialgHomClass.toAlgHom f) = RingHomClass.toRingHom f := rfl

end SemialgHomClass

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B where
    map_smulₛₗ _ _ _ := by
      simp only [Algebra.smul_def, map_mul, AlgHomClass.commutes, RingHom.id_apply]

/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B where
  __ := (f : A →+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

@[simp]
lemma toRingHom_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    RingHomClass.toRingHom (AlgHomClass.toAlgHom f) = RingHomClass.toRingHom f := rfl

end AlgHomClass

namespace AlgHom

section Semiring

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S]
variable {φ : R →+* S}
variable {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra S B]

lemma _root_.Algebra.algHom_apply (R A B : Type*) [CommSemiring R] [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (x : A) :
    Algebra.algHom R A B x = algebraMap A B x := rfl

@[simp] lemma _root_.AlgHomClass.toLinearMap_toAlgHom {R A B F : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (SemialgHomClass.toAlgHom f : A →ₗ[R] B) = f := rfl

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →ₛₐ[φ] B) : A → B := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐ[R] B) = f :=
  rfl

@[simp]
protected theorem coe_coeₛₐ {F : Type*} [FunLike F A B] [SemialgHomClass F φ A B] (f : F) :
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
theorem mk_coe {f : A →ₛₐ[φ] B} (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₛₐ[φ] B) = f :=
  rfl

@[simp] lemma addHomMk_coe (f : A →ₛₐ[φ] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
theorem commutesₛₐ (r : R) : f (algebraMap R A r) = algebraMap S B (φ r) :=
  f.commutes' r

theorem commutes [Algebra R B] (f : A →ₐ[R] B) (r : R) :
   f (algebraMap R A r) = algebraMap R B r :=
  RingHom.id_apply r ▸ f.commutesₛₐ r

theorem comp_algebraMap [Algebra R B] (f : A →ₐ[R] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| f.commutes

theorem comp_algebraMapₛₐ : (f : A →+* B).comp (algebraMap R A) = (algebraMap S B).comp φ :=
  RingHom.ext <| f.commutesₛₐ

/-- If a `RingHom : A →+* B` that factors through `algebraMap R A`, then it is an `AlgHom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = φ c • f x) : A →ₛₐ[φ] B :=
  { f with
    toFun := f
    commutes' _ := by simp [Algebra.algebraMap_eq_smul_one, h, f.map_one]}

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = φ c • f x) :
    ⇑(mk' f h) = f := rfl

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' _ := rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₛₗ[φ] B where
  toFun := f
  map_add' := map_add _
  map_smul' := map_smulₛₗ _

@[simp]
theorem toLinearMap_apply (p : A) : f.toLinearMap p = f p :=
  rfl

@[simp]
lemma coe_toLinearMap : ⇑f.toLinearMap = f := rfl

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₛₗ[φ] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  rfl

@[simp] lemma linearMapMk_toAddHom (f : A →ₛₐ[φ] B) :
    LinearMap.mk f (map_smulₛₗ f) = f.toLinearMap :=
  rfl

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₛₗ[φ] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₛₐ[φ] B where
  __ := f
  map_one' := map_one
  map_mul' := map_mul
  map_zero' := by simp
  commutes' := by simp [Algebra.algebraMap_eq_smul_one, map_one, map_smulₛₗ]

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

variable (R) in
theorem map_smul_of_tower [Algebra R B] {R'} [SMul R' A] [SMul R' B]
    [LinearMap.CompatibleSMul A B R' R] {f : A →ₐ[R] B} (r : R') (x : A) : f (r • x) = r • f x :=
  f.toLinearMap.map_smul_of_tower r x

section comp

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} {R₄ : Type u₄}
variable [CommSemiring R₁] [CommSemiring R₂] [CommSemiring R₃] [CommSemiring R₄]
variable {A₁ : Type v₁} {A₂ : Type v₂} {A₃ : Type v₃} {A₄ : Type v₄}
variable [Semiring A₁] [Semiring A₂] [Semiring A₃] [Semiring A₄]
variable [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃] [Algebra R₄ A₄]
variable {φ₁₂ : R₁ →+* R₂} {φ₂₃ : R₂ →+* R₃} {φ₁₃ : R₁ →+* R₃}
variable {φ₁₄ : R₁ →+* R₄} {φ₂₄ : R₂ →+* R₄} {φ₃₄ : R₃ →+* R₄}
variable [RingHomCompTriple φ₁₂ φ₂₃ φ₁₃] [RingHomCompTriple φ₁₂ φ₂₄ φ₁₄]
variable [RingHomCompTriple φ₂₃ φ₃₄ φ₂₄] [RingHomCompTriple φ₁₃ φ₃₄ φ₁₄]
variable (g : A₂ →ₛₐ[φ₂₃] A₃) (f : A₁ →ₛₐ[φ₁₂] A₂) (h : A₃ →ₛₐ[φ₃₄] A₄)

/-- If `φ₁` and `φ₂` are `R`-algebra homomorphisms with the
domain of `φ₁` equal to the codomain of `φ₂`, then
`φ₁.comp φ₂` is the algebra homomorphism `x ↦ φ₁ (φ₂ x)`.
-/
def comp : A₁ →ₛₐ[φ₁₃] A₃ where
  toRingHom := g.toRingHom.comp f
  commutes' _ := by simp [Function.comp_apply, RingHomCompTriple.comp_apply]

@[simp] theorem coe_comp : ⇑(g.comp f) = g ∘ f := rfl
theorem comp_apply (p : A₁) : g.comp f p = g (f p) := rfl
theorem comp_toRingHom : (g.comp f : A₁ →+* A₃) = (g : A₂ →+* A₃).comp ↑f := rfl
@[simp] theorem comp_id : f.comp (AlgHom.id R₁ A₁) = f := rfl
@[simp] theorem id_comp : (AlgHom.id R₂ A₂).comp f = f := rfl
theorem comp_assoc (f : A₁ →ₛₐ[φ₁₂] A₂) (g : A₂ →ₛₐ[φ₂₃] A₃) (h : A₃ →ₛₐ[φ₃₄] A₄) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

instance {f₁ : A₂ →ₛₐ[φ₂₃] A₃} {f₂ : A₁ →ₛₐ[φ₁₂] A₂} :
    RingHomCompTriple f₂.toRingHom f₁.toRingHom (f₁.comp f₂).toRingHom := ⟨rfl⟩

lemma cancel_right {g₁ g₂ : A₂ →ₛₐ[φ₂₃] A₃} {f : A₁ →ₛₐ[φ₁₂] A₂} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

lemma cancel_left {g₁ g₂ : A₁ →ₛₐ[φ₁₂] A₂} {f : A₂ →ₛₐ[φ₂₃] A₃} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

@[simp]
theorem comp_toLinearMap :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

end comp

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

theorem algebraMap_eq_applyₛₐ (f : A →ₛₐ[φ] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap S B (φ y) = f x :=
  h ▸ (f.commutesₛₐ _).symm


theorem algebraMap_eq_apply [Algebra R B] (f : A →ₐ[R] B) {y : R} {x : A}
    (h : algebraMap R A y = x) : algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm

/-- `AlgHom.toLinearMap` as a `MonoidHom`. -/
@[simps] def toEnd : (A →ₐ[R] A) →* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end Semiring
end AlgHom

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' _ := by simp }

@[simp]
lemma toNatAlgHom_coe [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑f.toNatAlgHom = ⇑f := rfl

lemma toNatAlgHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' _ := by simp }

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

variable (R : Type uR) (A : Type uA) (B : Type uB)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `AlgebraMap` as an `AlgHom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' _ := by simp }

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

variable (M : Submonoid R) {B : Type uB} [Semiring B] [Algebra R B] {A}

lemma algebraMapSubmonoid_map_eq (f : A →ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
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
    commutes' := smul_algebraMap _ }

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
