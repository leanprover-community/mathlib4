/-
Copyright (c) 2026 Kevin Buzzard, Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.Hom

/-!
# Semialgebra homomorphisms

Let `φ : R →+* S` be a homomorphism of commutative semirings, let `A` be an `R`-algebra and let
`B` be an `S`-algebra. A *`φ`-semialgebra homomorphism* from `A` to `B` is a ring homomorphism
`f : A →+* B` lying over `φ`, in the sense that
`f (algebraMap R A r) = algebraMap S B (φ r)` for all `r : R`; equivalently
`f (r • a) = φ r • f a` for all `r : R` and `a : A`.

This is the algebra analogue of semilinear maps. Unlike `LinearMap`, however,
`AlgHom` is *not* defined as the special case `φ = RingHom.id R` of `SemialgHom`.
Refactoring `AlgHom` to be a special case of `SemialgHom` leads to performance
degradation.

## Main definitions

* `SemialgHom φ A B`, with notation `A →ₛₐ[φ] B`: the type of `φ`-semialgebra homomorphisms
  from `A` to `B`.
* `SemialgHomClass F φ A B`: the class of types of `φ`-semialgebra homomorphisms.
* `AlgHom.toSemialgHom`, `SemialgHom.toAlgHom` and `AlgHom.semialgHomEquiv`: the transfer
  between `A →ₐ[R] B` and `A →ₛₐ[RingHom.id R] B`.
* `SemialgHom.toAlgHomCompHom`: a `φ`-semialgebra homomorphism `A →ₛₐ[φ] B` regarded as an
  `R`-algebra homomorphism, where `B` is made into an `R`-algebra along `φ`.

## Notation

* `A →ₛₐ[φ] B` : `φ`-semialgebra homomorphism from `A` to `B`.
-/

@[expose] public section

universe uR uS uT uA uB uC

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be an
`S`-algebra. Then `SemialgHom φ A B`, denoted `A →ₛₐ[φ] B`, is the type of ring homomorphisms
`f : A →+* B` lying over `φ`, i.e. such that `f (algebraMap R A r) = algebraMap S B (φ r)`. -/
structure SemialgHom {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends RingHom A B where
  /-- A semialgebra homomorphism lies over `φ`. -/
  commutes' (r : R) : toFun (algebraMap R A r) = algebraMap S B (φ r)

/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

/-- `SemialgHomClass F φ A B` asserts that `F` is a type of bundled `φ`-semialgebra
homomorphisms from `A` to `B`. -/
class SemialgHomClass (F : Type*) {R S : outParam Type*} [CommSemiring R] [CommSemiring S]
    (φ : outParam (R →+* S)) (A B : outParam Type*) [Semiring A] [Semiring B]
    [Algebra R A] [Algebra S B] [FunLike F A B] : Prop extends RingHomClass F A B where
  /-- A semialgebra homomorphism lies over `φ`. -/
  commutes (f : F) (r : R) : f (algebraMap R A r) = algebraMap S B (φ r)

-- Lowered so that `RingHomClass (A →ₐ[R] B) A B` still resolves through `AlgHom.algHomClass`
-- rather than detouring via `AlgHomClass.toSemialgHomClass` below.
attribute [instance 90] SemialgHomClass.toRingHomClass

namespace SemialgHomClass

variable {F : Type*} {R S A B : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [FunLike F A B]

section

variable [SemialgHomClass F φ A B]

instance (priority := 100) semilinearMapClass : SemilinearMapClass F φ A B where
  map_smulₛₗ _ _ _ := by simp only [Algebra.smul_def, map_mul, SemialgHomClass.commutes]

/-- Turn an element of a type `F` satisfying `SemialgHomClass F φ A B` into an actual
`SemialgHom`. This is declared as the default coercion from `F` to `A →ₛₐ[φ] B`. -/
@[coe]
def toSemialgHom (f : F) : A →ₛₐ[φ] B where
  __ := (f : A →+* B)
  commutes' := commutes f

end

/-- Every `AlgHomClass` is a `SemialgHomClass` for the identity ring homomorphism. -/
instance (priority := 100) _root_.AlgHomClass.toSemialgHomClass {F R A B : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B] :
    SemialgHomClass F (RingHom.id R) A B where
  commutes f r := AlgHomClass.commutes f r

end SemialgHomClass

namespace SemialgHom

section Semiring

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
variable {A : Type uA} {B : Type uB} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance funLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩; congr

instance semialgHomClass : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →ₛₐ[φ] B) : A → B := f

initialize_simps_projections SemialgHom (toFun → apply)

@[simp]
lemma _root_.SemialgHomClass.toLinearMap_toSemialgHom {F : Type*} [FunLike F A B]
    [SemialgHomClass F φ A B] (f : F) :
    (SemialgHomClass.toSemialgHom f : A →ₛₗ[φ] B) = f :=
  rfl

@[simp]
lemma _root_.SemialgHomClass.toRingHom_toSemialgHom {F : Type*} [FunLike F A B]
    [SemialgHomClass F φ A B] (f : F) :
    RingHomClass.toRingHom (SemialgHomClass.toSemialgHom f : A →ₛₐ[φ] B) =
      RingHomClass.toRingHom f :=
  rfl

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [SemialgHomClass F φ A B] (f : F) :
    ⇑(SemialgHomClass.toSemialgHom f : A →ₛₐ[φ] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →ₛₐ[φ] B) : f.toFun = f :=
  rfl

/-- Turn a semialgebra homomorphism into the corresponding multiplicative monoid
homomorphism. -/
@[coe]
def toMonoidHom' (f : A →ₛₐ[φ] B) : A →* B := (f : A →+* B)

instance coeOutMonoidHom : CoeOut (A →ₛₐ[φ] B) (A →* B) :=
  ⟨SemialgHom.toMonoidHom'⟩

/-- Turn a semialgebra homomorphism into the corresponding additive monoid homomorphism. -/
@[coe]
def toAddMonoidHom' (f : A →ₛₐ[φ] B) : A →+ B := (f : A →+* B)

instance coeOutAddMonoidHom : CoeOut (A →ₛₐ[φ] B) (A →+ B) :=
  ⟨SemialgHom.toAddMonoidHom'⟩

@[simp]
theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) :
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

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₛₐ[φ] B) → A →+* B) :=
  fun f₁ f₂ H ↦ coe_fn_injective <|
    show ((f₁ : A →+* B) : A → B) = ((f₂ : A →+* B) : A → B) from congr_arg _ H

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
theorem commutes (r : R) : f (algebraMap R A r) = algebraMap S B (φ r) :=
  f.commutes' r

theorem comp_algebraMap : (f : A →+* B).comp (algebraMap R A) = (algebraMap S B).comp φ :=
  RingHom.ext f.commutes

theorem algebraMap_eq_apply {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap S B (φ y) = f x :=
  h ▸ (f.commutes _).symm

/-- If a `RingHom` `f : A →+* B` satisfies `f (r • a) = φ r • f a`, then it is a
`φ`-semialgebra homomorphism. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = φ c • f x) : A →ₛₐ[φ] B where
  __ := f
  commutes' _ := by simp [Algebra.algebraMap_eq_smul_one, h, f.map_one]

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = φ c • f x) : ⇑(mk' f h) = f :=
  rfl

@[simp, norm_cast]
theorem toRingHom_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = φ c • f x) :
    ((mk' f h : A →ₛₐ[φ] B) : A →+* B) = f :=
  rfl

section id

variable (R A)

/-- Identity map as a `SemialgHom`. -/
protected def id : A →ₛₐ[RingHom.id R] A where
  __ := RingHom.id A
  commutes' _ := rfl

@[simp, norm_cast]
theorem coe_id : ⇑(SemialgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toRingHom : (SemialgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

variable {R A}

@[simp]
theorem id_apply (p : A) : SemialgHom.id R A p = p :=
  rfl

end id

section toLinearMap

/-- A `φ`-semialgebra homomorphism is in particular a `φ`-semilinear map. -/
def toLinearMap (f : A →ₛₐ[φ] B) : A →ₛₗ[φ] B where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

@[simp]
theorem toLinearMap_apply (p : A) : f.toLinearMap p = f p :=
  rfl

@[simp]
lemma coe_toLinearMap : ⇑f.toLinearMap = f := rfl

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : (A →ₛₐ[φ] B) → A →ₛₗ[φ] B) := fun _f _g h ↦
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (SemialgHom.id R A) = LinearMap.id :=
  rfl

@[simp] lemma linearMapMk_toAddHom (f : A →ₛₐ[φ] B) :
    LinearMap.mk f (map_smulₛₗ f) = f.toLinearMap := rfl

/-- Promote a `φ`-semilinear map which is multiplicative and unital to a `φ`-semialgebra
homomorphism. -/
def ofLinearMap (f : A →ₛₗ[φ] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₛₐ[φ] B where
  toFun := f
  map_one' := map_one
  map_mul' := map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, map_one]

@[simp]
theorem coe_ofLinearMap (f : A →ₛₗ[φ] B) (map_one) (map_mul) :
    ⇑(ofLinearMap f map_one map_mul) = f :=
  rfl

@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap f.toLinearMap map_one map_mul = f := by
  ext
  rfl

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₛₗ[φ] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by
  ext
  rfl

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = SemialgHom.id R A :=
  ext fun _ ↦ rfl

end toLinearMap

end Semiring

section comp

variable {R : Type uR} {S : Type uS} {T : Type uT} [CommSemiring R] [CommSemiring S]
  [CommSemiring T]
variable {A : Type uA} {B : Type uB} {C : Type uC} [Semiring A] [Semiring B] [Semiring C]
variable [Algebra R A] [Algebra S B] [Algebra T C]
variable {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T}

section
variable [RingHomCompTriple φ ψ χ] (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B)

/-- Composition of semialgebra homomorphisms. -/
def comp : A →ₛₐ[χ] C where
  __ := (g : B →+* C).comp (f : A →+* B)
  commutes' r := by simp [RingHomCompTriple.comp_apply]

@[simp] theorem coe_comp : ⇑(g.comp f) = g ∘ f := rfl

theorem comp_apply (p : A) : g.comp f p = g (f p) := rfl

theorem comp_toRingHom : (g.comp f : A →+* C) = (g : B →+* C).comp (f : A →+* B) := rfl

@[simp]
theorem comp_toLinearMap : (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

end

@[simp] theorem comp_id (f : A →ₛₐ[φ] B) : f.comp (SemialgHom.id R A) = f := rfl

@[simp] theorem id_comp (f : A →ₛₐ[φ] B) : (SemialgHom.id S B).comp f = f := rfl

theorem comp_assoc {R₄ : Type*} [CommSemiring R₄] {A₄ : Type*} [Semiring A₄] [Algebra R₄ A₄]
    {ω : T →+* R₄} {χ₂₄ : S →+* R₄} {χ₁₄ : R →+* R₄}
    [RingHomCompTriple φ ψ χ] [RingHomCompTriple ψ ω χ₂₄] [RingHomCompTriple χ ω χ₁₄]
    [RingHomCompTriple φ χ₂₄ χ₁₄]
    (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] C) (h : C →ₛₐ[ω] A₄) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

variable [RingHomCompTriple φ ψ χ]

instance {g : B →ₛₐ[ψ] C} {f : A →ₛₐ[φ] B} :
    RingHomCompTriple (f : A →+* B) (g : B →+* C) ((g.comp f : A →ₛₐ[χ] C) : A →+* C) :=
  ⟨rfl⟩

theorem cancel_right {g₁ g₂ : B →ₛₐ[ψ] C} {f : A →ₛₐ[φ] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 (SemialgHom.ext_iff.1 h), fun h ↦ h ▸ rfl⟩

theorem cancel_left {g₁ g₂ : A →ₛₐ[φ] B} {f : B →ₛₐ[ψ] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext fun a ↦ hf (SemialgHom.congr_fun h a), fun h ↦ h ▸ rfl⟩

end comp

end SemialgHom

section transfer

variable {R : Type uR} [CommSemiring R] {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An `R`-algebra homomorphism is the same thing as a `RingHom.id R`-semialgebra
homomorphism. -/
def AlgHom.toSemialgHom (f : A →ₐ[R] B) : A →ₛₐ[RingHom.id R] B where
  __ := (f : A →+* B)
  commutes' := f.commutes'

/-- A `RingHom.id R`-semialgebra homomorphism is the same thing as an `R`-algebra homomorphism. -/
def SemialgHom.toAlgHom (f : A →ₛₐ[RingHom.id R] B) : A →ₐ[R] B where
  __ := (f : A →+* B)
  commutes' := f.commutes'

@[simp]
theorem AlgHom.coe_toSemialgHom (f : A →ₐ[R] B) : ⇑f.toSemialgHom = f := rfl

@[simp]
theorem AlgHom.toRingHom_toSemialgHom (f : A →ₐ[R] B) :
    (f.toSemialgHom : A →+* B) = (f : A →+* B) := rfl

@[simp]
theorem SemialgHom.coe_toAlgHom (f : A →ₛₐ[RingHom.id R] B) : ⇑f.toAlgHom = f := rfl

@[simp]
theorem SemialgHom.toRingHom_toAlgHom (f : A →ₛₐ[RingHom.id R] B) :
    (f.toAlgHom : A →+* B) = (f : A →+* B) := rfl

@[simp]
theorem SemialgHom.toAlgHom_toSemialgHom (f : A →ₐ[R] B) : f.toSemialgHom.toAlgHom = f := rfl

@[simp]
theorem AlgHom.toSemialgHom_toAlgHom (f : A →ₛₐ[RingHom.id R] B) :
    f.toAlgHom.toSemialgHom = f := rfl

variable (R A B) in
/-- `R`-algebra homomorphisms are the same thing as `RingHom.id R`-semialgebra
homomorphisms. -/
@[simps]
def AlgHom.semialgHomEquiv : (A →ₐ[R] B) ≃ (A →ₛₐ[RingHom.id R] B) where
  toFun f := f.toSemialgHom
  invFun f := f.toAlgHom

@[simp]
theorem AlgHom.toSemialgHom_id : (AlgHom.id R A).toSemialgHom = SemialgHom.id R A := rfl

@[simp]
theorem SemialgHom.toAlgHom_id : (SemialgHom.id R A).toAlgHom = AlgHom.id R A := rfl

theorem AlgHom.toSemialgHom_injective :
    Function.Injective (AlgHom.toSemialgHom : (A →ₐ[R] B) → A →ₛₐ[RingHom.id R] B) :=
  fun _ _ h ↦ AlgHom.ext fun x ↦ SemialgHom.congr_fun h x

theorem SemialgHom.toAlgHom_injective :
    Function.Injective (SemialgHom.toAlgHom : (A →ₛₐ[RingHom.id R] B) → A →ₐ[R] B) :=
  fun _ _ h ↦ SemialgHom.ext fun x ↦ AlgHom.congr_fun h x

@[simp]
theorem AlgHom.toSemialgHom_toLinearMap (f : A →ₐ[R] B) :
    f.toSemialgHom.toLinearMap = f.toLinearMap :=
  rfl

@[simp]
theorem SemialgHom.toAlgHom_toLinearMap (f : A →ₛₐ[RingHom.id R] B) :
    f.toAlgHom.toLinearMap = f.toLinearMap :=
  rfl

variable {C : Type*} [Semiring C] [Algebra R C]

@[simp]
theorem AlgHom.toSemialgHom_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (f.comp g).toSemialgHom = f.toSemialgHom.comp g.toSemialgHom :=
  rfl

@[simp]
theorem SemialgHom.toAlgHom_comp (f : B →ₛₐ[RingHom.id R] C) (g : A →ₛₐ[RingHom.id R] B) :
    (f.comp g).toAlgHom = f.toAlgHom.comp g.toAlgHom :=
  rfl

end transfer

namespace SemialgHom

section compAlgHom

variable {R : Type uR} {S : Type uS} {T : Type uT} [CommSemiring R] [CommSemiring S]
  [CommSemiring T]
variable {A : Type uA} {B : Type uB} {C : Type uC} [Semiring A] [Semiring B] [Semiring C]

/-- Compose a semialgebra homomorphism with an algebra homomorphism on the right. -/
def compAlgHom [Algebra R A] [Algebra R B] [Algebra S C] {φ : R →+* S}
    (g : B →ₛₐ[φ] C) (f : A →ₐ[R] B) : A →ₛₐ[φ] C :=
  g.comp f.toSemialgHom

@[simp]
theorem coe_compAlgHom [Algebra R A] [Algebra R B] [Algebra S C] {φ : R →+* S}
    (g : B →ₛₐ[φ] C) (f : A →ₐ[R] B) : ⇑(g.compAlgHom f) = g ∘ f := rfl

theorem compAlgHom_apply [Algebra R A] [Algebra R B] [Algebra S C] {φ : R →+* S}
    (g : B →ₛₐ[φ] C) (f : A →ₐ[R] B) (a : A) : g.compAlgHom f a = g (f a) := rfl

/-- Compose an algebra homomorphism with a semialgebra homomorphism on the right. -/
def _root_.AlgHom.compSemialgHom [Algebra R A] [Algebra S B] [Algebra S C] {φ : R →+* S}
    (g : B →ₐ[S] C) (f : A →ₛₐ[φ] B) : A →ₛₐ[φ] C :=
  g.toSemialgHom.comp f

@[simp]
theorem _root_.AlgHom.coe_compSemialgHom [Algebra R A] [Algebra S B] [Algebra S C] {φ : R →+* S}
    (g : B →ₐ[S] C) (f : A →ₛₐ[φ] B) : ⇑(g.compSemialgHom f) = g ∘ f := rfl

theorem _root_.AlgHom.compSemialgHom_apply [Algebra R A] [Algebra S B] [Algebra S C]
    {φ : R →+* S} (g : B →ₐ[S] C) (f : A →ₛₐ[φ] B) (a : A) :
    g.compSemialgHom f a = g (f a) := rfl

end compAlgHom

section compHom

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
variable {A : Type uA} {B : Type uB} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

/-- A `φ`-semialgebra homomorphism `A →ₛₐ[φ] B` is the same thing as an `R`-algebra
homomorphism `A →ₐ[R] B`, where `B` is regarded as an `R`-algebra along `φ`. -/
def toAlgHomCompHom (f : A →ₛₐ[φ] B) :
    let := Algebra.compHom B φ
    A →ₐ[R] B :=
  let := Algebra.compHom B φ
  { __ := (f : A →+* B)
    commutes' := f.commutes' }

/-- An `R`-algebra homomorphism `A →ₐ[R] B`, where `B` is regarded as an `R`-algebra along `φ`,
is the same thing as a `φ`-semialgebra homomorphism `A →ₛₐ[φ] B`. -/
def ofAlgHomCompHom (f : letI := Algebra.compHom B φ; A →ₐ[R] B) : A →ₛₐ[φ] B :=
  let := Algebra.compHom B φ
  { __ := (f : A →+* B)
    commutes' := f.commutes' }

@[simp]
theorem coe_toAlgHomCompHom (f : A →ₛₐ[φ] B) : ⇑f.toAlgHomCompHom = f := rfl

@[simp]
theorem coe_ofAlgHomCompHom (f : let := Algebra.compHom B φ; A →ₐ[R] B) :
    ⇑(ofAlgHomCompHom f) = f := rfl

variable (φ A B) in
/-- `φ`-semialgebra homomorphisms `A →ₛₐ[φ] B` are the same thing as `R`-algebra homomorphisms
`A →ₐ[R] B`, where `B` is regarded as an `R`-algebra along `φ`. -/
@[simps]
def algHomCompHomEquiv :
    (A →ₛₐ[φ] B) ≃ (let := Algebra.compHom B φ; A →ₐ[R] B) where
  toFun f := f.toAlgHomCompHom
  invFun f := ofAlgHomCompHom f

end compHom

section restrictScalars

/-- Restrict the scalars of a semialgebra homomorphism `f : A →ₛₐ[ψ] B` along `φ : R →+* S`,
given that `ψ : R' →+* S'` lies over `φ`. -/
@[simps!]
def restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring R']
    [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S} {ψ : R' →+* S'}
    (h : ∀ r : R, ψ (algebraMap R R' r) = algebraMap S S' (φ r))
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [Algebra R' A]
    [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B] (f : A →ₛₐ[ψ] B) :
    A →ₛₐ[φ] B where
  __ := (f : A →+* B)
  commutes' r := by
    have hA : algebraMap R A r = algebraMap R' A (algebraMap R R' r) := by
      simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    have hB : ∀ s : S, algebraMap S B s = algebraMap S' B (algebraMap S S' s) := fun s ↦ by
      simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [hB, ← h]
    exact hA ▸ f.commutes (algebraMap R R' r)

end restrictScalars

section toAlgebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra S B]

/-- A semialgebra homomorphism `f : A →ₛₐ[φ] B` makes `B` into an `A`-algebra, and the resulting
`algebraMap A B` is `f` itself. -/
theorem algebraMap_apply (f : A →ₛₐ[φ] B) (a : A) :
    let := (f : A →+* B).toAlgebra
    algebraMap A B a = f a :=
  rfl

end toAlgebra

section Subsingleton

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [Subsingleton B]

instance uniqueOfRight : Unique (A →ₛₐ[φ] B) where
  default := ofLinearMap 0 (Subsingleton.elim _ _) fun _ _ ↦ Subsingleton.elim _ _
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma default_apply (x : A) : (default : A →ₛₐ[φ] B) x = 0 :=
  rfl

end Subsingleton

end SemialgHom
