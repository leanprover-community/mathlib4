/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Algebra.Hom

#align_import algebra.hom.non_unital_alg from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `Mul` instead of `Group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `NonUnitalAlgHom`.

TODO: add `NonUnitalAlgEquiv` when needed.

## Main definitions

  * `NonUnitalAlgHom`
  * `AlgHom.toNonUnitalAlgHom`

## Tags

non-unital, algebra, morphism
-/

universe u u₁ v w w₁ w₂ w₃

variable {R : Type u} {S : Type u₁}

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B

#align non_unital_alg_hom NonUnitalAlgHom

@[inherit_doc NonUnitalAlgHom]
infixr:25 " →ₙₐ " => NonUnitalAlgHom _

@[inherit_doc]
notation:25 A " →ₛₙₐ[" φ "] " B => NonUnitalAlgHom φ A B

@[inherit_doc]
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom (MonoidHom.id R) A B

attribute [nolint docBlame] NonUnitalAlgHom.toMulHom

/-- `NonUnitalAlgSemiHomClass F φ A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are equivariant with respect to `φ`.  -/
class NonUnitalAlgSemiHomClass (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
    (φ : outParam (R →* S)) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction S B] [FunLike F A B]
    extends DistribMulActionSemiHomClass F φ A B, MulHomClass F A B : Prop
#align non_unital_alg_hom_class NonUnitalAlgSemiHomClass

/-- `NonUnitalAlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are `R`-linear.

  This is an abbreviation to `NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B` -/
abbrev NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*)
    [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] :=
  NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

-- Porting note: commented out, not dangerous
-- attribute [nolint dangerousInstance] NonUnitalAlgHomClass.toMulHomClass

namespace NonUnitalAlgHomClass

-- Porting note: Made following instance non-dangerous through [...] -> [...] replacement
-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass
  {F R S A B : Type*} {_ : Monoid R} {_ : Monoid S} {φ : outParam (R →* S)}
    {_ : NonUnitalNonAssocSemiring A} [DistribMulAction R A]
    {_ : NonUnitalNonAssocSemiring B} [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with }
#align non_unital_alg_hom_class.non_unital_alg_hom_class.to_non_unital_ring_hom_class NonUnitalAlgHomClass.toNonUnitalRingHomClass

variable [Semiring R] [Semiring S] {φ : R →+* S}
  {A B : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module S B]

-- see Note [lower instance priority]
instance (priority := 100) {F R S A B : Type*}
    {_ : Semiring R} {_ : Semiring S} {φ : R →+* S}
    {_ : NonUnitalSemiring A} {_ : NonUnitalSemiring B} [Module R A] [Module S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass (R := R) (S := S) F φ A B] :
    SemilinearMapClass F φ A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with map_smulₛₗ := map_smulₛₗ }

instance (priority := 100) {F : Type*} [FunLike F A B] [Module R B] [NonUnitalAlgHomClass F R A B] :
    LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smulₛₗ }

/-- Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[φ] B`. -/
@[coe]
def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R →* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A →ₛₙₐ[φ] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A →ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[R] B`. -/
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

-- Porting note: Replaced with DFunLike instance
-- /-- see Note [function coercion] -/
-- instance : CoeFun (A →ₙₐ[R] B) fun _ => A → B :=
--   ⟨toFun⟩

instance  : DFunLike (A →ₛₙₐ[φ] B) A fun _ => B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]
theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f :=
  rfl
#align non_unital_alg_hom.to_fun_eq_coe NonUnitalAlgHom.toFun_eq_coe

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →ₛₙₐ[φ] B) : A → B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)

variable {φ A B C}
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f :=
  rfl
#align non_unital_alg_hom.coe_coe NonUnitalAlgHom.coe_coe

theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

#align non_unital_alg_hom.coe_injective NonUnitalAlgHom.coe_injective
instance : FunLike (A →ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' := coe_injective

instance : NonUnitalAlgSemiHomClass (A →ₛₙₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[ext]
theorem ext {f g : A →ₛₙₐ[φ] B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align non_unital_alg_hom.ext NonUnitalAlgHom.ext

theorem ext_iff {f g : A →ₛₙₐ[φ] B} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    rfl, ext⟩
#align non_unital_alg_hom.ext_iff NonUnitalAlgHom.ext_iff

theorem congr_fun {f g : A →ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl
#align non_unital_alg_hom.congr_fun NonUnitalAlgHom.congr_fun

@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f :=
  rfl
#align non_unital_alg_hom.coe_mk NonUnitalAlgHom.coe_mk

@[simp]
theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  rfl
#align non_unital_alg_hom.mk_coe NonUnitalAlgHom.mk_coe

instance : CoeOut (A →ₛₙₐ[φ] B) (A →ₑ+[φ] B) :=
  ⟨toDistribMulActionHom⟩

instance : CoeOut (A →ₛₙₐ[φ] B) (A →ₙ* B) :=
  ⟨toMulHom⟩

@[simp]
theorem toDistribMulActionHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toDistribMulActionHom = ↑f :=
  rfl
#align non_unital_alg_hom.to_distrib_mul_action_hom_eq_coe NonUnitalAlgHom.toDistribMulActionHom_eq_coe

@[simp]
theorem toMulHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toMulHom = ↑f :=
  rfl
#align non_unital_alg_hom.to_mul_hom_eq_coe NonUnitalAlgHom.toMulHom_eq_coe

@[simp, norm_cast]
theorem coe_to_distribMulActionHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₑ+[φ] B) = f :=
  rfl
#align non_unital_alg_hom.coe_to_distrib_mul_action_hom NonUnitalAlgHom.coe_to_distribMulActionHom

@[simp, norm_cast]
theorem coe_to_mulHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₙ* B) = f :=
  rfl
#align non_unital_alg_hom.coe_to_mul_hom NonUnitalAlgHom.coe_to_mulHom

theorem to_distribMulActionHom_injective {f g : A →ₛₙₐ[φ] B}
    (h : (f : A →ₑ+[φ] B) = (g : A →ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a
#align non_unital_alg_hom.to_distrib_mul_action_hom_injective NonUnitalAlgHom.to_distribMulActionHom_injective

theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a
#align non_unital_alg_hom.to_mul_hom_injective NonUnitalAlgHom.to_mulHom_injective

@[norm_cast]
theorem coe_distribMulActionHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  rfl
#align non_unital_alg_hom.coe_distrib_mul_action_hom_mk NonUnitalAlgHom.coe_distribMulActionHom_mk

@[norm_cast]
theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  rfl
#align non_unital_alg_hom.coe_mul_hom_mk NonUnitalAlgHom.coe_mulHom_mk

-- @[simp] -- Porting note (#10618) : simp can prove this
protected theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x :=
  map_smulₛₗ _ _ _
#align non_unital_alg_hom.map_smul NonUnitalAlgHom.map_smul

-- @[simp] -- Porting note (#10618) : simp can prove this
protected theorem map_add (f : A →ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _
#align non_unital_alg_hom.map_add NonUnitalAlgHom.map_add

-- @[simp] -- Porting note (#10618) : simp can prove this
protected theorem map_mul (f : A →ₛₙₐ[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _
#align non_unital_alg_hom.map_mul NonUnitalAlgHom.map_mul

-- @[simp] -- Porting note (#10618) : simp can prove this
protected theorem map_zero (f : A →ₛₙₐ[φ] B) : f 0 = 0 :=
  map_zero _
#align non_unital_alg_hom.map_zero NonUnitalAlgHom.map_zero

/-- The identity map as a `NonUnitalAlgHom`. -/
protected def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp]
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl

instance : Zero (A →ₛₙₐ[φ] B) :=
  ⟨{ (0 : A →ₑ+[φ] B) with map_mul' := by simp }⟩

instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[simp]
theorem coe_zero : ⇑(0 : A →ₛₙₐ[φ] B) = 0 :=
  rfl
#align non_unital_alg_hom.coe_zero NonUnitalAlgHom.coe_zero

@[simp]
theorem coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id :=
  rfl
#align non_unital_alg_hom.coe_one NonUnitalAlgHom.coe_one

theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 :=
  rfl
#align non_unital_alg_hom.zero_apply NonUnitalAlgHom.zero_apply

theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
  rfl
#align non_unital_alg_hom.one_apply NonUnitalAlgHom.one_apply

instance : Inhabited (A →ₛₙₐ[φ] B) :=
  ⟨0⟩

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ]:
    A →ₛₙₐ[χ] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →ₑ+[ψ] C).comp (g : A →ₑ+[φ] B) with }
#align non_unital_alg_hom.comp NonUnitalAlgHom.comp

@[simp, norm_cast]
theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := rfl
#align non_unital_alg_hom.coe_comp NonUnitalAlgHom.coe_comp

theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := rfl
#align non_unital_alg_hom.comp_apply NonUnitalAlgHom.comp_apply

variable {B₁: Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →ₙₐ[R] A :=
  { (f : A →ₙ* B₁).inverse g h₁ h₂, (f : A →+[R] B₁).inverse g h₁ h₂ with }
#align non_unital_alg_hom.inverse NonUnitalAlgHom.inverse

@[simp]
theorem coe_inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ → A) = g :=
  rfl
#align non_unital_alg_hom.coe_inverse NonUnitalAlgHom.coe_inverse

/-- The inverse of a bijective morphism is a morphism. -/
def inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₛₙₐ[φ'] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero, h₁]
    map_add' := fun x y ↦ by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x, ← h₂ y, ← map_add, h₁, h₂, h₂] }

@[simp]
theorem coe_inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B → A) = g :=
  rfl

/-! ### Operations on the product type

Note that much of this is copied from [`LinearAlgebra/Prod`](../../LinearAlgebra/Prod). -/


section Prod

variable (R A B)
variable  [DistribMulAction R B]

/-- The first projection of a product is a non-unital alg_hom. -/
@[simps]
def fst : A × B →ₙₐ[R] A where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
#align non_unital_alg_hom.fst NonUnitalAlgHom.fst

/-- The second projection of a product is a non-unital alg_hom. -/
@[simps]
def snd : A × B →ₙₐ[R] B where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
#align non_unital_alg_hom.snd NonUnitalAlgHom.snd

variable {R A B}
variable [DistribMulAction R C]

/-- The prod of two morphisms is a morphism. -/
@[simps]
def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C where
  toFun := Pi.prod f g
  map_zero' := by simp only [Pi.prod, Prod.zero_eq_mk, map_zero]
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Pi.prod, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Pi.prod, map_smul, MonoidHom.id_apply, id_eq, Prod.smul_mk]
#align non_unital_alg_hom.prod NonUnitalAlgHom.prod

theorem coe_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align non_unital_alg_hom.coe_prod NonUnitalAlgHom.coe_prod

@[simp]
theorem fst_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  rfl
#align non_unital_alg_hom.fst_prod NonUnitalAlgHom.fst_prod

@[simp]
theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl
#align non_unital_alg_hom.snd_prod NonUnitalAlgHom.snd_prod

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  coe_injective Pi.prod_fst_snd
#align non_unital_alg_hom.prod_fst_snd NonUnitalAlgHom.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₙₐ[R] B) × (A →ₙₐ[R] C) ≃ (A →ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv _ := rfl
  right_inv _ := rfl
#align non_unital_alg_hom.prod_equiv NonUnitalAlgHom.prodEquiv

variable (R A B)

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →ₙₐ[R] A × B :=
  prod 1 0
#align non_unital_alg_hom.inl NonUnitalAlgHom.inl

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →ₙₐ[R] A × B :=
  prod 0 1
#align non_unital_alg_hom.inr NonUnitalAlgHom.inr

variable {R A B}

@[simp]
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl
#align non_unital_alg_hom.coe_inl NonUnitalAlgHom.coe_inl

theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl
#align non_unital_alg_hom.inl_apply NonUnitalAlgHom.inl_apply

@[simp]
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl
#align non_unital_alg_hom.coe_inr NonUnitalAlgHom.coe_inr

theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl
#align non_unital_alg_hom.inr_apply NonUnitalAlgHom.inr_apply

end Prod

end NonUnitalAlgHom

/-! ### Interaction with `AlgHom` -/

namespace AlgHom

variable {F R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) [FunLike F A B] [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smulₛₗ := map_smul }

/-- A unital morphism of algebras is a `NonUnitalAlgHom`. -/
@[coe]
def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
#align alg_hom.to_non_unital_alg_hom AlgHom.toNonUnitalAlgHom

instance NonUnitalAlgHom.hasCoe : CoeOut (A →ₐ[R] B) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩
#align alg_hom.non_unital_alg_hom.has_coe AlgHom.NonUnitalAlgHom.hasCoe

@[simp]
theorem toNonUnitalAlgHom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl
#align alg_hom.to_non_unital_alg_hom_eq_coe AlgHom.toNonUnitalAlgHom_eq_coe

-- Note (#6057) : tagging simpNF because linter complains
@[simp, norm_cast, nolint simpNF]
theorem coe_to_nonUnitalAlgHom (f : A →ₐ[R] B) : ⇑(f.toNonUnitalAlgHom) = ⇑f :=
  rfl

#align alg_hom.coe_to_non_unital_alg_hom AlgHom.coe_to_nonUnitalAlgHom

end AlgHom

section RestrictScalars

namespace NonUnitalAlgHom

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital algebra homomorphism
over `S` can be viewed as a non-unital algebra homomorphism over `R`.  -/
def restrictScalars (f : A →ₙₐ[S] B) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    map_smul' := fun r x ↦ by have := map_smul f (r • 1) x; simpa }

@[simp]
lemma restrictScalars_apply (f : A →ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

lemma coe_restrictScalars (f : A →ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl

lemma coe_restrictScalars' (f : A →ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₙₐ[S] B) → A →ₙₐ[R] B) :=
  fun _ _ h ↦ ext (congr_fun h : _)

end NonUnitalAlgHom

end RestrictScalars
