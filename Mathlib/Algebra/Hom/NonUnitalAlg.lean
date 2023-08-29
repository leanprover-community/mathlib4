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

set_option autoImplicit true


universe u v w w₁ w₂ w₃

variable (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure NonUnitalAlgHom [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] extends A →+[R] B, A →ₙ* B
#align non_unital_alg_hom NonUnitalAlgHom

@[inherit_doc NonUnitalAlgHom]
infixr:25 " →ₙₐ " => NonUnitalAlgHom _

@[inherit_doc]
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom R A B

attribute [nolint docBlame] NonUnitalAlgHom.toMulHom

/-- `NonUnitalAlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class NonUnitalAlgHomClass (F : Type*) (R : outParam (Type*)) (A : outParam (Type*))
  (B : outParam (Type*)) [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [DistribMulAction R A] [DistribMulAction R B] extends DistribMulActionHomClass F R A B,
  MulHomClass F A B
#align non_unital_alg_hom_class NonUnitalAlgHomClass

-- Porting note: commented out, not dangerous
-- attribute [nolint dangerousInstance] NonUnitalAlgHomClass.toMulHomClass

namespace NonUnitalAlgHomClass

-- Porting note: Made following instance non-dangerous through [...] -> [...] replacement
-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass {F R A B : Type*}
    [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [NonUnitalAlgHomClass F R A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgHomClass F R A B› with coe := (⇑) }
#align non_unital_alg_hom_class.non_unital_alg_hom_class.to_non_unital_ring_hom_class NonUnitalAlgHomClass.toNonUnitalRingHomClass

variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module R B]

-- see Note [lower instance priority]
instance (priority := 100) {F : Type*} [NonUnitalAlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smul }

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₙₐ[R] B`. -/
@[coe]
def toNonUnitalAlgHom {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    map_smul' := map_smul f }

instance {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {R A B C} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C]

-- Porting note: Replaced with FunLike instance
-- /-- see Note [function coercion] -/
-- instance : CoeFun (A →ₙₐ[R] B) fun _ => A → B :=
--   ⟨toFun⟩

instance : FunLike (A →ₙₐ[R] B) A fun _ => B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
                       -- ⊢ { toDistribMulActionHom := { toMulActionHom := { toFun := f, map_smul' := ma …
                                                                   -- 🎉 no goals

@[simp]
theorem toFun_eq_coe (f : A →ₙₐ[R] B) : f.toFun = ⇑f :=
  rfl
#align non_unital_alg_hom.to_fun_eq_coe NonUnitalAlgHom.toFun_eq_coe

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →ₙₐ[R] B) : A → B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)

@[simp]
protected theorem coe_coe {F : Type*} [NonUnitalAlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₙₐ[R] B) = f :=
  rfl
#align non_unital_alg_hom.coe_coe NonUnitalAlgHom.coe_coe

theorem coe_injective : @Function.Injective (A →ₙₐ[R] B) (A → B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
  -- ⊢ { toDistribMulActionHom := { toMulActionHom := { toFun := f, map_smul' := ma …
                                              -- 🎉 no goals
#align non_unital_alg_hom.coe_injective NonUnitalAlgHom.coe_injective

instance : NonUnitalAlgHomClass (A →ₙₐ[R] B) R A B
    where
  coe f := f.toFun
  coe_injective' := coe_injective
  map_smul f := f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

@[ext]
theorem ext {f g : A →ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align non_unital_alg_hom.ext NonUnitalAlgHom.ext

theorem ext_iff {f g : A →ₙₐ[R] B} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    -- ⊢ ↑f x = ↑f x
    rfl, ext⟩
    -- 🎉 no goals
#align non_unital_alg_hom.ext_iff NonUnitalAlgHom.ext_iff

theorem congr_fun {f g : A →ₙₐ[R] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl
#align non_unital_alg_hom.congr_fun NonUnitalAlgHom.congr_fun

@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₙₐ[R] B) = f :=
  rfl
#align non_unital_alg_hom.coe_mk NonUnitalAlgHom.coe_mk

@[simp]
theorem mk_coe (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₙₐ[R] B) = f := by
  rfl
  -- 🎉 no goals
#align non_unital_alg_hom.mk_coe NonUnitalAlgHom.mk_coe

instance : CoeOut (A →ₙₐ[R] B) (A →+[R] B) :=
  ⟨toDistribMulActionHom⟩

instance : CoeOut (A →ₙₐ[R] B) (A →ₙ* B) :=
  ⟨toMulHom⟩

@[simp]
theorem toDistribMulActionHom_eq_coe (f : A →ₙₐ[R] B) : f.toDistribMulActionHom = ↑f :=
  rfl
#align non_unital_alg_hom.to_distrib_mul_action_hom_eq_coe NonUnitalAlgHom.toDistribMulActionHom_eq_coe

@[simp]
theorem toMulHom_eq_coe (f : A →ₙₐ[R] B) : f.toMulHom = ↑f :=
  rfl
#align non_unital_alg_hom.to_mul_hom_eq_coe NonUnitalAlgHom.toMulHom_eq_coe

@[simp, norm_cast]
theorem coe_to_distribMulActionHom (f : A →ₙₐ[R] B) : ⇑(f : A →+[R] B) = f :=
  rfl
#align non_unital_alg_hom.coe_to_distrib_mul_action_hom NonUnitalAlgHom.coe_to_distribMulActionHom

@[simp, norm_cast]
theorem coe_to_mulHom (f : A →ₙₐ[R] B) : ⇑(f : A →ₙ* B) = f :=
  rfl
#align non_unital_alg_hom.coe_to_mul_hom NonUnitalAlgHom.coe_to_mulHom

theorem to_distribMulActionHom_injective {f g : A →ₙₐ[R] B}
    (h : (f : A →+[R] B) = (g : A →+[R] B)) : f = g := by
  ext a
  -- ⊢ ↑f a = ↑g a
  exact DistribMulActionHom.congr_fun h a
  -- 🎉 no goals
#align non_unital_alg_hom.to_distrib_mul_action_hom_injective NonUnitalAlgHom.to_distribMulActionHom_injective

theorem to_mulHom_injective {f g : A →ₙₐ[R] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  -- ⊢ ↑f a = ↑g a
  exact FunLike.congr_fun h a
  -- 🎉 no goals
#align non_unital_alg_hom.to_mul_hom_injective NonUnitalAlgHom.to_mulHom_injective

@[norm_cast]
theorem coe_distribMulActionHom_mk (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₙₐ[R] B) : A →+[R] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  rfl
  -- 🎉 no goals
#align non_unital_alg_hom.coe_distrib_mul_action_hom_mk NonUnitalAlgHom.coe_distribMulActionHom_mk

@[norm_cast]
theorem coe_mulHom_mk (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₙₐ[R] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  rfl
  -- 🎉 no goals
#align non_unital_alg_hom.coe_mul_hom_mk NonUnitalAlgHom.coe_mulHom_mk

-- @[simp] -- Porting note: simp can prove this
protected theorem map_smul (f : A →ₙₐ[R] B) (c : R) (x : A) : f (c • x) = c • f x :=
  map_smul _ _ _
#align non_unital_alg_hom.map_smul NonUnitalAlgHom.map_smul

-- @[simp] -- Porting note: simp can prove this
protected theorem map_add (f : A →ₙₐ[R] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _
#align non_unital_alg_hom.map_add NonUnitalAlgHom.map_add

-- @[simp] -- Porting note: simp can prove this
protected theorem map_mul (f : A →ₙₐ[R] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _
#align non_unital_alg_hom.map_mul NonUnitalAlgHom.map_mul

-- @[simp] -- Porting note: simp can prove this
protected theorem map_zero (f : A →ₙₐ[R] B) : f 0 = 0 :=
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

instance : Zero (A →ₙₐ[R] B) :=
  ⟨{ (0 : A →+[R] B) with map_mul' := by simp }⟩
                                         -- 🎉 no goals

instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[simp]
theorem coe_zero : ⇑(0 : A →ₙₐ[R] B) = 0 :=
  rfl
#align non_unital_alg_hom.coe_zero NonUnitalAlgHom.coe_zero

@[simp]
theorem coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id :=
  rfl
#align non_unital_alg_hom.coe_one NonUnitalAlgHom.coe_one

theorem zero_apply (a : A) : (0 : A →ₙₐ[R] B) a = 0 :=
  rfl
#align non_unital_alg_hom.zero_apply NonUnitalAlgHom.zero_apply

theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
  rfl
#align non_unital_alg_hom.one_apply NonUnitalAlgHom.one_apply

instance : Inhabited (A →ₙₐ[R] B) :=
  ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) : A →ₙₐ[R] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →+[R] C).comp (g : A →+[R] B) with }
#align non_unital_alg_hom.comp NonUnitalAlgHom.comp

@[simp, norm_cast]
theorem coe_comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) :=
  rfl
#align non_unital_alg_hom.coe_comp NonUnitalAlgHom.coe_comp

theorem comp_apply (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) (x : A) : f.comp g x = f (g x) :=
  rfl
#align non_unital_alg_hom.comp_apply NonUnitalAlgHom.comp_apply

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : A →ₙₐ[R] B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →ₙₐ[R] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →+[R] B).inverse g h₁ h₂ with }
#align non_unital_alg_hom.inverse NonUnitalAlgHom.inverse

@[simp]
theorem coe_inverse (f : A →ₙₐ[R] B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B → A) = g :=
  rfl
#align non_unital_alg_hom.coe_inverse NonUnitalAlgHom.coe_inverse

/-! ### Operations on the product type

Note that much of this is copied from [`LinearAlgebra/Prod`](../../LinearAlgebra/Prod). -/


section Prod

variable (R A B)

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

/-- The prod of two morphisms is a morphism. -/
@[simps]
def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C
    where
  toFun := Pi.prod f g
  map_zero' := by simp only [Pi.prod, Prod.zero_eq_mk, map_zero]
                  -- 🎉 no goals
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
                     -- 🎉 no goals
                      -- 🎉 no goals
  map_mul' x y := by simp only [Pi.prod, Prod.mk_mul_mk, map_mul]
                     -- 🎉 no goals
  map_smul' c x := by simp only [Pi.prod, Prod.smul_mk, map_smul, RingHom.id_apply]
#align non_unital_alg_hom.prod NonUnitalAlgHom.prod

theorem coe_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align non_unital_alg_hom.coe_prod NonUnitalAlgHom.coe_prod

@[simp]
theorem fst_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  rfl
  -- 🎉 no goals
#align non_unital_alg_hom.fst_prod NonUnitalAlgHom.fst_prod

@[simp]
theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl
  -- 🎉 no goals
#align non_unital_alg_hom.snd_prod NonUnitalAlgHom.snd_prod

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  coe_injective Pi.prod_fst_snd
#align non_unital_alg_hom.prod_fst_snd NonUnitalAlgHom.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₙₐ[R] B) × (A →ₙₐ[R] C) ≃ (A →ₙₐ[R] B × C)
    where
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

variable {R A B} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smul := map_smul }

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

@[simp, norm_cast]
theorem coe_to_nonUnitalAlgHom (f : A →ₐ[R] B) : ⇑(f.toNonUnitalAlgHom) = ⇑f :=
  rfl
#align alg_hom.coe_to_non_unital_alg_hom AlgHom.coe_to_nonUnitalAlgHom

end AlgHom
