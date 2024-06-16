/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Star.Prod

#align_import algebra.star.star_alg_hom from "leanprover-community/mathlib"@"35882ddc66524b6980532a123a4ad4166db34c81"

/-!
# Morphisms of star algebras

This file defines morphisms between `R`-algebras (unital or non-unital) `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms, namely `StarAlgHom` and
`NonUnitalStarAlgHom` are direct extensions of their non-`star`red counterparts with a field
`map_star` which guarantees they preserve the star operation. We keep the type classes as generic
as possible, in keeping with the definition of `NonUnitalAlgHom` in the non-unital case. In this
file, we only assume `Star` unless we want to talk about the zero map as a
`NonUnitalStarAlgHom`, in which case we need `StarAddMonoid`. Note that the scalar ring `R`
is not required to have a star operation, nor do we need `StarRing` or `StarModule` structures on
`A` and `B`.

As with `NonUnitalAlgHom`, in the non-unital case the multiplications are not assumed to be
associative or unital, or even to be compatible with the scalar actions. In a typical application,
the operations will satisfy compatibility conditions making them into algebras (albeit possibly
non-associative and/or non-unital) but such conditions are not required here for the definitions.

The primary impetus for defining these types is that they constitute the morphisms in the categories
of unital C⋆-algebras (with `StarAlgHom`s) and of C⋆-algebras (with `NonUnitalStarAlgHom`s).

## Main definitions

  * `NonUnitalStarAlgHom`
  * `StarAlgHom`

## Tags

non-unital, algebra, morphism, star
-/

open EquivLike

/-! ### Non-unital star algebra homomorphisms -/


/-- A *non-unital ⋆-algebra homomorphism* is a non-unital algebra homomorphism between
non-unital `R`-algebras `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure NonUnitalStarAlgHom (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
  [Star B] extends A →ₙₐ[R] B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
#align non_unital_star_alg_hom NonUnitalStarAlgHom

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

/-- Reinterpret a non-unital star algebra homomorphism as a non-unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc NonUnitalStarAlgHom.toNonUnitalAlgHom

/-- `NonUnitalStarAlgHomClass F R A B` asserts `F` is a type of bundled non-unital ⋆-algebra
homomorphisms from `A` to `B`. -/
class NonUnitalStarAlgHomClass (F : Type*) (R A B : outParam Type*)
  [Monoid R] [Star A] [Star B] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] [NonUnitalAlgHomClass F R A B]
  extends StarHomClass F A B : Prop
#align non_unital_star_alg_hom_class NonUnitalStarAlgHomClass

namespace NonUnitalStarAlgHomClass

variable {F R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `NonUnitalStarAlgHomClass F R A B` into an actual
`NonUnitalStarAlgHom`. This is declared as the default coercion from `F` to `A →⋆ₙₐ[R] B`. -/
@[coe]
def toNonUnitalStarAlgHom [NonUnitalStarAlgHomClass F R A B] (f : F) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[R] B) with
    map_star' := map_star f }

instance [NonUnitalStarAlgHomClass F R A B] : CoeTC F (A →⋆ₙₐ[R] B) :=
  ⟨toNonUnitalStarAlgHom⟩

end NonUnitalStarAlgHomClass

namespace NonUnitalStarAlgHom

section Basic

variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

instance : FunLike (A →⋆ₙₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalAlgHomClass (A →⋆ₙₐ[R] B) R A B where
  map_smulₛₗ f := f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

instance : NonUnitalStarAlgHomClass (A →⋆ₙₐ[R] B) R A B where
  map_star f := f.map_star'

-- Porting note: in mathlib3 we didn't need the `Simps.apply` hint.
/-- See Note [custom simps projection] -/
def Simps.apply (f : A →⋆ₙₐ[R] B) : A → B := f

initialize_simps_projections NonUnitalStarAlgHom
  (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [NonUnitalStarAlgHomClass F R A B] (f : F) :
    ⇑(f : A →⋆ₙₐ[R] B) = f := rfl
#align non_unital_star_alg_hom.coe_coe NonUnitalStarAlgHom.coe_coe

@[simp]
theorem coe_toNonUnitalAlgHom {f : A →⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A → B) = f :=
  rfl
#align non_unital_star_alg_hom.coe_to_non_unital_alg_hom NonUnitalStarAlgHom.coe_toNonUnitalAlgHom

@[ext]
theorem ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
#align non_unital_star_alg_hom.ext NonUnitalStarAlgHom.ext

/-- Copy of a `NonUnitalStarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f
#align non_unital_star_alg_hom.copy NonUnitalStarAlgHom.copy

@[simp]
theorem coe_copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align non_unital_star_alg_hom.coe_copy NonUnitalStarAlgHom.coe_copy

theorem copy_eq (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align non_unital_star_alg_hom.copy_eq NonUnitalStarAlgHom.copy_eq

-- Porting note: doesn't align with Mathlib 3 because `NonUnitalStarAlgHom.mk` has a new signature
@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl
#align non_unital_star_alg_hom.coe_mk NonUnitalStarAlgHom.coe_mkₓ

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
theorem coe_mk' (f : A →ₙₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

-- Porting note: doesn't align with Mathlib 3 because `NonUnitalStarAlgHom.mk` has a new signature
@[simp]
theorem mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) = f := by
  ext
  rfl
#align non_unital_star_alg_hom.mk_coe NonUnitalStarAlgHom.mk_coeₓ

section

variable (R A)

/-- The identity as a non-unital ⋆-algebra homomorphism. -/
protected def id : A →⋆ₙₐ[R] A :=
  { (1 : A →ₙₐ[R] A) with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.id NonUnitalStarAlgHom.id

@[simp]
theorem coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id :=
  rfl
#align non_unital_star_alg_hom.coe_id NonUnitalStarAlgHom.coe_id

end

/-- The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism. -/
def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, eq_self_iff_true, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }
#align non_unital_star_alg_hom.comp NonUnitalStarAlgHom.comp

@[simp]
theorem coe_comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl
#align non_unital_star_alg_hom.coe_comp NonUnitalStarAlgHom.coe_comp

@[simp]
theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl
#align non_unital_star_alg_hom.comp_apply NonUnitalStarAlgHom.comp_apply

@[simp]
theorem comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align non_unital_star_alg_hom.comp_assoc NonUnitalStarAlgHom.comp_assoc

@[simp]
theorem id_comp (f : A →⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl
#align non_unital_star_alg_hom.id_comp NonUnitalStarAlgHom.id_comp

@[simp]
theorem comp_id (f : A →⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f :=
  ext fun _ => rfl
#align non_unital_star_alg_hom.comp_id NonUnitalStarAlgHom.comp_id

instance : Monoid (A →⋆ₙₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id :=
  rfl
#align non_unital_star_alg_hom.coe_one NonUnitalStarAlgHom.coe_one

theorem one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a :=
  rfl
#align non_unital_star_alg_hom.one_apply NonUnitalStarAlgHom.one_apply

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

instance : Zero (A →⋆ₙₐ[R] B) :=
  ⟨{ (0 : NonUnitalAlgHom (MonoidHom.id R) A B) with map_star' := by simp }⟩

instance : Inhabited (A →⋆ₙₐ[R] B) :=
  ⟨0⟩

instance : MonoidWithZero (A →⋆ₙₐ[R] A) :=
  { inferInstanceAs (Monoid (A →⋆ₙₐ[R] A)),
    inferInstanceAs (Zero (A →⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]
theorem coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 :=
  rfl
#align non_unital_star_alg_hom.coe_zero NonUnitalStarAlgHom.coe_zero

theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 :=
  rfl
#align non_unital_star_alg_hom.zero_apply NonUnitalStarAlgHom.zero_apply

end Zero

section RestrictScalars

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital star algebra homomorphism
over `S` can be viewed as a non-unital star algebra homomorphism over `R`.  -/
def restrictScalars (f : A →⋆ₙₐ[S] B) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]
lemma restrictScalars_apply (f : A →⋆ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

lemma coe_restrictScalars (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl

lemma coe_restrictScalars' (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →⋆ₙₐ[S] B) → A →⋆ₙₐ[R] B) :=
  fun _ _ h ↦ ext (DFunLike.congr_fun h : _)

end RestrictScalars

end NonUnitalStarAlgHom

/-! ### Unital star algebra homomorphisms -/


section Unital

/-- A *⋆-algebra homomorphism* is an algebra homomorphism between `R`-algebras `A` and `B`
equipped with a `star` operation, and this homomorphism is also `star`-preserving. -/
structure StarAlgHom (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] extends AlgHom R A B where
  /-- By definition, a ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ x : A, toFun (star x) = star (toFun x)
#align star_alg_hom StarAlgHom

@[inherit_doc StarAlgHom] infixr:25 " →⋆ₐ " => StarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₐ[" R "] " B => StarAlgHom R A B

/-- Reinterpret a unital star algebra homomorphism as a unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarAlgHom.toAlgHom

/-- `StarAlgHomClass F R A B` states that `F` is a type of ⋆-algebra homomorphisms.

You should also extend this typeclass when you extend `StarAlgHom`. -/
class StarAlgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    [FunLike F A B] [AlgHomClass F R A B] extends StarHomClass F A B : Prop
#align star_alg_hom_class StarAlgHomClass

-- Porting note: no longer needed
---- `R` becomes a metavariable but that's fine because it's an `outParam`
--attribute [nolint dangerousInstance] StarAlgHomClass.toStarHomClass

namespace StarAlgHomClass

variable (F R A B : Type*)

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalStarAlgHomClass {_ : CommSemiring R} {_ : Semiring A}
  [Algebra R A] [Star A] {_ : Semiring B} [Algebra R B] [Star B]
  [FunLike F A B] [AlgHomClass F R A B] [StarAlgHomClass F R A B] :
  NonUnitalStarAlgHomClass F R A B :=
  { }
#align star_alg_hom_class.to_non_unital_star_alg_hom_class StarAlgHomClass.toNonUnitalStarAlgHomClass

variable [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
variable [Semiring B] [Algebra R B] [Star B] [FunLike F A B] [AlgHomClass F R A B]
variable [StarAlgHomClass F R A B]

variable {F R A B} in
/-- Turn an element of a type `F` satisfying `StarAlgHomClass F R A B` into an actual
`StarAlgHom`. This is declared as the default coercion from `F` to `A →⋆ₐ[R] B`. -/
@[coe]
def toStarAlgHom (f : F) : A →⋆ₐ[R] B :=
  { (f : A →ₐ[R] B) with
    map_star' := map_star f }

instance : CoeTC F (A →⋆ₐ[R] B) :=
  ⟨toStarAlgHom⟩

end StarAlgHomClass

namespace StarAlgHom

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

instance : FunLike (A →⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr

instance : AlgHomClass (A →⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'

instance : StarAlgHomClass (A →⋆ₐ[R] B) R A B where
  map_star f := f.map_star'

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarAlgHomClass F R A B] (f : F) :
    ⇑(f : A →⋆ₐ[R] B) = f :=
  rfl
#align star_alg_hom.coe_coe StarAlgHom.coe_coe

-- Porting note: in mathlib3 we didn't need the `Simps.apply` hint.
/-- See Note [custom simps projection] -/
def Simps.apply (f : A →⋆ₐ[R] B) : A → B := f

initialize_simps_projections StarAlgHom (toFun → apply)

@[simp]
theorem coe_toAlgHom {f : A →⋆ₐ[R] B} : (f.toAlgHom : A → B) = f :=
  rfl
#align star_alg_hom.coe_to_alg_hom StarAlgHom.coe_toAlgHom

@[ext]
theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
#align star_alg_hom.ext StarAlgHom.ext

/-- Copy of a `StarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₐ[R] B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f
#align star_alg_hom.copy StarAlgHom.copy

@[simp]
theorem coe_copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align star_alg_hom.coe_copy StarAlgHom.coe_copy

theorem copy_eq (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align star_alg_hom.copy_eq StarAlgHom.copy_eq

-- Porting note: doesn't align with Mathlib 3 because `StarAlgHom.mk` has a new signature
@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl
#align star_alg_hom.coe_mk StarAlgHom.coe_mkₓ

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
theorem coe_mk' (f : A →ₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

-- Porting note: doesn't align with Mathlib 3 because `StarAlgHom.mk` has a new signature
@[simp]
theorem mk_coe (f : A →⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) = f := by
  ext
  rfl
#align star_alg_hom.mk_coe StarAlgHom.mk_coeₓ

section

variable (R A)

/-- The identity as a `StarAlgHom`. -/
protected def id : A →⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun _ => rfl }
#align star_alg_hom.id StarAlgHom.id

@[simp]
theorem coe_id : ⇑(StarAlgHom.id R A) = id :=
  rfl
#align star_alg_hom.coe_id StarAlgHom.coe_id

/-- `algebraMap R A` as a `StarAlgHom` when `A` is a star algebra over `R`. -/
@[simps]
def ofId (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
    [Algebra R A] [StarModule R A] : R →⋆ₐ[R] A :=
  { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

end

instance : Inhabited (A →⋆ₐ[R] A) :=
  ⟨StarAlgHom.id R A⟩

/-- The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism. -/
def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
  { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, eq_self_iff_true, forall_const] }
#align star_alg_hom.comp StarAlgHom.comp

@[simp]
theorem coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl
#align star_alg_hom.coe_comp StarAlgHom.coe_comp

@[simp]
theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl
#align star_alg_hom.comp_apply StarAlgHom.comp_apply

@[simp]
theorem comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align star_alg_hom.comp_assoc StarAlgHom.comp_assoc

@[simp]
theorem id_comp (f : A →⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl
#align star_alg_hom.id_comp StarAlgHom.id_comp

@[simp]
theorem comp_id (f : A →⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f :=
  ext fun _ => rfl
#align star_alg_hom.comp_id StarAlgHom.comp_id

instance : Monoid (A →⋆ₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

/-- A unital morphism of ⋆-algebras is a `NonUnitalStarAlgHom`. -/
def toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
#align star_alg_hom.to_non_unital_star_alg_hom StarAlgHom.toNonUnitalStarAlgHom

@[simp]
theorem coe_toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A → B) = f :=
  rfl
#align star_alg_hom.coe_to_non_unital_star_alg_hom StarAlgHom.coe_toNonUnitalStarAlgHom

end StarAlgHom

end Unital

/-! ### Operations on the product type

Note that this is copied from [`Algebra.Hom.NonUnitalAlg`](../Hom/NonUnitalAlg). -/


namespace NonUnitalStarAlgHom

section Prod

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [NonUnitalNonAssocSemiring C]
  [DistribMulAction R C] [Star C]

/-- The first projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
def fst : A × B →⋆ₙₐ[R] A :=
  { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.fst NonUnitalStarAlgHom.fst

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
def snd : A × B →⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }
#align non_unital_star_alg_hom.snd NonUnitalStarAlgHom.snd

variable {R A B C}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : A →⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.star_def] }
#align non_unital_star_alg_hom.prod NonUnitalStarAlgHom.prod

theorem coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align non_unital_star_alg_hom.coe_prod NonUnitalStarAlgHom.coe_prod

@[simp]
theorem fst_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl
#align non_unital_star_alg_hom.fst_prod NonUnitalStarAlgHom.fst_prod

@[simp]
theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl
#align non_unital_star_alg_hom.snd_prod NonUnitalStarAlgHom.snd_prod

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Pi.prod_fst_snd
#align non_unital_star_alg_hom.prod_fst_snd NonUnitalStarAlgHom.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C) ≃ (A →⋆ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align non_unital_star_alg_hom.prod_equiv NonUnitalStarAlgHom.prodEquiv

end Prod

section InlInr

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0
#align non_unital_star_alg_hom.inl NonUnitalStarAlgHom.inl

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →⋆ₙₐ[R] A × B :=
  prod 0 1
#align non_unital_star_alg_hom.inr NonUnitalStarAlgHom.inr

variable {R A B}

@[simp]
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl
#align non_unital_star_alg_hom.coe_inl NonUnitalStarAlgHom.coe_inl

theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl
#align non_unital_star_alg_hom.inl_apply NonUnitalStarAlgHom.inl_apply

@[simp]
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl
#align non_unital_star_alg_hom.coe_inr NonUnitalStarAlgHom.coe_inr

theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl
#align non_unital_star_alg_hom.inr_apply NonUnitalStarAlgHom.inr_apply

end InlInr

end NonUnitalStarAlgHom

namespace StarAlgHom

variable (R A B C : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- The first projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
def fst : A × B →⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun _ => rfl }
#align star_alg_hom.fst StarAlgHom.fst

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
def snd : A × B →⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun _ => rfl }
#align star_alg_hom.snd StarAlgHom.snd

variable {R A B C}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : A →⋆ₐ[R] B × C :=
  { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }
#align star_alg_hom.prod StarAlgHom.prod

theorem coe_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align star_alg_hom.coe_prod StarAlgHom.coe_prod

@[simp]
theorem fst_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl
#align star_alg_hom.fst_prod StarAlgHom.fst_prod

@[simp]
theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl
#align star_alg_hom.snd_prod StarAlgHom.snd_prod

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Pi.prod_fst_snd
#align star_alg_hom.prod_fst_snd StarAlgHom.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₐ[R] B) × (A →⋆ₐ[R] C) ≃ (A →⋆ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align star_alg_hom.prod_equiv StarAlgHom.prodEquiv

end StarAlgHom

/-! ### Star algebra equivalences -/

-- Porting note: changed order of arguments to work around
-- [https://github.com/leanprover-community/mathlib4/issues/2505]
/-- A *⋆-algebra* equivalence is an equivalence preserving addition, multiplication, scalar
multiplication and the star operation, which allows for considering both unital and non-unital
equivalences with a single structure. Currently, `AlgEquiv` requires unital algebras, which is
why this structure does not extend it. -/
structure StarAlgEquiv (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  [Star A] [Star B] extends A ≃+* B where
  /-- By definition, a ⋆-algebra equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
  /-- By definition, a ⋆-algebra equivalence commutes with the action of scalars. -/
  map_smul' : ∀ (r : R) (a : A), toFun (r • a) = r • toFun a
#align star_alg_equiv StarAlgEquiv

@[inherit_doc StarAlgEquiv] infixr:25 " ≃⋆ₐ " => StarAlgEquiv _

@[inherit_doc] notation:25 A " ≃⋆ₐ[" R "] " B => StarAlgEquiv R A B

/-- Reinterpret a star algebra equivalence as a `RingEquiv` by forgetting the interaction with
the star operation and scalar multiplication. -/
add_decl_doc StarAlgEquiv.toRingEquiv

/-- The class that directly extends `RingEquivClass` and `SMulHomClass`.

Mostly an implementation detail for `StarAlgEquivClass`.
-/
class NonUnitalAlgEquivClass (F : Type*) (R A B : outParam Type*)
  [Add A] [Mul A] [SMul R A] [Add B] [Mul B] [SMul R B] [EquivLike F A B]
  extends RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B : Prop where

/-- `StarAlgEquivClass F R A B` asserts `F` is a type of bundled ⋆-algebra equivalences between
`A` and `B`.

You should also extend this typeclass when you extend `StarAlgEquiv`. -/
class StarAlgEquivClass (F : Type*) (R A B : outParam Type*)
  [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
  [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] : Prop where
  /-- By definition, a ⋆-algebra equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)
#align star_alg_equiv_class StarAlgEquivClass

-- Porting note: no longer needed
---- `R` becomes a metavariable but that's fine because it's an `outParam`
-- attribute [nolint dangerousInstance] StarAlgEquivClass.toRingEquivClass

namespace StarAlgEquivClass

-- Porting note: Made following instance non-dangerous through [...] -> [...] replacement
-- See note [lower instance priority]
instance (priority := 50) {F R A B : Type*} {_ : Add A} {_ : Mul A} [SMul R A] {_ : Star A}
    {_ : Add B} {_ : Mul B} [SMul R B] {_ : Star B}
    [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
    [hF : StarAlgEquivClass F R A B] :
    StarHomClass F A B :=
  { hF with }

-- See note [lower instance priority]
instance (priority := 100) {F R A B : Type*} {_ : Monoid R} {_ : NonUnitalNonAssocSemiring A}
    [DistribMulAction R A] {_ : NonUnitalNonAssocSemiring B}
    [DistribMulAction R B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] :
    NonUnitalAlgHomClass F R A B :=
  { }

-- See note [lower instance priority]
instance (priority := 100) {F R A B : Type*} {_ : Monoid R} {_ : NonUnitalNonAssocSemiring A}
    [DistribMulAction R A] {_ : Star A} {_ : NonUnitalNonAssocSemiring B}
    [DistribMulAction R B] {_ : Star B} [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
    [StarAlgEquivClass F R A B] :
    NonUnitalStarAlgHomClass F R A B :=
  { }

-- See note [lower instance priority]
instance (priority := 100) instAlgHomClass (F R A B : Type*) {_ : CommSemiring R}
    {_ : Semiring A} [Algebra R A] {_ : Semiring B} [Algebra R B]
    [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] :
    AlgEquivClass F R A B :=
  { commutes := fun f r => by simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] }

-- See note [lower instance priority]
instance (priority := 100) instStarAlgHomClass (F R A B : Type*) {_ : CommSemiring R}
    {_ : Semiring A} [Algebra R A] {_ : Star A} {_ : Semiring B} [Algebra R B] {_ : Star B}
    [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarAlgEquivClass F R A B] :
    StarAlgHomClass F R A B :=
  { }

/-- Turn an element of a type `F` satisfying `StarAlgEquivClass F R A B` into an actual
`StarAlgEquiv`. This is declared as the default coercion from `F` to `A ≃⋆ₐ[R] B`. -/
@[coe]
def toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
    [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarAlgEquivClass F R A B]
    (f : F) : A ≃⋆ₐ[R] B :=
  { (f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f}

/-- Any type satisfying `StarAlgEquivClass` can be cast into `StarAlgEquiv` via
`StarAlgEquivClass.toStarAlgEquiv`. -/
instance instCoeHead {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
    [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
    [StarAlgEquivClass F R A B] : CoeHead F (A ≃⋆ₐ[R] B) :=
  ⟨toStarAlgEquiv⟩

end StarAlgEquivClass

namespace StarAlgEquiv

section Basic

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

instance : EquivLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

instance : StarAlgEquivClass (A ≃⋆ₐ[R] B) R A B where
  map_star := map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
instance : FunLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

@[simp]
theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e :=
  rfl

@[ext]
theorem ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align star_alg_equiv.ext StarAlgEquiv.ext

theorem ext_iff {f g : A ≃⋆ₐ[R] B} : f = g ↔ ∀ a, f a = g a :=
  DFunLike.ext_iff
#align star_alg_equiv.ext_iff StarAlgEquiv.ext_iff

/-- The identity map is a star algebra isomorphism. -/
@[refl]
def refl : A ≃⋆ₐ[R] A :=
  { RingEquiv.refl A with
    map_smul' := fun _ _ => rfl
    map_star' := fun _ => rfl }
#align star_alg_equiv.refl StarAlgEquiv.refl

instance : Inhabited (A ≃⋆ₐ[R] A) :=
  ⟨refl⟩

@[simp]
theorem coe_refl : ⇑(refl : A ≃⋆ₐ[R] A) = id :=
  rfl
#align star_alg_equiv.coe_refl StarAlgEquiv.coe_refl

-- Porting note: changed proof a bit by using `EquivLike` to avoid lots of coercions
/-- The inverse of a star algebra isomorphism is a star algebra isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆ₐ[R] B) : B ≃⋆ₐ[R] A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm
    map_smul' := fun r b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_smul e r (inv e b)).symm }
#align star_alg_equiv.symm StarAlgEquiv.symm

-- Porting note: in mathlib3 we didn't need the `Simps.apply` hint.
/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃⋆ₐ[R] B) : A → B := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆ₐ[R] B) : B → A :=
  e.symm
#align star_alg_equiv.simps.symm_apply StarAlgEquiv.Simps.symm_apply

initialize_simps_projections StarAlgEquiv (toFun → apply, invFun → symm_apply)

-- Porting note: use `EquivLike.inv` instead of `invFun`
@[simp]
theorem invFun_eq_symm {e : A ≃⋆ₐ[R] B} : EquivLike.inv e = e.symm :=
  rfl
#align star_alg_equiv.inv_fun_eq_symm StarAlgEquiv.invFun_eq_symm

@[simp]
theorem symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e := by
  ext
  rfl
#align star_alg_equiv.symm_symm StarAlgEquiv.symm_symm

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) → B ≃⋆ₐ[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
#align star_alg_equiv.symm_bijective StarAlgEquiv.symm_bijective

-- Porting note: doesn't align with Mathlib 3 because `StarAlgEquiv.mk` has a new signature
@[simp]
theorem mk_coe' (e : A ≃⋆ₐ[R] B) (f h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨f, e, h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩ : B ≃⋆ₐ[R] A) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
#align star_alg_equiv.mk_coe' StarAlgEquiv.mk_coe'ₓ

/-- Auxilliary definition to avoid looping in `dsimp` with `StarAlgEquiv.symm_mk`. -/
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :=
  (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩ : A ≃⋆ₐ[R] B).symm

-- Porting note: doesn't align with Mathlib 3 because `StarAlgEquiv.mk` has a new signature
@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩ : A ≃⋆ₐ[R] B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ h₆ with
        toFun := f'
        invFun := f } :=
  rfl
#align star_alg_equiv.symm_mk StarAlgEquiv.symm_mkₓ

@[simp]
theorem refl_symm : (StarAlgEquiv.refl : A ≃⋆ₐ[R] A).symm = StarAlgEquiv.refl :=
  rfl
#align star_alg_equiv.refl_symm StarAlgEquiv.refl_symm

-- should be a `simp` lemma, but causes a linter timeout
theorem to_ringEquiv_symm (f : A ≃⋆ₐ[R] B) : (f : A ≃+* B).symm = f.symm :=
  rfl
#align star_alg_equiv.to_ring_equiv_symm StarAlgEquiv.to_ringEquiv_symm

@[simp]
theorem symm_to_ringEquiv (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃+* A) = (e : A ≃+* B).symm :=
  rfl
#align star_alg_equiv.symm_to_ring_equiv StarAlgEquiv.symm_to_ringEquiv

/-- Transitivity of `StarAlgEquiv`. -/
@[trans]
def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
  { e₁.toRingEquiv.trans
      e₂.toRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul', e₂.map_smul']
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }
#align star_alg_equiv.trans StarAlgEquiv.trans

@[simp]
theorem apply_symm_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply
#align star_alg_equiv.apply_symm_apply StarAlgEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply
#align star_alg_equiv.symm_apply_apply StarAlgEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl
#align star_alg_equiv.symm_trans_apply StarAlgEquiv.symm_trans_apply

@[simp]
theorem coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align star_alg_equiv.coe_trans StarAlgEquiv.coe_trans

@[simp]
theorem trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
#align star_alg_equiv.trans_apply StarAlgEquiv.trans_apply

theorem leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv
#align star_alg_equiv.left_inverse_symm StarAlgEquiv.leftInverse_symm

theorem rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e :=
  e.right_inv
#align star_alg_equiv.right_inverse_symm StarAlgEquiv.rightInverse_symm

end Basic

section Bijective

variable {F G R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [NonUnitalStarAlgHomClass F R A B]
variable [FunLike G B A] [NonUnitalAlgHomClass G R B A] [NonUnitalStarAlgHomClass G R B A]

/-- If a (unital or non-unital) star algebra morphism has an inverse, it is an isomorphism of
star algebras. -/
@[simps]
def ofStarAlgHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_smul' := map_smul f
  map_star' := map_star f
#align star_alg_equiv.of_star_alg_hom StarAlgEquiv.ofStarAlgHom

/-- Promote a bijective star algebra homomorphism to a star algebra equivalence. -/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B :=
  {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }
#align star_alg_equiv.of_bijective StarAlgEquiv.ofBijective

@[simp]
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarAlgEquiv.ofBijective f hf : A → B) = f :=
  rfl
#align star_alg_equiv.coe_of_bijective StarAlgEquiv.coe_ofBijective

theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarAlgEquiv.ofBijective f hf) a = f a :=
  rfl
#align star_alg_equiv.of_bijective_apply StarAlgEquiv.ofBijective_apply

end Bijective

end StarAlgEquiv
