/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Star.StarRingHom

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

@[expose] public section

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

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

/-- Reinterpret a non-unital star algebra homomorphism as a non-unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc NonUnitalStarAlgHom.toNonUnitalAlgHom

namespace NonUnitalStarAlgHomClass

variable {F R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` and `StarHomClass F A B`
into an actual `NonUnitalStarAlgHom`. This is declared as the default coercion from `F` to
`A →⋆ₙₐ[R] B`. -/
@[coe]
def toNonUnitalStarAlgHom [StarHomClass F A B] (f : F) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[R] B) with
    map_star' := map_star f }

instance [StarHomClass F A B] : CoeTC F (A →⋆ₙₐ[R] B) :=
  ⟨toNonUnitalStarAlgHom⟩

instance [StarHomClass F A B] : NonUnitalStarRingHomClass F A B :=
  NonUnitalStarRingHomClass.mk

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

instance : StarHomClass (A →⋆ₙₐ[R] B) A B where
  map_star f := f.map_star'

initialize_simps_projections NonUnitalStarAlgHom
  (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

@[simp]
theorem coe_toNonUnitalAlgHom {f : A →⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A → B) = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `NonUnitalStarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
theorem coe_copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about this being `@[simp]`. -/
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
theorem coe_mk' (f : A →ₙₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a non-unital ⋆-algebra homomorphism. -/
protected def id : A →⋆ₙₐ[R] A :=
  { (1 : A →ₙₐ[R] A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id :=
  rfl

end

/-- The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism. -/
def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }

@[simp]
theorem coe_comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f :=
  ext fun _ => rfl

instance : Monoid (A →⋆ₙₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id :=
  rfl

theorem one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a :=
  rfl

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
  { inferInstanceAs% (Monoid (A →⋆ₙₐ[R] A)),
    inferInstanceAs% (Zero (A →⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]
theorem coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 :=
  rfl

theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 :=
  rfl

end Zero

section RestrictScalars

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital star algebra homomorphism
over `S` can be viewed as a non-unital star algebra homomorphism over `R`. -/
def restrictScalars (f : A →⋆ₙₐ[S] B) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]
lemma restrictScalars_apply (f : A →⋆ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

lemma coe_restrictScalars (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl

lemma coe_restrictScalars' (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →⋆ₙₐ[S] B) → A →⋆ₙₐ[R] B) :=
  fun _ _ h ↦ ext (DFunLike.congr_fun h :)

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

@[inherit_doc StarAlgHom] infixr:25 " →⋆ₐ " => StarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₐ[" R "] " B => StarAlgHom R A B

/-- Reinterpret a unital star algebra homomorphism as a unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarAlgHom.toAlgHom

namespace StarAlgHomClass

variable {F R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
variable [Semiring B] [Algebra R B] [Star B] [FunLike F A B] [AlgHomClass F R A B]
variable [StarHomClass F A B]

/-- Turn an element of a type `F` satisfying `AlgHomClass F R A B` and `StarHomClass F A B` into an
actual `StarAlgHom`. This is declared as the default coercion from `F` to `A →⋆ₐ[R] B`. -/
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

instance : StarHomClass (A →⋆ₐ[R] B) A B where
  map_star f := f.map_star'

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₐ[R] B) = f :=
  rfl

initialize_simps_projections StarAlgHom (toFun → apply)

@[simp]
theorem coe_toAlgHom {f : A →⋆ₐ[R] B} : (f.toAlgHom : A → B) = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

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

@[simp]
theorem coe_copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
theorem coe_mk' (f : A →ₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a `StarAlgHom`. -/
protected def id : A →⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(StarAlgHom.id R A) = id :=
  rfl

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
        Function.comp_apply, forall_const] }

@[simp]
theorem coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f :=
  ext fun _ => rfl

instance : Monoid (A →⋆ₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

/-- A unital morphism of ⋆-algebras is a `NonUnitalStarAlgHom`. -/
def toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

@[simp]
theorem coe_toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A → B) = f :=
  rfl

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

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
def snd : A × B →⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : A →⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.star_def] }

theorem coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C) ≃ (A →⋆ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end Prod

section Pi

variable {ι : Type*}

/-- `Function.eval` as a `NonUnitalStarAlgHom`. -/
@[simps]
def _root_.Pi.evalNonUnitalStarAlgHom (R : Type*) (A : ι → Type*) (j : ι) [Monoid R]
    [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)] [∀ i, Star (A i)] :
    (∀ i, A i) →⋆ₙₐ[R] A j :=
  { Pi.evalMulHom A j, Pi.evalAddHom A j with
    map_smul' _ _ := rfl
    map_zero' := rfl
    map_star' _ := rfl }

/-- `Function.eval` as a `StarAlgHom`. -/
@[simps]
def _root_.Pi.evalStarAlgHom (R : Type*) (A : ι → Type*) (j : ι) [CommSemiring R]
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, Star (A i)] :
    (∀ i, A i) →⋆ₐ[R] A j :=
  { Pi.evalNonUnitalStarAlgHom R A j, Pi.evalRingHom A j with
    commutes' _ := rfl }

end Pi

section InlInr

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →⋆ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl

theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl

theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl

end InlInr

end NonUnitalStarAlgHom

namespace StarAlgHom

variable (R A B C : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- The first projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
def fst : A × B →⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun _ => rfl }

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
def snd : A × B →⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : A →⋆ₐ[R] B × C :=
  { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }

theorem coe_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₐ[R] B) × (A →⋆ₐ[R] C) ≃ (A →⋆ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end StarAlgHom

/-! ### Star algebra equivalences -/

/-- A *⋆-algebra* equivalence is an equivalence preserving addition, multiplication, scalar
multiplication and the star operation, which allows for considering both unital and non-unital
equivalences with a single structure. -/
structure StarAlgEquiv (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  [Star A] [Star B] extends A ≃⋆+* B where
  /-- By definition, a ⋆-algebra equivalence commutes with the action of scalars. -/
  map_smul' : ∀ (r : R) (a : A), toFun (r • a) = r • toFun a

@[inherit_doc StarAlgEquiv] infixr:25 " ≃⋆ₐ " => StarAlgEquiv _

@[inherit_doc] notation:25 A " ≃⋆ₐ[" R "] " B => StarAlgEquiv R A B

/-- Reinterpret a star algebra equivalence as a `StarRingEquiv` by forgetting the interaction with
the scalar multiplication. -/
add_decl_doc StarAlgEquiv.toStarRingEquiv

/-- The class that directly extends `RingEquivClass` and `SMulHomClass`.

Mostly an implementation detail for the ⋆-algebra equivalence class
which is currently: `[NonUnitalAlgEquivClass]` and `[StarHomClass]`.
-/
class NonUnitalAlgEquivClass (F : Type*) (R A B : outParam Type*)
  [Add A] [Mul A] [SMul R A] [Add B] [Mul B] [SMul R B] [EquivLike F A B] : Prop
  extends RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B where

-- See note [lower instance priority]
instance (priority := 100) {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [EquivLike F A B]
    [NonUnitalAlgEquivClass F R A B] :
    NonUnitalAlgHomClass F R A B :=
  { }

-- See note [lower instance priority]
instance (priority := 100) (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] :
    AlgEquivClass F R A B :=
  { commutes := fun f r => by simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] }

namespace StarAlgEquivClass

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` and `StarHomClass F A B` into
an actual `StarAlgEquiv`. This is declared as the default coercion from `F` to `A ≃⋆ₐ[R] B`. -/
@[coe]
def toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
    [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B]
    (f : F) : A ≃⋆ₐ[R] B :=
  { (f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f }

/-- Any type satisfying `AlgEquivClass` and `StarHomClass` can be cast into `StarAlgEquiv` via
`StarAlgEquivClass.toStarAlgEquiv`. -/
instance instCoeHead {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
    [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B] :
    CoeHead F (A ≃⋆ₐ[R] B) :=
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
    rcases f with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    congr

instance : NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

instance : StarRingEquivClass (A ≃⋆ₐ[R] B) A B where
  map_star f := f.map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
instance : FunLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

@[simp]
theorem toStarRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toStarRingEquiv = e := rfl

theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e :=
  rfl

@[ext]
theorem ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The identity map is a star algebra isomorphism. -/
@[refl]
def refl : A ≃⋆ₐ[R] A :=
  { StarRingEquiv.refl (A := A) with
    map_smul' := fun _ _ => rfl }

instance : Inhabited (A ≃⋆ₐ[R] A) :=
  ⟨refl⟩

@[simp]
theorem coe_refl : ⇑(refl : A ≃⋆ₐ[R] A) = id :=
  rfl

/-- The inverse of a star algebra isomorphism is a star algebra isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆ₐ[R] B) : B ≃⋆ₐ[R] A :=
  { e.symm with
    map_smul' := fun r b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_smul e r (inv e b)).symm }

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆ₐ[R] B) : B → A :=
  e.symm

initialize_simps_projections StarAlgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm {e : A ≃⋆ₐ[R] B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) → B ≃⋆ₐ[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem coe_mk (e h) : ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e := rfl

@[simp]
theorem mk_coe (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B) = e := ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `StarAlgEquiv.symm_mk`. -/
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :=
  (⟨⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B).symm

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ h₆ with
        toFun := f'
        invFun := f } :=
  rfl

@[simp]
theorem refl_symm : (StarAlgEquiv.refl : A ≃⋆ₐ[R] A).symm = StarAlgEquiv.refl :=
  rfl

@[simp]
theorem toStarRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* B).symm := rfl

@[simp]
theorem toRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃+* A) = (e : A ≃+* B).symm :=
  rfl

@[deprecated "← toRingEquiv_symm" (since := "2025-08-25")]
theorem to_ringEquiv_symm (f : A ≃⋆ₐ[R] B) : (f : A ≃+* B).symm = f.symm := rfl
@[deprecated (since := "2025-08-25")] alias symm_to_ringEquiv := toRingEquiv_symm

/-- Transitivity of `StarAlgEquiv`. -/
@[trans]
def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
  { e₁.toStarRingEquiv.trans e₂.toStarRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul', e₂.map_smul'] }

@[simp]
theorem apply_symm_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e (e.symm x) = x :=
  e.toStarRingEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e.symm (e x) = x :=
  e.toStarRingEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

theorem leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e :=
  e.right_inv

section AlgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

/-- Interpret a ⋆-algebra equivalence as an algebra equivalence. -/
def toAlgEquiv (f : A ≃⋆ₐ[R] B) : A ≃ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one', map_smul']; simp

@[simp]
theorem toAlgEquiv_symm (f : A ≃⋆ₐ[R] B) : f.symm.toAlgEquiv = f.toAlgEquiv.symm := rfl

@[simp]
theorem coe_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv = ⇑f := rfl

@[simp]
theorem coe_symm_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv.symm = ⇑f.symm := rfl

@[simp]
theorem toAlgEquiv_trans {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
    (g : B ≃⋆ₐ[R] C) : (f.trans g).toAlgEquiv = f.toAlgEquiv.trans g.toAlgEquiv := rfl

theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv (R := R) (A := A) (B := B)) :=
  fun _ _ h => ext <| AlgEquiv.congr_fun h

@[simp]
theorem toAlgEquiv_refl : (refl : A ≃⋆ₐ[R] A).toAlgEquiv = AlgEquiv.refl := rfl

/-- Upgrade an algebra equivalence to a ⋆-algebra equivalence given that it preserves the
`star` operation. -/
def ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    A ≃⋆ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  map_smul' := f.toLinearEquiv.map_smul
  map_star' := map_star

@[simp]
theorem ofAlgEquiv_apply (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) (x : A) :
    ofAlgEquiv f map_star x = f x := rfl

@[simp]
theorem ofAlgEquiv_symm (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).symm = ofAlgEquiv f.symm (ofAlgEquiv f map_star).symm.map_star' :=
  rfl

@[simp]
theorem toAlgEquiv_ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).toAlgEquiv = f := rfl

@[simp]
theorem ofAlgEquiv_toAlgEquiv (f : A ≃⋆ₐ[R] B) (map_star) :
    ofAlgEquiv f.toAlgEquiv map_star = f := rfl

end AlgEquiv

end Basic

section Bijective

variable {F G R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
variable [FunLike G B A] [NonUnitalAlgHomClass G R B A] [StarHomClass G B A]

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

/-- Promote a bijective star algebra homomorphism to a star algebra equivalence. -/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B :=
  {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }

@[simp]
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarAlgEquiv.ofBijective f hf : A → B) = f :=
  rfl

theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarAlgEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

section Group
variable {S R : Type*} [Mul R] [Add R] [Star R] [SMul S R]

@[simps -isSimp one mul]
instance aut : Group (R ≃⋆ₐ[S] R) where
  one := refl
  mul a b := b.trans a
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  inv f := f.symm
  inv_mul_cancel f := ext <| symm_apply_apply f

@[simp] theorem mul_apply (f g : R ≃⋆ₐ[S] R) (x : R) : (f * g) x = f (g x) := rfl

@[simp] theorem one_apply (x : R) : (1 : R ≃⋆ₐ[S] R) x = x := rfl

theorem aut_inv (f : R ≃⋆ₐ[S] R) : f⁻¹ = f.symm := rfl

@[simp] theorem coe_pow (f : R ≃⋆ₐ[S] R) (n : ℕ) :
    ⇑(f ^ n) = (⇑f)^[n] :=
  hom_coe_pow _ (funext one_apply) (fun f g ↦ funext <| mul_apply f g) _ _

end Group

end StarAlgEquiv
