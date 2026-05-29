/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Morphisms of star rings

This file defines a new type of morphism between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphism, namely `NonUnitalStarRingHom`, is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalRingHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalStarRingHom`

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/StarAlgHom.lean`.

## Tags

non-unital, ring, morphism, star
-/

@[expose] public section

open EquivLike

/-! ### Non-unital star ring homomorphisms -/

/-- A *non-unital ⋆-ring homomorphism* is a non-unital ring homomorphism between non-unital
non-associative semirings `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

/-- Reinterpret a non-unital star ring homomorphism as a non-unital ring homomorphism
by forgetting the interaction with the star operation.

Users should not make use of this, but instead utilize the coercion obtained through
the `NonUnitalRingHomClass` instance. -/
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

/-- `NonUnitalStarRingHomClass F A B` states that `F` is a type of non-unital ⋆-ring homomorphisms.
You should also extend this typeclass when you extend `NonUnitalStarRingHom`. -/
class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] : Prop extends StarHomClass F A B

namespace NonUnitalStarRingHomClass

variable {F A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- Turn an element of a type `F` satisfying `NonUnitalStarRingHomClass F A B` into an actual
`NonUnitalStarRingHom`. This is declared as the default coercion from `F` to `A →⋆ₙ+ B`. -/
@[coe]
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A →⋆ₙ+* B :=
  { (f : A →ₙ+* B) with
    map_star' := map_star f }

instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A →⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩

end NonUnitalStarRingHomClass

namespace NonUnitalStarRingHom

section Basic

variable {A B C D : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]
variable [NonUnitalNonAssocSemiring D] [Star D]

instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B where
  map_star f := f.map_star'

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →⋆ₙ+* B) : A → B := f

initialize_simps_projections NonUnitalStarRingHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    [NonUnitalStarRingHomClass F A B] (f : F) : ⇑(f : A →⋆ₙ+* B) = f :=
  rfl

@[simp]
theorem coe_toNonUnitalRingHom (f : A →⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆ₙ+* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `NonUnitalStarRingHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : A →⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
theorem coe_copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_mk (f : A →ₙ+* B) (h) : ((⟨f, h⟩ : A →⋆ₙ+* B) : A → B) = f := rfl

@[simp]
theorem mk_coe (f : A →⋆ₙ+* B) (h₁ h₂ h₃ h₄) :
    (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →⋆ₙ+* B) = f := by
  ext
  rfl

section

variable (A)

/-- The identity as a non-unital ⋆-ring homomorphism. -/
protected def id : A →⋆ₙ+* A :=
  { (1 : A →ₙ+* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(NonUnitalStarRingHom.id A) = id :=
  rfl

end

/-- The composition of non-unital ⋆-ring homomorphisms, as a non-unital ⋆-ring homomorphism. -/
def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [map_star, map_star] }

@[simp]
theorem coe_comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆ₙ+* D) (g : B →⋆ₙ+* C) (h : A →⋆ₙ+* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f :=
  ext fun _ => rfl

instance : Monoid (A →⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : A →⋆ₙ+* A) : A → A) = id :=
  rfl

theorem one_apply (a : A) : (1 : A →⋆ₙ+* A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

instance : Zero (A →⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

instance : Inhabited (A →⋆ₙ+* B) :=
  ⟨0⟩

instance : MonoidWithZero (A →⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]
theorem coe_zero : ((0 : A →⋆ₙ+* B) : A → B) = 0 :=
  rfl

theorem zero_apply (a : A) : (0 : A →⋆ₙ+* B) a = 0 :=
  rfl

end Zero


end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

/-- A *⋆-ring* equivalence is an equivalence preserving addition, multiplication, and the star
operation, which allows for considering both unital and non-unital equivalences with a single
structure. -/
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

/-- Reinterpret a star ring equivalence as a `RingEquiv` by forgetting the interaction with the star
operation. -/
add_decl_doc StarRingEquiv.toRingEquiv

/-- `StarRingEquivClass F A B` asserts `F` is a type of bundled ⋆-ring equivalences between `A` and
`B`.
You should also extend this typeclass when you extend `StarRingEquiv`. -/
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquivClass

-- See note [lower instance priority]
instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B where
  __ := hF

-- See note [lower instance priority]
instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [StarRingEquivClass F A B] :
    NonUnitalStarRingHomClass F A B where

/-- Turn an element of a type `F` satisfying `StarRingEquivClass F A B` into an actual
`StarRingEquiv`. This is declared as the default coercion from `F` to `A ≃⋆+* B`. -/
@[coe]
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f }

/-- Any type satisfying `StarRingEquivClass` can be cast into `StarRingEquiv` via
`StarRingEquivClass.toStarRingEquiv`. -/
instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩

end StarRingEquivClass

namespace StarRingEquiv

section Basic

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

instance : CoeOut (A ≃⋆+* B) (A ≃+* B) where coe := toRingEquiv

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
theorem toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e :=
  rfl

@[ext]
theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a star ring isomorphism. -/
@[refl]
def refl : A ≃⋆+* A :=
  { RingEquiv.refl A with
    map_star' := fun _ => rfl }

instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩

@[simp]
theorem coe_refl : ⇑(refl : A ≃⋆+* A) = id :=
  rfl

/-- The inverse of a star ring isomorphism is a star ring isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆+* B) : B ≃⋆+* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm }

/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃⋆+* B) : A → B := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆+* B) : B → A :=
  e.symm

initialize_simps_projections StarRingEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) → B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp] theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e := rfl

@[simp]
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl

@[simp]
theorem symm_mk (e : A ≃+* B) (h₁) : dsimp%
    (⟨e, h₁⟩ : A ≃⋆+* B).symm =
      { (⟨e, h₁⟩ : A ≃⋆+* B).symm with
        toRingEquiv := e.symm } :=
  rfl

@[simp]
theorem refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl :=
  rfl

/-- Transitivity of `StarRingEquiv`. -/
@[trans]
def trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }

@[simp]
theorem apply_symm_apply (e : A ≃⋆+* B) : ∀ x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃⋆+* B) : ∀ x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic


section Bijective

variable {F G A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]
variable [FunLike G B A]

/-- If a (unital or non-unital) star ring morphism has an inverse, it is an isomorphism of
star rings. -/
@[simps]
def ofStarRingHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆+* B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f

/-- Promote a bijective star ring homomorphism to a star ring equivalence. -/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarRingEquiv.ofBijective f hf : A → B) = f :=
  rfl

theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarRingEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

end StarRingEquiv
