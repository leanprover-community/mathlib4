/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Basic
/-!
# Morphisms of star monoids

This file defines the type of morphisms `StarMonoidHom` between monoids `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms are star-preserving monoid
homomorphisms and are equipped with the notation `A →⋆* B`.

The primary motivation for these morphisms is to provide a target type for morphisms which induce
a corresponding morphism between the unitary groups in a star monoid.

## Main definitions

  * `StarMonoidHom`
  * `StarMulEquiv`

## Tags

monoid, star
-/

variable {F A B C D : Type*}

/-! ### Star monoid homomorphisms -/

/-- A *star monoid homomorphism* is a monoid homomorphism which is `star`-preserving. -/
structure StarMonoidHom (A B : Type*) [Monoid A] [Star A] [Monoid B] [Star B]
    extends A →* B where
  /-- By definition, a star monoid homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆* β` denotes the type of star monoid homomorphisms from `α` to `β`. -/
infixr:25 " →⋆* " => StarMonoidHom

/-- Reinterpret a star monoid homomorphism as a monoid homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarMonoidHom.toMonoidHom

namespace StarMonoidHom

variable [Monoid A] [Star A] [Monoid B] [Star B]

instance : FunLike (A →⋆* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; simp_all

instance : MonoidHomClass (A →⋆* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance : StarHomClass (A →⋆* B) A B where
  map_star f := f.map_star'

/-- See Note [custom simps projection] -/
def Simps.coe (f : A →⋆* B) : A → B := f

initialize_simps_projections StarMonoidHom (toFun → coe)

/-- Construct a `StarMonoidHom` from a morphism in some type which preserves `1`, `*` and `star`. -/
@[simps]
def ofClass [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F) :
    A →⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
theorem coe_toMonoidHom (f : A →⋆* B) : ⇑f.toMonoidHom = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `StarMonoidHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆* B) (f' : A → B) (h : f' = f) : A →⋆* B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
theorem coe_copy (f : A →⋆* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : A →⋆* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_mk (f : A →* B) (h) :
    ((⟨f, h⟩ : A  →⋆* B) : A → B) = f :=
  rfl

section Id

variable (A)

/-- The identity as a star monoid homomorphism. -/
protected def id : A →⋆* A :=
  { (.id A : A →* A) with map_star' := fun _ ↦ rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(StarMonoidHom.id A) = id :=
  rfl

end Id

section Comp

variable [Monoid C] [Star C] [Monoid D] [Star D]

/-- The composition of star monoid homomorphisms, as a star monoid homomorphism. -/
def comp (f : B →⋆* C) (g : A →⋆* B) : A →⋆* C :=
  { f.toMonoidHom.comp g.toMonoidHom with
    map_star' := fun a => by simp [map_star] }

@[simp]
theorem coe_comp (f : B →⋆* C) (g : A →⋆* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆* C) (g : A →⋆* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆* D) (g : B →⋆* C) (h : A →⋆* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆* B) : (StarMonoidHom.id B).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆* B) : f.comp (.id _) = f :=
  ext fun _ => rfl

instance : Monoid (A →⋆* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := .id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : A →⋆* A) : A → A) = id :=
  rfl

theorem one_apply (a : A) : (1 : A →⋆* A) a = a :=
  rfl

end Comp

end StarMonoidHom


/-! ### Star monoid equivalences -/

/-- A *star monoid equivalence* is an equivalence preserving multiplication and the star
operation. -/
structure StarMulEquiv (A B : Type*) [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃* B where
  /-- By definition, a star monoid equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆* " B => StarMulEquiv A B

/-- Reinterpret a star monoid equivalence as a `MulEquiv` by forgetting the interaction with the
star operation. -/
add_decl_doc StarMulEquiv.toMulEquiv

namespace StarMulEquiv

section Basic

variable [Mul A] [Mul B] [Mul C] [Mul D]
variable [Star A] [Star B] [Star C] [Star D]

instance : EquivLike (A ≃⋆* B) A B where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

instance : MulEquivClass (A ≃⋆* B) A B where
  map_mul f := f.map_mul'

instance : StarHomClass (A ≃⋆* B) A B where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : A ≃⋆* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (A) in
/-- The identity map as a star monoid isomorphism. -/
@[refl]
protected def refl : A ≃⋆* A :=
  { MulEquiv.refl A with
    map_star' := fun _ => rfl }

instance : Inhabited (A ≃⋆* A) :=
  ⟨.refl A⟩

@[simp]
theorem coe_refl : ⇑(.refl A : A ≃⋆* A) = id :=
  rfl

/-- The inverse of a star monoid isomorphism is a star monoid isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆* B) : B ≃⋆* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [EquivLike.apply_inv_apply, EquivLike.inv_apply_apply] using
        congr_arg (EquivLike.inv e) (map_star e (EquivLike.inv e b)).symm }

/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃⋆* B) : A → B := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆* B) : B → A :=
  e.symm

initialize_simps_projections StarMulEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm {e : A ≃⋆* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃⋆* B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆* B) → B ≃⋆* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e := rfl

/-- Construct a `StarMulEquiv` from an equivalence in some type which preserves `*` and `star`. -/
@[simps]
def ofClass [EquivLike F A B] [MulEquivClass F A B] [StarHomClass F A B] (f : F) :
    A ≃⋆* B where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
theorem coe_toMulEquiv (f : A ≃⋆* B) : ⇑f.toMulEquiv = f :=
  rfl

@[simp]
theorem refl_symm : (.refl A : A ≃⋆* A).symm = .refl A :=
  rfl

/-- Transitivity of `StarMulEquiv`. -/
@[trans]
def trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : A ≃⋆* C :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }

@[simp]
theorem apply_symm_apply (e : A ≃⋆* B) : ∀ x, e (e.symm x) = x :=
  e.toMulEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃⋆* B) : ∀ x, e.symm (e x) = x :=
  e.toMulEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

theorem leftInverse_symm (e : A ≃⋆* B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃⋆* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic

section Bijective

variable [Monoid A] [Monoid B] [Star A] [Star B]

/-- If a star monoid morphism has an inverse, it is an isomorphism of star monoids. -/
@[simps]
def ofStarMonoidHom (f : A →⋆* B) (g : B →⋆* A) (h₁ : g.comp f = .id _) (h₂ : f.comp g = .id _) :
    A ≃⋆* B where
  toFun := f
  invFun := g
  left_inv := DFunLike.ext_iff.mp h₁
  right_inv := DFunLike.ext_iff.mp h₂
  map_mul' := map_mul f
  map_star' := map_star f

/-- Promote a bijective star monoid homomorphism to a star monoid equivalence. -/
noncomputable def ofBijective (f : A →⋆* B) (hf : Function.Bijective f) : A ≃⋆* B :=
  { MulEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
theorem coe_ofBijective {f : A →⋆* B} (hf : Function.Bijective f) :
    (StarMulEquiv.ofBijective f hf : A → B) = f :=
  rfl

theorem ofBijective_apply {f : A →⋆* B} (hf : Function.Bijective f) (a : A) :
    StarMulEquiv.ofBijective f hf a = f a :=
  rfl

end Bijective

end StarMulEquiv
