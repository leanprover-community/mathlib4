/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.NeZero

#align_import algebra.hom.group from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Monoid with zero and group with zero homomorphisms

This file defines homomorphisms of monoids with zero.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.


## Notations

* `→*₀`: `MonoidWithZeroHom`, the type of bundled `MonoidWithZero` homs. Also use for
  `GroupWithZero` homs.

## Implementation notes

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

monoid homomorphism
-/

assert_not_exists DenselyOrdered

open Function

namespace NeZero
variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

lemma of_map (f : F) [neZero : NeZero (f a)] : NeZero a :=
  ⟨fun h ↦ ne (f a) <| by rw [h]; exact ZeroHomClass.map_zero f⟩
#align ne_zero.of_map NeZero.of_map

lemma of_injective {f : F} (hf : Injective f) [NeZero a] : NeZero (f a) :=
  ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩
#align ne_zero.of_injective NeZero.of_injective

end NeZero

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

/-- `MonoidWithZeroHomClass F α β` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`. -/
class MonoidWithZeroHomClass (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
  [MulZeroOneClass β] [FunLike F α β] extends MonoidHomClass F α β, ZeroHomClass F α β : Prop
#align monoid_with_zero_hom_class MonoidWithZeroHomClass

/-- `α →*₀ β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*₀ β)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`. -/
structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β
#align monoid_with_zero_hom MonoidWithZeroHom

/-- `α →*₀ β` denotes the type of zero-preserving monoid homomorphisms from `α` to `β`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom

/-- Turn an element of a type `F` satisfying `MonoidWithZeroHomClass F α β` into an actual
`MonoidWithZeroHom`. This is declared as the default coercion from `F` to `α →*₀ β`. -/
@[coe]
def MonoidWithZeroHomClass.toMonoidWithZeroHom [FunLike F α β] [MonoidWithZeroHomClass F α β]
    (f : F) : α →*₀ β := { (f : α →* β), (f : ZeroHom α β) with }

/-- Any type satisfying `MonoidWithZeroHomClass` can be cast into `MonoidWithZeroHom` via
`MonoidWithZeroHomClass.toMonoidWithZeroHom`. -/
instance [FunLike F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀ β) :=
  ⟨MonoidWithZeroHomClass.toMonoidWithZeroHom⟩

namespace MonoidWithZeroHom

attribute [nolint docBlame] toMonoidHom
attribute [nolint docBlame] toZeroHom

instance funLike : FunLike (α →*₀ β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance monoidWithZeroHomClass : MonoidWithZeroHomClass (α →*₀ β) α β where
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'
#align monoid_with_zero_hom.monoid_with_zero_hom_class MonoidWithZeroHom.monoidWithZeroHomClass

instance [Subsingleton α] : Subsingleton (α →*₀ β) := .of_oneHomClass

variable [FunLike F α β]

@[simp] lemma coe_coe [MonoidWithZeroHomClass F α β] (f : F) : ((f : α →*₀ β) : α → β) = f := rfl
#align monoid_with_zero_hom.coe_coe MonoidWithZeroHom.coe_coe

-- Completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] toMonoidHom

/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
instance coeToMonoidHom : Coe (α →*₀ β) (α →* β) :=
  ⟨toMonoidHom⟩
#align monoid_with_zero_hom.has_coe_to_monoid_hom MonoidWithZeroHom.coeToMonoidHom

attribute [coe] toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
instance coeToZeroHom :
  Coe (α →*₀ β) (ZeroHom α β) := ⟨toZeroHom⟩
#align monoid_with_zero_hom.has_coe_to_zero_hom MonoidWithZeroHom.coeToZeroHom

-- This must come after the coe_toFun definitions
initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[simp] lemma coe_mk (f h1 hmul) : (mk f h1 hmul : α → β) = (f : α → β) := rfl
#align monoid_with_zero_hom.coe_mk MonoidWithZeroHom.coe_mk

@[simp] lemma toZeroHom_coe (f : α →*₀ β) : (f.toZeroHom : α → β) = f := rfl
#align monoid_with_zero_hom.to_zero_hom_coe MonoidWithZeroHom.toZeroHom_coe

lemma toMonoidHom_coe (f : α →*₀ β) : f.toMonoidHom.toFun = f := rfl
#align monoid_with_zero_hom.to_monoid_hom_coe MonoidWithZeroHom.toMonoidHom_coe

@[ext] lemma ext ⦃f g : α →*₀ β⦄ (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
#align monoid_with_zero_hom.ext MonoidWithZeroHom.ext

section Deprecated -- since 2022-12-03

@[deprecated DFunLike.congr_fun]
lemma congr_fun {f g : α →*₀ β} (h : f = g) (x : α) : f x = g x := DFunLike.congr_fun h x
#align monoid_with_zero_hom.congr_fun MonoidWithZeroHom.congr_fun

@[deprecated DFunLike.congr_arg]
lemma congr_arg (f : α →*₀ β) {x y : α} (h : x = y) : f x = f y := DFunLike.congr_arg f h
#align monoid_with_zero_hom.congr_arg MonoidWithZeroHom.congr_arg

@[deprecated DFunLike.coe_injective]
lemma coe_inj ⦃f g : α →*₀ β⦄ (h : (f : α → β) = g) : f = g := DFunLike.coe_injective h
#align monoid_with_zero_hom.coe_inj MonoidWithZeroHom.coe_inj

@[deprecated DFunLike.ext_iff]
lemma ext_iff {f g : α →*₀ β} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff
#align monoid_with_zero_hom.ext_iff MonoidWithZeroHom.ext_iff

end Deprecated

@[simp] lemma mk_coe (f : α →*₀ β) (h1 hmul) : mk f h1 hmul = f := ext fun _ ↦ rfl
#align monoid_with_zero_hom.mk_coe MonoidWithZeroHom.mk_coe

end Coes

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀ β) (f' : α → β) (h : f' = f) : α →* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }
#align monoid_with_zero_hom.copy MonoidWithZeroHom.copy

@[simp]
lemma coe_copy {_ : MulZeroOneClass α} {_ : MulZeroOneClass β} (f : α →*₀ β) (f' : α → β) (h) :
    (f.copy f' h) = f' := rfl
#align monoid_with_zero_hom.coe_copy MonoidWithZeroHom.coe_copy

lemma copy_eq {_ : MulZeroOneClass α} {_ : MulZeroOneClass β} (f : α →*₀ β) (f' : α → β) (h) :
    f.copy f' h = f := DFunLike.ext' h
#align monoid_with_zero_hom.copy_eq MonoidWithZeroHom.copy_eq

protected lemma map_one (f : α →*₀ β) : f 1 = 1 := f.map_one'
#align monoid_with_zero_hom.map_one MonoidWithZeroHom.map_one

protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'
#align monoid_with_zero_hom.map_zero MonoidWithZeroHom.map_zero

protected lemma map_mul (f : α →*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b
#align monoid_with_zero_hom.map_mul MonoidWithZeroHom.map_mul

/-- The identity map from a `MonoidWithZero` to itself. -/
@[simps]
def id (α : Type*) [MulZeroOneClass α] : α →*₀ α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_with_zero_hom.id MonoidWithZeroHom.id
#align monoid_with_zero_hom.id_apply MonoidWithZeroHom.id_apply

/-- Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`. -/
def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
  toFun := hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp
#align monoid_with_zero_hom.comp MonoidWithZeroHom.comp

@[simp] lemma coe_comp (g : β →*₀ γ) (f : α →*₀ β) : ↑(g.comp f) = g ∘ f := rfl
#align monoid_with_zero_hom.coe_comp MonoidWithZeroHom.coe_comp

lemma comp_apply (g : β →*₀ γ) (f : α →*₀ β) (x : α) : g.comp f x = g (f x) := rfl
#align monoid_with_zero_hom.comp_apply MonoidWithZeroHom.comp_apply

lemma comp_assoc (f : α →*₀ β) (g : β →*₀ γ) (h : γ →*₀ δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
#align monoid_with_zero_hom.comp_assoc MonoidWithZeroHom.comp_assoc

lemma cancel_right {g₁ g₂ : β →*₀ γ} {f : α →*₀ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext $ hf.forall.2 (DFunLike.ext_iff.1 h), fun h ↦ h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_right MonoidWithZeroHom.cancel_right

lemma cancel_left {g : β →*₀ γ} {f₁ f₂ : α →*₀ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun x ↦ hg $ by rw [← comp_apply, h,
    comp_apply], fun h ↦ h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_left MonoidWithZeroHom.cancel_left

set_option linter.deprecated false in
lemma toMonoidHom_injective : Injective (toMonoidHom : (α →*₀ β) → α →* β) :=
  fun _ _ h ↦ ext $ MonoidHom.ext_iff.mp h
#align monoid_with_zero_hom.to_monoid_hom_injective MonoidWithZeroHom.toMonoidHom_injective

lemma toZeroHom_injective : Injective (toZeroHom : (α →*₀ β) → ZeroHom α β) :=
  fun _ _ h ↦ ext $ (DFunLike.ext_iff (F := ZeroHom α β)).mp h
#align monoid_with_zero_hom.to_zero_hom_injective MonoidWithZeroHom.toZeroHom_injective

@[simp] lemma comp_id (f : α →*₀ β) : f.comp (id α) = f := ext fun _ ↦ rfl
#align monoid_with_zero_hom.comp_id MonoidWithZeroHom.comp_id

@[simp] lemma id_comp (f : α →*₀ β) : (id β).comp f = f := ext fun _ ↦ rfl
#align monoid_with_zero_hom.id_comp MonoidWithZeroHom.id_comp

-- Unlike the other homs, `MonoidWithZeroHom` does not have a `1` or `0`
instance : Inhabited (α →*₀ α) := ⟨id α⟩

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero, `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`. -/
instance {β} [CommMonoidWithZero β] : Mul (α →*₀ β) where
  mul f g :=
    { (f * g : α →* β) with
      map_zero' := by dsimp; rw [map_zero, zero_mul] }

end MonoidWithZeroHom

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
def powMonoidWithZeroHom : M₀ →*₀ M₀ :=
  { powMonoidHom n with map_zero' := zero_pow hn }
#align pow_monoid_with_zero_hom powMonoidWithZeroHom

@[simp] lemma coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M₀ → M₀) = fun x ↦ x ^ n := rfl
#align coe_pow_monoid_with_zero_hom coe_powMonoidWithZeroHom

@[simp] lemma powMonoidWithZeroHom_apply (a : M₀) : powMonoidWithZeroHom hn a = a ^ n := rfl
#align pow_monoid_with_zero_hom_apply powMonoidWithZeroHom_apply

end CommMonoidWithZero

/-! ### Equivalences -/

namespace MulEquivClass
variable {F α β : Type*} [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) toZeroHomClass [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero f :=
    calc
      f 0 = f 0 * f (EquivLike.inv f 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass with }
#align mul_equiv_class.to_monoid_with_zero_hom_class MulEquivClass.toMonoidWithZeroHomClass

end MulEquivClass
