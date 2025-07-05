/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.GroupWithZero.Basic

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

assert_not_exists DenselyOrdered Ring

open Function

namespace NeZero
variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

lemma of_map (f : F) [neZero : NeZero (f a)] : NeZero a :=
  ⟨fun h ↦ ne (f a) <| by rw [h]; exact ZeroHomClass.map_zero f⟩

lemma of_injective {f : F} (hf : Injective f) [NeZero a] : NeZero (f a) :=
  ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

end NeZero

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

/-- `MonoidWithZeroHomClass F α β` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`. -/
class MonoidWithZeroHomClass (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
    [MulZeroOneClass β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, ZeroHomClass F α β

/-- `α →*₀ β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*₀ β)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`. -/
structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β

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

instance [Subsingleton α] : Subsingleton (α →*₀ β) := .of_oneHomClass

variable [FunLike F α β]

@[simp] lemma coe_coe [MonoidWithZeroHomClass F α β] (f : F) : ((f : α →*₀ β) : α → β) = f := rfl

-- Completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] toMonoidHom

/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
instance coeToMonoidHom : Coe (α →*₀ β) (α →* β) :=
  ⟨toMonoidHom⟩

attribute [coe] toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
instance coeToZeroHom :
  Coe (α →*₀ β) (ZeroHom α β) := ⟨toZeroHom⟩

-- This must come after the coe_toFun definitions
initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[simp] lemma coe_mk (f h1 hmul) : (mk f h1 hmul : α → β) = (f : α → β) := rfl

@[simp] lemma toZeroHom_coe (f : α →*₀ β) : (f.toZeroHom : α → β) = f := rfl

lemma toMonoidHom_coe (f : α →*₀ β) : f.toMonoidHom.toFun = f := rfl

@[ext] lemma ext ⦃f g : α →*₀ β⦄ (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

@[simp] lemma mk_coe (f : α →*₀ β) (h1 hmul) : mk f h1 hmul = f := ext fun _ ↦ rfl

end Coes

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀ β) (f' : α → β) (h : f' = f) : α →* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[simp]
lemma coe_copy (f : α →*₀ β) (f' : α → β) (h) : (f.copy f' h) = f' := rfl

lemma copy_eq (f : α →*₀ β) (f' : α → β) (h) : f.copy f' h = f := DFunLike.ext' h

protected lemma map_one (f : α →*₀ β) : f 1 = 1 := f.map_one'

protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'

protected lemma map_mul (f : α →*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

@[simp]
theorem map_ite_zero_one {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp [h]

@[simp]
theorem map_ite_one_zero {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 1 0) = ite p 1 0 := by
  split_ifs with h <;> simp [h]

/-- The identity map from a `MonoidWithZero` to itself. -/
@[simps]
def id (α : Type*) [MulZeroOneClass α] : α →*₀ α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`. -/
def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
  toFun := hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp

@[simp] lemma coe_comp (g : β →*₀ γ) (f : α →*₀ β) : ↑(g.comp f) = g ∘ f := rfl

lemma comp_apply (g : β →*₀ γ) (f : α →*₀ β) (x : α) : g.comp f x = g (f x) := rfl

lemma comp_assoc (f : α →*₀ β) (g : β →*₀ γ) (h : γ →*₀ δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

lemma cancel_right {g₁ g₂ : β →*₀ γ} {f : α →*₀ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h ↦ h ▸ rfl⟩

lemma cancel_left {g : β →*₀ γ} {f₁ f₂ : α →*₀ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun x ↦ hg <| by rw [← comp_apply, h,
    comp_apply], fun h ↦ h ▸ rfl⟩

lemma toMonoidHom_injective : Injective (toMonoidHom : (α →*₀ β) → α →* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

lemma toZeroHom_injective : Injective (toZeroHom : (α →*₀ β) → ZeroHom α β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[simp] lemma comp_id (f : α →*₀ β) : f.comp (id α) = f := ext fun _ ↦ rfl

@[simp] lemma id_comp (f : α →*₀ β) : (id β).comp f = f := ext fun _ ↦ rfl

-- Unlike the other homs, `MonoidWithZeroHom` does not have a `1` or `0`
instance : Inhabited (α →*₀ α) := ⟨id α⟩

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero, `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`. -/
instance {β} [CommMonoidWithZero β] : Mul (α →*₀ β) where
  mul f g :=
    { (f * g : α →* β) with
      map_zero' := by dsimp; rw [map_zero, zero_mul] }

/-- The trivial homomorphism between monoids with zero, sending everything to 1 other than 0. -/
protected instance one (M₀ N₀ : Type*) [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    One (M₀ →*₀ N₀) where
  one.toFun x := if x = 0 then 0 else 1
  one.map_zero' := by simp
  one.map_one' := by simp
  one.map_mul' x y := by split_ifs <;> simp_all

@[simp]
lemma one_apply_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    (1 : M₀ →*₀ N₀) 0 = 0 :=
  if_pos rfl

lemma one_apply_of_ne_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] {x : M₀} (hx : x ≠ 0) :
    (1 : M₀ →*₀ N₀) x = 1 :=
  if_neg hx

end MonoidWithZeroHom

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
def powMonoidWithZeroHom : M₀ →*₀ M₀ :=
  { powMonoidHom n with map_zero' := zero_pow hn }

@[simp] lemma coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M₀ → M₀) = fun x ↦ x ^ n := rfl

@[simp] lemma powMonoidWithZeroHom_apply (a : M₀) : powMonoidWithZeroHom hn a = a ^ n := rfl

end CommMonoidWithZero
