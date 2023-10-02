/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.FunLike.Basic

#align_import algebra.hom.group from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`MonoidHom` (resp., `AddMonoidHom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `ZeroHom`
* `OneHom`
* `AddHom`
* `MulHom`
* `MonoidWithZeroHom`

## Notations

* `→+`: Bundled `AddMonoid` homs. Also use for `AddGroup` homs.
* `→*`: Bundled `Monoid` homs. Also use for `Group` homs.
* `→*₀`: Bundled `MonoidWithZero` homs. Also use for `GroupWithZero` homs.
* `→ₙ*`: Bundled `Semigroup` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `GroupHom` -- the idea is that `MonoidHom` is used.
The constructor for `MonoidHom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `MonoidHom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `Deprecated/Group`.

## Tags

MonoidHom, AddMonoidHom

-/


variable {α β M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

-- homs
section Zero

/-- `ZeroHom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : ZeroHom M N)`,
you should parametrize over `(F : Type*) [ZeroHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `ZeroHomClass`.
-/
structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 0 -/
  protected map_zero' : toFun 0 = 0
#align zero_hom ZeroHom
#align zero_hom.map_zero' ZeroHom.map_zero'

/-- `ZeroHomClass F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `ZeroHom`.
-/
class ZeroHomClass (F : Type*) (M N : outParam (Type*)) [Zero M] [Zero N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves 0 -/
  map_zero : ∀ f : F, f 0 = 0
#align zero_hom_class ZeroHomClass
#align zero_hom_class.map_zero ZeroHomClass.map_zero

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

section Add

/-- `AddHom M N` is the type of functions `M → N` that preserve addition.

When possible, instead of parametrizing results over `(f : AddHom M N)`,
you should parametrize over `(F : Type*) [AddHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddHomClass`.
-/
structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves addition -/
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
#align add_hom AddHom

/-- `AddHomClass F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `AddHom`.
-/
class AddHomClass (F : Type*) (M N : outParam (Type*)) [Add M] [Add N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves addition -/
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y
#align add_hom_class AddHomClass

-- Instances and lemmas are defined below through `@[to_additive]`.
end Add

section add_zero

/-- `M →+ N` is the type of functions `M → N` that preserve the `AddZeroClass` structure.

`AddMonoidHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [AddMonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddMonoidHomClass`.
-/
structure AddMonoidHom (M : Type*) (N : Type*) [AddZeroClass M] [AddZeroClass N] extends
  ZeroHom M N, AddHom M N
#align add_monoid_hom AddMonoidHom

attribute [nolint docBlame] AddMonoidHom.toAddHom
attribute [nolint docBlame] AddMonoidHom.toZeroHom

/-- `M →+ N` denotes the type of additive monoid homomorphisms from `M` to `N`. -/
infixr:25 " →+ " => AddMonoidHom

/-- `AddMonoidHomClass F M N` states that `F` is a type of `AddZeroClass`-preserving
homomorphisms.

You should also extend this typeclass when you extend `AddMonoidHom`.
-/
class AddMonoidHomClass (F : Type*) (M N : outParam (Type*)) [AddZeroClass M] [AddZeroClass N]
  extends AddHomClass F M N, ZeroHomClass F M N
#align add_monoid_hom_class AddMonoidHomClass

-- Instances and lemmas are defined below through `@[to_additive]`.
end add_zero

section One

variable [One M] [One N]

/-- `OneHom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : OneHom M N)`,
you should parametrize over `(F : Type*) [OneHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `OneHomClass`.
-/
@[to_additive]
structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 1 -/
  protected map_one' : toFun 1 = 1
#align one_hom OneHom

/-- `OneHomClass F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `OneHom`.
-/
@[to_additive]
class OneHomClass (F : Type*) (M N : outParam (Type*)) [One M] [One N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves 1 -/
  map_one : ∀ f : F, f 1 = 1
#align one_hom_class OneHomClass

@[to_additive]
instance OneHom.oneHomClass : OneHomClass (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_one := OneHom.map_one'
#align one_hom.one_hom_class OneHom.oneHomClass
#align zero_hom.zero_hom_class ZeroHom.zeroHomClass

@[to_additive (attr := simp)]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f
#align map_one map_one
#align map_zero map_zero

/-- In principle this could be an instance, but in practice it causes performance issues. -/
@[to_additive]
theorem Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] :
    Subsingleton F where
  allEq f g := FunLike.ext _ _ fun x ↦ by simp [Subsingleton.elim x 1]

@[to_additive] instance [Subsingleton M] : Subsingleton (OneHom M N) := .of_oneHomClass

@[to_additive]
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f) {x : M} :
    f x = 1 ↔ x = 1 := hf.eq_iff' (map_one f)
#align map_eq_one_iff map_eq_one_iff
#align map_eq_zero_iff map_eq_zero_iff

@[to_additive]
theorem map_ne_one_iff {R S F : Type*} [One R] [One S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x ≠ 1 ↔ x ≠ 1 := (map_eq_one_iff f hf).not
#align map_ne_one_iff map_ne_one_iff
#align map_ne_zero_iff map_ne_zero_iff

@[to_additive]
theorem ne_one_of_map {R S F : Type*} [One R] [One S] [OneHomClass F R S] {f : F} {x : R}
    (hx : f x ≠ 1) : x ≠ 1 := ne_of_apply_ne f <| (by rwa [(map_one f)])
#align ne_one_of_map ne_one_of_map
#align ne_zero_of_map ne_zero_of_map

/-- Turn an element of a type `F` satisfying `OneHomClass F M N` into an actual
`OneHom`. This is declared as the default coercion from `F` to `OneHom M N`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `ZeroHomClass F M N` into an actual
`ZeroHom`. This is declared as the default coercion from `F` to `ZeroHom M N`."]
def OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := map_one f

/-- Any type satisfying `OneHomClass` can be cast into `OneHom` via `OneHomClass.toOneHom`. -/
@[to_additive "Any type satisfying `ZeroHomClass` can be cast into `ZeroHom` via
`ZeroHomClass.toZeroHom`. "]
instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) : ((f : OneHom M N) : M → N) = f := rfl
#align one_hom.coe_coe OneHom.coe_coe
#align zero_hom.coe_coe ZeroHom.coe_coe

end One

section Mul

variable [Mul M] [Mul N]

/-- `M →ₙ* N` is the type of functions `M → N` that preserve multiplication. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `NonUnitalAlgHom` and
`NonUnitalRingHom`, so a `MulHom` is a non-unital monoid hom.

When possible, instead of parametrizing results over `(f : M →ₙ* N)`,
you should parametrize over `(F : Type*) [MulHomClass F M N] (f : F)`.
When you extend this structure, make sure to extend `MulHomClass`.
-/
@[to_additive]
structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves multiplication -/
  protected map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
#align mul_hom MulHom

/-- `M →ₙ* N` denotes the type of multiplication-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ* " => MulHom

/-- `MulHomClass F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `MulHom`.
-/
@[to_additive]
class MulHomClass (F : Type*) (M N : outParam (Type*)) [Mul M] [Mul N]
  extends FunLike F M fun _ => N where
  /-- The proposition that the function preserves multiplication -/
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y
#align mul_hom_class MulHomClass

/-- `MulHom` is a type of multiplication-preserving homomorphisms -/
@[to_additive "`AddHom` is a type of addition-preserving homomorphisms"]
instance MulHom.mulHomClass : MulHomClass (M →ₙ* N) M N where
  coe := MulHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_mul := MulHom.map_mul'
#align mul_hom.mul_hom_class MulHom.mulHomClass
#align add_hom.add_hom_class AddHom.addHomClass

@[to_additive (attr := simp)]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y
#align map_mul map_mul
#align map_add map_add

/-- Turn an element of a type `F` satisfying `MulHomClass F M N` into an actual
`MulHom`. This is declared as the default coercion from `F` to `M →ₙ* N`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `AddHomClass F M N` into an actual
`AddHom`. This is declared as the default coercion from `F` to `M →ₙ+ N`."]
def MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M →ₙ* N where
  toFun := f
  map_mul' := map_mul f

/-- Any type satisfying `MulHomClass` can be cast into `MulHom` via `MulHomClass.toMulHom`. -/
@[to_additive "Any type satisfying `AddHomClass` can be cast into `AddHom` via
`AddHomClass.toAddHom`."]
instance [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]
theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M → N) = f := rfl
#align mul_hom.coe_coe MulHom.coe_coe
#align add_hom.coe_coe AddHom.coe_coe

end Mul

section mul_one

variable [MulOneClass M] [MulOneClass N]

/-- `M →* N` is the type of functions `M → N` that preserve the `Monoid` structure.
`MonoidHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [MonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `MonoidHomClass`.
-/
@[to_additive]
structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N
#align monoid_hom MonoidHom
-- Porting note: remove once `to_additive` is updated
-- This is waiting on https://github.com/leanprover-community/mathlib4/issues/660
attribute [to_additive existing] MonoidHom.toMulHom

attribute [nolint docBlame] MonoidHom.toMulHom
attribute [nolint docBlame] MonoidHom.toOneHom

/-- `M →* N` denotes the type of monoid homomorphisms from `M` to `N`. -/
infixr:25 " →* " => MonoidHom

/-- `MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `MonoidHom`. -/
@[to_additive]
class MonoidHomClass (F : Type*) (M N : outParam (Type*)) [MulOneClass M] [MulOneClass N]
  extends MulHomClass F M N, OneHomClass F M N
#align monoid_hom_class MonoidHomClass

@[to_additive]
instance MonoidHom.monoidHomClass : MonoidHomClass (M →* N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply FunLike.coe_injective'
    exact h
  map_mul := MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'
#align monoid_hom.monoid_hom_class MonoidHom.monoidHomClass
#align add_monoid_hom.add_monoid_hom_class AddMonoidHom.addMonoidHomClass

-- Porting note: we need to add an extra `to_additive`.
-- This is waiting on https://github.com/leanprover-community/mathlib4/issues/660
attribute [to_additive existing] MonoidHomClass.toOneHomClass

@[to_additive] instance [Subsingleton M] : Subsingleton (M →* N) := .of_oneHomClass

/-- Turn an element of a type `F` satisfying `MonoidHomClass F M N` into an actual
`MonoidHom`. This is declared as the default coercion from `F` to `M →* N`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `AddMonoidHomClass F M N` into an
actual `MonoidHom`. This is declared as the default coercion from `F` to `M →+ N`."]
def MonoidHomClass.toMonoidHom [MonoidHomClass F M N] (f : F) : M →* N :=
  { (f : M →ₙ* N), (f : OneHom M N) with }

/-- Any type satisfying `MonoidHomClass` can be cast into `MonoidHom` via
`MonoidHomClass.toMonoidHom`. -/
@[to_additive "Any type satisfying `AddMonoidHomClass` can be cast into `AddMonoidHom` via
`AddMonoidHomClass.toAddMonoidHom`."]
instance [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]
theorem MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M →* N) : M → N) = f := rfl
#align monoid_hom.coe_coe MonoidHom.coe_coe
#align add_monoid_hom.coe_coe AddMonoidHom.coe_coe

@[to_additive]
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) : f a * f b = 1 :=
  by rw [← map_mul, h, map_one]
#align map_mul_eq_one map_mul_eq_one
#align map_add_eq_zero map_add_eq_zero

@[to_additive]
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, hf]
#align map_div' map_div'
#align map_sub' map_sub'

/-- Group homomorphisms preserve inverse. -/
@[to_additive (attr := simp) "Additive group homomorphisms preserve negation."]
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| map_mul_eq_one f <| inv_mul_self _
#align map_inv map_inv
#align map_neg map_neg

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
theorem map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G) :
    f (a * b⁻¹) = f a * (f b)⁻¹ := by rw [map_mul, map_inv]
#align map_mul_inv map_mul_inv
#align map_add_neg map_add_neg

/-- Group homomorphisms preserve division. -/
@[to_additive (attr := simp) "Additive group homomorphisms preserve subtraction."]
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b := map_div' _ <| map_inv f
#align map_div map_div
#align map_sub map_sub

@[to_additive (attr := simp) (reorder := 8 9)]
theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow f a n]
#align map_pow map_pow
#align map_nsmul map_nsmul

@[to_additive]
theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by rw [zpow_ofNat, map_pow, zpow_ofNat]
  | Int.negSucc n => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc, ← zpow_negSucc]
#align map_zpow' map_zpow'
#align map_zsmul' map_zsmul'

/-- Group homomorphisms preserve integer power. -/
@[to_additive (attr := simp) (reorder := 8 9)
"Additive group homomorphisms preserve integer scaling."]
theorem map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n := map_zpow' f (map_inv f) g n
#align map_zpow map_zpow
#align map_zsmul map_zsmul

end mul_one

section MulZeroOne

variable [MulZeroOneClass M] [MulZeroOneClass N]

/-- `M →*₀ N` is the type of functions `M → N` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →*₀ N)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`.
-/
structure MonoidWithZeroHom (M : Type*) (N : Type*)
  [MulZeroOneClass M] [MulZeroOneClass N] extends ZeroHom M N, MonoidHom M N
#align monoid_with_zero_hom MonoidWithZeroHom

attribute [nolint docBlame] MonoidWithZeroHom.toMonoidHom
attribute [nolint docBlame] MonoidWithZeroHom.toZeroHom

/-- `M →*₀ N` denotes the type of zero-preserving monoid homomorphisms from `M` to `N`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom

/-- `MonoidWithZeroHomClass F M N` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`.
-/
class MonoidWithZeroHomClass (F : Type*) (M N : outParam (Type*)) [MulZeroOneClass M]
  [MulZeroOneClass N] extends MonoidHomClass F M N, ZeroHomClass F M N
#align monoid_with_zero_hom_class MonoidWithZeroHomClass

instance MonoidWithZeroHom.monoidWithZeroHomClass : MonoidWithZeroHomClass (M →*₀ N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply FunLike.coe_injective'
    exact h
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'
#align monoid_with_zero_hom.monoid_with_zero_hom_class MonoidWithZeroHom.monoidWithZeroHomClass

instance [Subsingleton M] : Subsingleton (M →*₀ N) := .of_oneHomClass

/-- Turn an element of a type `F` satisfying `MonoidWithZeroHomClass F M N` into an actual
`MonoidWithZeroHom`. This is declared as the default coercion from `F` to `M →*₀ N`. -/
@[coe]
def MonoidWithZeroHomClass.toMonoidWithZeroHom [MonoidWithZeroHomClass F M N] (f : F) : M →*₀ N :=
  { (f : M →* N), (f : ZeroHom M N) with }

/-- Any type satisfying `MonoidWithZeroHomClass` can be cast into `MonoidWithZeroHom` via
`MonoidWithZeroHomClass.toMonoidWithZeroHom`. -/
instance [MonoidWithZeroHomClass F M N] : CoeTC F (M →*₀ N) :=
  ⟨MonoidWithZeroHomClass.toMonoidWithZeroHom⟩

@[simp]
theorem MonoidWithZeroHom.coe_coe [MonoidWithZeroHomClass F M N] (f : F) :
    ((f : M →*₀ N) : M → N) = f := rfl
#align monoid_with_zero_hom.coe_coe MonoidWithZeroHom.coe_coe

end MulZeroOne

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] MonoidHom.toOneHom
attribute [coe] AddMonoidHom.toZeroHom

/-- `MonoidHom` down-cast to a `OneHom`, forgetting the multiplicative property. -/
@[to_additive "`AddMonoidHom` down-cast to a `ZeroHom`, forgetting the additive property"]
instance MonoidHom.coeToOneHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (OneHom M N) := ⟨MonoidHom.toOneHom⟩
#align monoid_hom.has_coe_to_one_hom MonoidHom.coeToOneHom
#align add_monoid_hom.has_coe_to_zero_hom AddMonoidHom.coeToZeroHom

attribute [coe] MonoidHom.toMulHom
attribute [coe] AddMonoidHom.toAddHom

/-- `MonoidHom` down-cast to a `MulHom`, forgetting the 1-preserving property. -/
@[to_additive "`AddMonoidHom` down-cast to an `AddHom`, forgetting the 0-preserving property."]
instance MonoidHom.coeToMulHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (M →ₙ* N) := ⟨MonoidHom.toMulHom⟩
#align monoid_hom.has_coe_to_mul_hom MonoidHom.coeToMulHom
#align add_monoid_hom.has_coe_to_add_hom AddMonoidHom.coeToAddHom

attribute [coe] MonoidWithZeroHom.toMonoidHom

/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
instance MonoidWithZeroHom.coeToMonoidHom [MulZeroOneClass M] [MulZeroOneClass N] :
  Coe (M →*₀ N) (M →* N) := ⟨MonoidWithZeroHom.toMonoidHom⟩
#align monoid_with_zero_hom.has_coe_to_monoid_hom MonoidWithZeroHom.coeToMonoidHom

attribute [coe] MonoidWithZeroHom.toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
instance MonoidWithZeroHom.coeToZeroHom [MulZeroOneClass M] [MulZeroOneClass N] :
  Coe (M →*₀ N) (ZeroHom M N) := ⟨MonoidWithZeroHom.toZeroHom⟩
#align monoid_with_zero_hom.has_coe_to_zero_hom MonoidWithZeroHom.coeToZeroHom

-- these must come after the coe_toFun definitions
initialize_simps_projections ZeroHom (toFun → apply)
initialize_simps_projections AddHom (toFun → apply)
initialize_simps_projections AddMonoidHom (toFun → apply)
initialize_simps_projections OneHom (toFun → apply)
initialize_simps_projections MulHom (toFun → apply)
initialize_simps_projections MonoidHom (toFun → apply)
initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[to_additive (attr := simp)]
theorem OneHom.coe_mk [One M] [One N] (f : M → N) (h1) : (OneHom.mk f h1 : M → N) = f := rfl
#align one_hom.coe_mk OneHom.coe_mk
#align zero_hom.coe_mk ZeroHom.coe_mk

@[to_additive (attr := simp)]
theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f := rfl
#align one_hom.to_fun_eq_coe OneHom.toFun_eq_coe
#align zero_hom.to_fun_eq_coe ZeroHom.toFun_eq_coe

@[to_additive (attr := simp)]
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) (hmul) : (MulHom.mk f hmul : M → N) = f := rfl
#align mul_hom.coe_mk MulHom.coe_mk
#align add_hom.coe_mk AddHom.coe_mk

@[to_additive (attr := simp)]
theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M →ₙ* N) : f.toFun = f := rfl
#align mul_hom.to_fun_eq_coe MulHom.toFun_eq_coe
#align add_hom.to_fun_eq_coe AddHom.toFun_eq_coe

@[to_additive (attr := simp)]
theorem MonoidHom.coe_mk [MulOneClass M] [MulOneClass N] (f hmul) :
    (MonoidHom.mk f hmul : M → N) = f := rfl
#align monoid_hom.coe_mk MonoidHom.coe_mk
#align add_monoid_hom.coe_mk AddMonoidHom.coe_mk

@[to_additive (attr := simp)]
theorem MonoidHom.toOneHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (f.toOneHom : M → N) = f := rfl
#align monoid_hom.to_one_hom_coe MonoidHom.toOneHom_coe
#align add_monoid_hom.to_zero_hom_coe AddMonoidHom.toZeroHom_coe

@[to_additive (attr := simp)]
theorem MonoidHom.toMulHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    f.toMulHom.toFun = f := rfl
#align monoid_hom.to_mul_hom_coe MonoidHom.toMulHom_coe
#align add_monoid_hom.to_add_hom_coe AddMonoidHom.toAddHom_coe

@[to_additive]
theorem MonoidHom.toFun_eq_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : f.toFun = f := rfl
#align monoid_hom.to_fun_eq_coe MonoidHom.toFun_eq_coe
#align add_monoid_hom.to_fun_eq_coe AddMonoidHom.toFun_eq_coe

@[simp]
theorem MonoidWithZeroHom.coe_mk [MulZeroOneClass M] [MulZeroOneClass N] (f h1 hmul) :
    (MonoidWithZeroHom.mk f h1 hmul : M → N) = (f : M → N) := rfl
#align monoid_with_zero_hom.coe_mk MonoidWithZeroHom.coe_mk

@[simp]
theorem MonoidWithZeroHom.toZeroHom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    (f.toZeroHom : M → N) = f := rfl
#align monoid_with_zero_hom.to_zero_hom_coe MonoidWithZeroHom.toZeroHom_coe

theorem MonoidWithZeroHom.toMonoidHom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f.toMonoidHom.toFun = f := rfl
#align monoid_with_zero_hom.to_monoid_hom_coe MonoidWithZeroHom.toMonoidHom_coe

@[to_additive (attr := ext)]
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align one_hom.ext OneHom.ext
#align zero_hom.ext ZeroHom.ext

@[to_additive (attr := ext)]
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align mul_hom.ext MulHom.ext
#align add_hom.ext AddHom.ext

@[to_additive (attr := ext)]
theorem MonoidHom.ext [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align monoid_hom.ext MonoidHom.ext
#align add_monoid_hom.ext AddMonoidHom.ext

@[ext]
theorem MonoidWithZeroHom.ext [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : M →*₀ N⦄
    (h : ∀ x, f x = g x) : f = g := FunLike.ext _ _ h
#align monoid_with_zero_hom.ext MonoidWithZeroHom.ext


namespace MonoidHom

variable [Group G]
variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive (attr := simps (config := .asFn))
  "Makes an additive group homomorphism from a proof that the map preserves addition."]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]
#align monoid_hom.mk' MonoidHom.mk'
#align add_monoid_hom.mk' AddMonoidHom.mk'
#align add_monoid_hom.mk'_apply AddMonoidHom.mk'_apply
#align monoid_hom.mk'_apply MonoidHom.mk'_apply

end MonoidHom

section Deprecated

/-- Deprecated: use `FunLike.congr_fun` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_fun` instead."]
theorem OneHom.congr_fun [One M] [One N] {f g : OneHom M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align one_hom.congr_fun OneHom.congr_fun
#align zero_hom.congr_fun ZeroHom.congr_fun

/-- Deprecated: use `FunLike.congr_fun` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_fun` instead."]
theorem MulHom.congr_fun [Mul M] [Mul N] {f g : M →ₙ* N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align mul_hom.congr_fun MulHom.congr_fun
#align add_hom.congr_fun AddHom.congr_fun

/-- Deprecated: use `FunLike.congr_fun` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_fun` instead."]
theorem MonoidHom.congr_fun [MulOneClass M] [MulOneClass N] {f g : M →* N} (h : f = g) (x : M) :
    f x = g x := FunLike.congr_fun h x
#align monoid_hom.congr_fun MonoidHom.congr_fun
#align add_monoid_hom.congr_fun AddMonoidHom.congr_fun

/-- Deprecated: use `FunLike.congr_fun` instead. -/
@[deprecated]
theorem MonoidWithZeroHom.congr_fun [MulZeroOneClass M] [MulZeroOneClass N] {f g : M →*₀ N}
    (h : f = g) (x : M) : f x = g x := FunLike.congr_fun h x
#align monoid_with_zero_hom.congr_fun MonoidWithZeroHom.congr_fun

/-- Deprecated: use `FunLike.congr_arg` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_arg` instead."]
theorem OneHom.congr_arg [One M] [One N] (f : OneHom M N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align one_hom.congr_arg OneHom.congr_arg
#align zero_hom.congr_arg ZeroHom.congr_arg

/-- Deprecated: use `FunLike.congr_arg` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_arg` instead."]
theorem MulHom.congr_arg [Mul M] [Mul N] (f : M →ₙ* N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align mul_hom.congr_arg MulHom.congr_arg
#align add_hom.congr_arg AddHom.congr_arg

/-- Deprecated: use `FunLike.congr_arg` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.congr_arg` instead."]
theorem MonoidHom.congr_arg [MulOneClass M] [MulOneClass N] (f : M →* N) {x y : M} (h : x = y) :
    f x = f y := FunLike.congr_arg f h
#align monoid_hom.congr_arg MonoidHom.congr_arg
#align add_monoid_hom.congr_arg AddMonoidHom.congr_arg

/-- Deprecated: use `FunLike.congr_arg` instead. -/
@[deprecated]
theorem MonoidWithZeroHom.congr_arg [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) {x y : M}
    (h : x = y) : f x = f y := FunLike.congr_arg f h
#align monoid_with_zero_hom.congr_arg MonoidWithZeroHom.congr_arg

/-- Deprecated: use `FunLike.coe_injective` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.coe_injective` instead."]
theorem OneHom.coe_inj [One M] [One N] ⦃f g : OneHom M N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h
#align one_hom.coe_inj OneHom.coe_inj
#align zero_hom.coe_inj ZeroHom.coe_inj

/-- Deprecated: use `FunLike.coe_injective` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.coe_injective` instead."]
theorem MulHom.coe_inj [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h
#align mul_hom.coe_inj MulHom.coe_inj
#align add_hom.coe_inj AddHom.coe_inj

/-- Deprecated: use `FunLike.coe_injective` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.coe_injective` instead."]
theorem MonoidHom.coe_inj [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : (f : M → N) = g) :
    f = g := FunLike.coe_injective h
#align monoid_hom.coe_inj MonoidHom.coe_inj
#align add_monoid_hom.coe_inj AddMonoidHom.coe_inj

/-- Deprecated: use `FunLike.coe_injective` instead. -/
@[deprecated]
theorem MonoidWithZeroHom.coe_inj [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : M →*₀ N⦄
    (h : (f : M → N) = g) : f = g := FunLike.coe_injective h
#align monoid_with_zero_hom.coe_inj MonoidWithZeroHom.coe_inj

/-- Deprecated: use `FunLike.ext_iff` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.ext_iff` instead."]
theorem OneHom.ext_iff [One M] [One N] {f g : OneHom M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align one_hom.ext_iff OneHom.ext_iff
#align zero_hom.ext_iff ZeroHom.ext_iff

/-- Deprecated: use `FunLike.ext_iff` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.ext_iff` instead."]
theorem MulHom.ext_iff [Mul M] [Mul N] {f g : M →ₙ* N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_hom.ext_iff MulHom.ext_iff
#align add_hom.ext_iff AddHom.ext_iff

/-- Deprecated: use `FunLike.ext_iff` instead. -/
@[to_additive (attr := deprecated) "Deprecated: use `FunLike.ext_iff` instead."]
theorem MonoidHom.ext_iff [MulOneClass M] [MulOneClass N] {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align monoid_hom.ext_iff MonoidHom.ext_iff
#align add_monoid_hom.ext_iff AddMonoidHom.ext_iff

/-- Deprecated: use `FunLike.ext_iff` instead. -/
@[deprecated]
theorem MonoidWithZeroHom.ext_iff [MulZeroOneClass M] [MulZeroOneClass N] {f g : M →*₀ N} :
    f = g ↔ ∀ x, f x = g x := FunLike.ext_iff
#align monoid_with_zero_hom.ext_iff MonoidWithZeroHom.ext_iff

end Deprecated

@[to_additive (attr := simp)]
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl
#align one_hom.mk_coe OneHom.mk_coe
#align zero_hom.mk_coe ZeroHom.mk_coe

@[to_additive (attr := simp)]
theorem MulHom.mk_coe [Mul M] [Mul N] (f : M →ₙ* N) (hmul) : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl
#align mul_hom.mk_coe MulHom.mk_coe
#align add_hom.mk_coe AddHom.mk_coe

@[to_additive (attr := simp)]
theorem MonoidHom.mk_coe [MulOneClass M] [MulOneClass N] (f : M →* N) (hmul) :
    MonoidHom.mk f hmul = f := MonoidHom.ext fun _ => rfl
#align monoid_hom.mk_coe MonoidHom.mk_coe
#align add_monoid_hom.mk_coe AddMonoidHom.mk_coe

@[simp]
theorem MonoidWithZeroHom.mk_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) (h1 hmul) :
    MonoidWithZeroHom.mk f h1 hmul = f := MonoidWithZeroHom.ext fun _ => rfl
#align monoid_with_zero_hom.mk_coe MonoidWithZeroHom.mk_coe

end Coes

/-- Copy of a `OneHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  "Copy of a `ZeroHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities."]
protected def OneHom.copy [One M] [One N] (f : OneHom M N) (f' : M → N) (h : f' = f) :
    OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'
#align one_hom.copy OneHom.copy
#align zero_hom.copy ZeroHom.copy

@[to_additive (attr := simp)]
theorem OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl
#align one_hom.coe_copy OneHom.coe_copy
#align zero_hom.coe_copy ZeroHom.coe_copy

@[to_additive]
theorem OneHom.coe_copy_eq {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  FunLike.ext' h
#align one_hom.coe_copy_eq OneHom.coe_copy_eq
#align zero_hom.coe_copy_eq ZeroHom.coe_copy_eq

/-- Copy of a `MulHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  "Copy of an `AddHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities."]
protected def MulHom.copy [Mul M] [Mul N] (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    M →ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'
#align mul_hom.copy MulHom.copy
#align add_hom.copy AddHom.copy

@[to_additive (attr := simp)]
theorem MulHom.coe_copy {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl
#align mul_hom.coe_copy MulHom.coe_copy
#align add_hom.coe_copy AddHom.coe_copy

@[to_additive]
theorem MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  FunLike.ext' h
#align mul_hom.coe_copy_eq MulHom.coe_copy_eq
#align add_hom.coe_copy_eq AddHom.coe_copy_eq

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
  "Copy of an `AddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities."]
protected def MonoidHom.copy [MulOneClass M] [MulOneClass N] (f : M →* N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }
#align monoid_hom.copy MonoidHom.copy
#align add_monoid_hom.copy AddMonoidHom.copy

@[to_additive (attr := simp)]
theorem MonoidHom.coe_copy {_ : MulOneClass M} {_ : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : (f.copy f' h) = f' :=
  rfl
#align monoid_hom.coe_copy MonoidHom.coe_copy
#align add_monoid_hom.coe_copy AddMonoidHom.coe_copy

@[to_additive]
theorem MonoidHom.copy_eq {_ : MulOneClass M} {_ : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align monoid_hom.copy_eq MonoidHom.copy_eq
#align add_monoid_hom.copy_eq AddMonoidHom.copy_eq

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def MonoidWithZeroHom.copy [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : M →* N :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }
#align monoid_with_zero_hom.copy MonoidWithZeroHom.copy

@[simp]
theorem MonoidWithZeroHom.coe_copy {_ : MulZeroOneClass M} {_ : MulZeroOneClass N} (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : (f.copy f' h) = f' :=
  rfl
#align monoid_with_zero_hom.coe_copy MonoidWithZeroHom.coe_copy

theorem MonoidWithZeroHom.copy_eq {_ : MulZeroOneClass M} {_ : MulZeroOneClass N} (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align monoid_with_zero_hom.copy_eq MonoidWithZeroHom.copy_eq

@[to_additive]
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'
#align one_hom.map_one OneHom.map_one
#align zero_hom.map_zero ZeroHom.map_zero

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive]
protected theorem MonoidHom.map_one [MulOneClass M] [MulOneClass N] (f : M →* N) : f 1 = 1 :=
  f.map_one'
#align monoid_hom.map_one MonoidHom.map_one
#align add_monoid_hom.map_zero AddMonoidHom.map_zero

protected theorem MonoidWithZeroHom.map_one [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f 1 = 1 := f.map_one'
#align monoid_with_zero_hom.map_one MonoidWithZeroHom.map_one

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc AddMonoidHom.map_zero

protected theorem MonoidWithZeroHom.map_zero [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f 0 = 0 := f.map_zero'
#align monoid_with_zero_hom.map_zero MonoidWithZeroHom.map_zero

@[to_additive]
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b
#align mul_hom.map_mul MulHom.map_mul
#align add_hom.map_add AddHom.map_add

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive]
protected theorem MonoidHom.map_mul [MulOneClass M] [MulOneClass N] (f : M →* N) (a b : M) :
    f (a * b) = f a * f b := f.map_mul' a b
#align monoid_hom.map_mul MonoidHom.map_mul
#align add_monoid_hom.map_add AddMonoidHom.map_add

protected theorem MonoidWithZeroHom.map_mul [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N)
    (a b : M) : f (a * b) = f a * f b := f.map_mul' a b
#align monoid_with_zero_hom.map_mul MonoidWithZeroHom.map_mul

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc AddMonoidHom.map_add

namespace MonoidHom

variable [MulOneClass M] [MulOneClass N] [MonoidHomClass F M N]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  "Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a right inverse, then `f x` has a right inverse too."]
theorem map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩
#align monoid_hom.map_exists_right_inv MonoidHom.map_exists_right_inv
#align add_monoid_hom.map_exists_right_neg AddMonoidHom.map_exists_right_neg

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  "Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
  `IsAddUnit.map`."]
theorem map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩
#align monoid_hom.map_exists_left_inv MonoidHom.map_exists_left_inv
#align add_monoid_hom.map_exists_left_neg AddMonoidHom.map_exists_left_neg

end MonoidHom

/-- The identity map from a type with 1 to itself. -/
@[to_additive (attr := simps)]
def OneHom.id (M : Type*) [One M] : OneHom M M where
  toFun x := x
  map_one' := rfl
#align one_hom.id OneHom.id
#align zero_hom.id ZeroHom.id
#align zero_hom.id_apply ZeroHom.id_apply
#align one_hom.id_apply OneHom.id_apply

/-- The identity map from a type with multiplication to itself. -/
@[to_additive (attr := simps)]
def MulHom.id (M : Type*) [Mul M] : M →ₙ* M where
  toFun x := x
  map_mul' _ _ := rfl
#align mul_hom.id MulHom.id
#align add_hom.id AddHom.id
#align add_hom.id_apply AddHom.id_apply
#align mul_hom.id_apply MulHom.id_apply

/-- The identity map from a monoid to itself. -/
@[to_additive (attr := simps)]
def MonoidHom.id (M : Type*) [MulOneClass M] : M →* M where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.id MonoidHom.id
#align add_monoid_hom.id AddMonoidHom.id
#align monoid_hom.id_apply MonoidHom.id_apply
#align add_monoid_hom.id_apply AddMonoidHom.id_apply

/-- The identity map from a `MonoidWithZero` to itself. -/
@[simps]
def MonoidWithZeroHom.id (M : Type*) [MulZeroOneClass M] : M →*₀ M where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_with_zero_hom.id MonoidWithZeroHom.id
#align monoid_with_zero_hom.id_apply MonoidWithZeroHom.id_apply

/-- The identity map from a type with zero to itself. -/
add_decl_doc ZeroHom.id

/-- The identity map from a type with addition to itself. -/
add_decl_doc AddHom.id

/-- The identity map from an additive monoid to itself. -/
add_decl_doc AddMonoidHom.id

/-- Composition of `OneHom`s as a `OneHom`. -/
@[to_additive]
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun := hnp ∘ hmn
  map_one' := by simp
#align one_hom.comp OneHom.comp
#align zero_hom.comp ZeroHom.comp

/-- Composition of `MulHom`s as a `MulHom`. -/
@[to_additive]
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
  toFun := hnp ∘ hmn
  map_mul' x y := by simp
#align mul_hom.comp MulHom.comp
#align add_hom.comp AddHom.comp

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive]
def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn
  map_one' := by simp
  map_mul' := by simp
#align monoid_hom.comp MonoidHom.comp
#align add_monoid_hom.comp AddMonoidHom.comp

/-- Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`. -/
def MonoidWithZeroHom.comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (hnp : N →*₀ P) (hmn : M →*₀ N) : M →*₀ P where
  toFun := hnp ∘ hmn
  map_zero' := by rw [Function.comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp
#align monoid_with_zero_hom.comp MonoidWithZeroHom.comp

/-- Composition of `ZeroHom`s as a `ZeroHom`. -/
add_decl_doc ZeroHom.comp

/-- Composition of `AddHom`s as an `AddHom`. -/
add_decl_doc AddHom.comp

/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc AddMonoidHom.comp

@[to_additive (attr := simp)]
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) :
    ↑(g.comp f) = g ∘ f := rfl
#align one_hom.coe_comp OneHom.coe_comp
#align zero_hom.coe_comp ZeroHom.coe_comp

@[to_additive (attr := simp)]
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) :
    ↑(g.comp f) = g ∘ f := rfl
#align mul_hom.coe_comp MulHom.coe_comp
#align add_hom.coe_comp AddHom.coe_comp

@[to_additive (attr := simp)]
theorem MonoidHom.coe_comp [MulOneClass M] [MulOneClass N] [MulOneClass P]
    (g : N →* P) (f : M →* N) : ↑(g.comp f) = g ∘ f := rfl
#align monoid_hom.coe_comp MonoidHom.coe_comp
#align add_monoid_hom.coe_comp AddMonoidHom.coe_comp

@[simp]
theorem MonoidWithZeroHom.coe_comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (g : N →*₀ P) (f : M →*₀ N) : ↑(g.comp f) = g ∘ f := rfl
#align monoid_with_zero_hom.coe_comp MonoidWithZeroHom.coe_comp

@[to_additive]
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) := rfl
#align one_hom.comp_apply OneHom.comp_apply
#align zero_hom.comp_apply ZeroHom.comp_apply

@[to_additive]
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
    g.comp f x = g (f x) := rfl
#align mul_hom.comp_apply MulHom.comp_apply
#align add_hom.comp_apply AddHom.comp_apply

@[to_additive]
theorem MonoidHom.comp_apply [MulOneClass M] [MulOneClass N] [MulOneClass P]
    (g : N →* P) (f : M →* N) (x : M) : g.comp f x = g (f x) := rfl
#align monoid_hom.comp_apply MonoidHom.comp_apply
#align add_monoid_hom.comp_apply AddMonoidHom.comp_apply

theorem MonoidWithZeroHom.comp_apply [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (g : N →*₀ P) (f : M →*₀ N) (x : M) : g.comp f x = g (f x) := rfl
#align monoid_with_zero_hom.comp_apply MonoidWithZeroHom.comp_apply

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive "Composition of additive monoid homomorphisms is associative."]
theorem OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q]
    (f : OneHom M N) (g : OneHom N P) (h : OneHom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
#align one_hom.comp_assoc OneHom.comp_assoc
#align zero_hom.comp_assoc ZeroHom.comp_assoc

@[to_additive]
theorem MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
    (f : M →ₙ* N) (g : N →ₙ* P) (h : P →ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) := rfl
#align mul_hom.comp_assoc MulHom.comp_assoc
#align add_hom.comp_assoc AddHom.comp_assoc

@[to_additive]
theorem MonoidHom.comp_assoc {Q : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P]
    [MulOneClass Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
#align monoid_hom.comp_assoc MonoidHom.comp_assoc
#align add_monoid_hom.comp_assoc AddMonoidHom.comp_assoc

theorem MonoidWithZeroHom.comp_assoc {Q : Type*} [MulZeroOneClass M] [MulZeroOneClass N]
    [MulZeroOneClass P] [MulZeroOneClass Q] (f : M →*₀ N) (g : N →*₀ P) (h : P →*₀ Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
#align monoid_with_zero_hom.comp_assoc MonoidWithZeroHom.comp_assoc

@[to_additive]
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext <| hf.forall.2 (FunLike.ext_iff.1 h), fun h => h ▸ rfl⟩
#align one_hom.cancel_right OneHom.cancel_right
#align zero_hom.cancel_right ZeroHom.cancel_right

@[to_additive]
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N →ₙ* P} {f : M →ₙ* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext <| hf.forall.2 (FunLike.ext_iff.1 h), fun h => h ▸ rfl⟩
#align mul_hom.cancel_right MulHom.cancel_right
#align add_hom.cancel_right AddHom.cancel_right

@[to_additive]
theorem MonoidHom.cancel_right [MulOneClass M] [MulOneClass N] [MulOneClass P]
    {g₁ g₂ : N →* P} {f : M →* N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext <| hf.forall.2 (FunLike.ext_iff.1 h), fun h => h ▸ rfl⟩
#align monoid_hom.cancel_right MonoidHom.cancel_right
#align add_monoid_hom.cancel_right AddMonoidHom.cancel_right

theorem MonoidWithZeroHom.cancel_right [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    {g₁ g₂ : N →*₀ P} {f : M →*₀ N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidWithZeroHom.ext <| hf.forall.2 (FunLike.ext_iff.1 h), fun h => h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_right MonoidWithZeroHom.cancel_right

@[to_additive]
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => OneHom.ext fun x => hg <| by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩
#align one_hom.cancel_left OneHom.cancel_left
#align zero_hom.cancel_left ZeroHom.cancel_left

@[to_additive]
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MulHom.ext fun x => hg <| by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩
#align mul_hom.cancel_left MulHom.cancel_left
#align add_hom.cancel_left AddHom.cancel_left

@[to_additive]
theorem MonoidHom.cancel_left [MulOneClass M] [MulOneClass N] [MulOneClass P]
    {g : N →* P} {f₁ f₂ : M →* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MonoidHom.ext fun x => hg <| by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩
#align monoid_hom.cancel_left MonoidHom.cancel_left
#align add_monoid_hom.cancel_left AddMonoidHom.cancel_left

theorem MonoidWithZeroHom.cancel_left [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    {g : N →*₀ P} {f₁ f₂ : M →*₀ N} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    MonoidWithZeroHom.ext fun x => hg <| by rw [← MonoidWithZeroHom.comp_apply, h,
    MonoidWithZeroHom.comp_apply], fun h => h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_left MonoidWithZeroHom.cancel_left

set_option linter.deprecated false in
section

@[to_additive]
theorem MonoidHom.toOneHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) :=
  fun _ _ h => MonoidHom.ext <| OneHom.ext_iff.mp h
#align monoid_hom.to_one_hom_injective MonoidHom.toOneHom_injective
#align add_monoid_hom.to_zero_hom_injective AddMonoidHom.toZeroHom_injective

@[to_additive]
theorem MonoidHom.toMulHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → M →ₙ* N) :=
  fun _ _ h => MonoidHom.ext <| MulHom.ext_iff.mp h
#align monoid_hom.to_mul_hom_injective MonoidHom.toMulHom_injective
#align add_monoid_hom.to_add_hom_injective AddMonoidHom.toAddHom_injective

theorem MonoidWithZeroHom.toMonoidHom_injective [MulZeroOneClass M] [MulZeroOneClass N] :
    Function.Injective (MonoidWithZeroHom.toMonoidHom : (M →*₀ N) → M →* N) :=
  fun _ _ h => MonoidWithZeroHom.ext <| MonoidHom.ext_iff.mp h
#align monoid_with_zero_hom.to_monoid_hom_injective MonoidWithZeroHom.toMonoidHom_injective

end

theorem MonoidWithZeroHom.toZeroHom_injective [MulZeroOneClass M] [MulZeroOneClass N] :
    Function.Injective (MonoidWithZeroHom.toZeroHom : (M →*₀ N) → ZeroHom M N) :=
  fun _ _ h => MonoidWithZeroHom.ext <| (FunLike.ext_iff (F := ZeroHom M N)).mp h
#align monoid_with_zero_hom.to_zero_hom_injective MonoidWithZeroHom.toZeroHom_injective

@[to_additive (attr := simp)]
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun _ => rfl
#align one_hom.comp_id OneHom.comp_id
#align zero_hom.comp_id ZeroHom.comp_id

@[to_additive (attr := simp)]
theorem MulHom.comp_id [Mul M] [Mul N] (f : M →ₙ* N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun _ => rfl
#align mul_hom.comp_id MulHom.comp_id
#align add_hom.comp_id AddHom.comp_id

@[to_additive (attr := simp)]
theorem MonoidHom.comp_id [MulOneClass M] [MulOneClass N] (f : M →* N) :
    f.comp (MonoidHom.id M) = f := MonoidHom.ext fun _ => rfl
#align monoid_hom.comp_id MonoidHom.comp_id
#align add_monoid_hom.comp_id AddMonoidHom.comp_id

@[simp]
theorem MonoidWithZeroHom.comp_id [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f.comp (MonoidWithZeroHom.id M) = f := MonoidWithZeroHom.ext fun _ => rfl
#align monoid_with_zero_hom.comp_id MonoidWithZeroHom.comp_id

@[to_additive (attr := simp)]
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun _ => rfl
#align one_hom.id_comp OneHom.id_comp
#align zero_hom.id_comp ZeroHom.id_comp

@[to_additive (attr := simp)]
theorem MulHom.id_comp [Mul M] [Mul N] (f : M →ₙ* N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun _ => rfl
#align mul_hom.id_comp MulHom.id_comp
#align add_hom.id_comp AddHom.id_comp

@[to_additive (attr := simp)]
theorem MonoidHom.id_comp [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (MonoidHom.id N).comp f = f := MonoidHom.ext fun _ => rfl
#align monoid_hom.id_comp MonoidHom.id_comp
#align add_monoid_hom.id_comp AddMonoidHom.id_comp

@[simp]
theorem MonoidWithZeroHom.id_comp [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    (MonoidWithZeroHom.id N).comp f = f := MonoidWithZeroHom.ext fun _ => rfl
#align monoid_with_zero_hom.id_comp MonoidWithZeroHom.id_comp

@[to_additive]
protected theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = f a ^ n := map_pow f a n
#align monoid_hom.map_pow MonoidHom.map_pow
#align add_monoid_hom.map_nsmul AddMonoidHom.map_nsmul

@[to_additive]
protected theorem MonoidHom.map_zpow' [DivInvMonoid M] [DivInvMonoid N] (f : M →* N)
    (hf : ∀ x, f x⁻¹ = (f x)⁻¹) (a : M) (n : ℤ) :
    f (a ^ n) = f a ^ n := map_zpow' f hf a n
#align monoid_hom.map_zpow' MonoidHom.map_zpow'
#align add_monoid_hom.map_zsmul' AddMonoidHom.map_zsmul'

section End

namespace Monoid

variable (M) [MulOneClass M]

/-- The monoid of endomorphisms. -/
protected def End := M →* M
#align monoid.End Monoid.End

namespace End

instance : Monoid (Monoid.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp

instance : Inhabited (Monoid.End M) := ⟨1⟩

instance : MonoidHomClass (Monoid.End M) M M := MonoidHom.monoidHomClass

end End

@[simp]
theorem coe_one : ((1 : Monoid.End M) : M → M) = id := rfl
#align monoid.coe_one Monoid.coe_one

@[simp]
theorem coe_mul (f g) : ((f * g : Monoid.End M) : M → M) = f ∘ g := rfl
#align monoid.coe_mul Monoid.coe_mul

end Monoid

namespace AddMonoid

variable (A : Type*) [AddZeroClass A]

/-- The monoid of endomorphisms. -/
protected def End := A →+ A
#align add_monoid.End AddMonoid.End

namespace End

instance monoid : Monoid (AddMonoid.End A) where
  mul := AddMonoidHom.comp
  one := AddMonoidHom.id A
  mul_assoc _ _ _ := AddMonoidHom.comp_assoc _ _ _
  mul_one := AddMonoidHom.comp_id
  one_mul := AddMonoidHom.id_comp

instance : Inhabited (AddMonoid.End A) := ⟨1⟩

instance : AddMonoidHomClass (AddMonoid.End A) A A := AddMonoidHom.addMonoidHomClass

end End

@[simp]
theorem coe_one : ((1 : AddMonoid.End A) : A → A) = id := rfl
#align add_monoid.coe_one AddMonoid.coe_one

@[simp]
theorem coe_mul (f g) : ((f * g : AddMonoid.End A) : A → A) = f ∘ g := rfl
#align add_monoid.coe_mul AddMonoid.coe_mul

end AddMonoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive "`0` is the homomorphism sending all elements to `0`."]
instance [One M] [One N] : One (OneHom M N) := ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive "`0` is the additive homomorphism sending all elements to `0`"]
instance [Mul M] [MulOneClass N] : One (M →ₙ* N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive "`0` is the additive monoid homomorphism sending all elements to `0`."]
instance [MulOneClass M] [MulOneClass N] : One (M →* N) :=
  ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

@[to_additive (attr := simp)]
theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 := rfl
#align one_hom.one_apply OneHom.one_apply
#align zero_hom.zero_apply ZeroHom.zero_apply

@[to_additive (attr := simp)]
theorem MonoidHom.one_apply [MulOneClass M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 := rfl
#align monoid_hom.one_apply MonoidHom.one_apply
#align add_monoid_hom.zero_apply AddMonoidHom.zero_apply

@[to_additive (attr := simp)]
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl
#align one_hom.one_comp OneHom.one_comp
#align zero_hom.zero_comp ZeroHom.zero_comp

@[to_additive (attr := simp)]
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [OneHom.map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]
#align one_hom.comp_one OneHom.comp_one
#align zero_hom.comp_zero ZeroHom.comp_zero

@[to_additive]
instance [One M] [One N] : Inhabited (OneHom M N) := ⟨1⟩

@[to_additive]
instance [Mul M] [MulOneClass N] : Inhabited (M →ₙ* N) := ⟨1⟩

@[to_additive]
instance [MulOneClass M] [MulOneClass N] : Inhabited (M →* N) := ⟨1⟩

-- unlike the other homs, `MonoidWithZeroHom` does not have a `1` or `0`
instance [MulZeroOneClass M] : Inhabited (M →*₀ M) := ⟨MonoidWithZeroHom.id M⟩

namespace MonoidHom

variable [Group G] [CommGroup H]

@[to_additive (attr := simp)]
theorem one_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 := rfl
#align monoid_hom.one_comp MonoidHom.one_comp
#align add_monoid_hom.zero_comp AddMonoidHom.zero_comp

@[to_additive (attr := simp)]
theorem comp_one [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]
#align monoid_hom.comp_one MonoidHom.comp_one
#align add_monoid_hom.comp_zero AddMonoidHom.comp_zero

/-- Group homomorphisms preserve inverse. -/
@[to_additive "Additive group homomorphisms preserve negation."]
protected theorem map_inv [Group α] [DivisionMonoid β] (f : α →* β) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f _
#align monoid_hom.map_inv MonoidHom.map_inv
#align add_monoid_hom.map_neg AddMonoidHom.map_neg

/-- Group homomorphisms preserve integer power. -/
@[to_additive "Additive group homomorphisms preserve integer scaling."]
protected theorem map_zpow [Group α] [DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ) :
    f (g ^ n) = f g ^ n := map_zpow f g n
#align monoid_hom.map_zpow MonoidHom.map_zpow
#align add_monoid_hom.map_zsmul AddMonoidHom.map_zsmul

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_div [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g / h) = f g / f h := map_div f g h
#align monoid_hom.map_div MonoidHom.map_div
#align add_monoid_hom.map_sub AddMonoidHom.map_sub

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ := by simp
#align monoid_hom.map_mul_inv MonoidHom.map_mul_inv
#align add_monoid_hom.map_add_neg AddMonoidHom.map_add_neg

end MonoidHom
