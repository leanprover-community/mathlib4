/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Notation.Pi
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate

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

## Notations

* `→+`: Bundled `AddMonoid` homs. Also use for `AddGroup` homs.
* `→*`: Bundled `Monoid` homs. Also use for `Group` homs.
* `→ₙ+`: Bundled `AddSemigroup` homs.
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

open Function

variable {ι α β M N P : Type*}

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

/-- `ZeroHomClass F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `ZeroHom`.
-/
class ZeroHomClass (F : Type*) (M N : outParam Type*) [Zero M] [Zero N] [FunLike F M N] :
    Prop where
  /-- The proposition that the function preserves 0 -/
  map_zero : ∀ f : F, f 0 = 0

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

section Add

/-- `M →ₙ+ N` is the type of functions `M → N` that preserve addition. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `NonUnitalAlgHom` and
`NonUnitalRingHom`, so an `AddHom` is a non-unital additive monoid hom.

When possible, instead of parametrizing results over `(f : AddHom M N)`,
you should parametrize over `(F : Type*) [AddHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddHomClass`.
-/
structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves addition -/
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

/-- `M →ₙ+ N` denotes the type of addition-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ+ " => AddHom

/-- `AddHomClass F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `AddHom`.
-/
class AddHomClass (F : Type*) (M N : outParam Type*) [Add M] [Add N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves addition -/
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y

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

attribute [nolint docBlame] AddMonoidHom.toAddHom
attribute [nolint docBlame] AddMonoidHom.toZeroHom

/-- `M →+ N` denotes the type of additive monoid homomorphisms from `M` to `N`. -/
infixr:25 " →+ " => AddMonoidHom

/-- `AddMonoidHomClass F M N` states that `F` is a type of `AddZeroClass`-preserving
homomorphisms.

You should also extend this typeclass when you extend `AddMonoidHom`.
-/
class AddMonoidHomClass (F : Type*) (M N : outParam Type*)
    [AddZeroClass M] [AddZeroClass N] [FunLike F M N] : Prop
    extends AddHomClass F M N, ZeroHomClass F M N

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

/-- `OneHomClass F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `OneHom`.
-/
@[to_additive]
class OneHomClass (F : Type*) (M N : outParam Type*) [One M] [One N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves 1 -/
  map_one : ∀ f : F, f 1 = 1

@[to_additive]
instance OneHom.funLike : FunLike (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[to_additive]
instance OneHom.oneHomClass : OneHomClass (OneHom M N) M N where
  map_one := OneHom.map_one'

library_note "hom simp lemma priority"
/--
The hom class hierarchy allows for a single lemma, such as `map_one`, to apply to a large variety
of morphism types, so long as they have an instance of `OneHomClass`. For example, this applies to
to `MonoidHom`, `RingHom`, `AlgHom`, `StarAlgHom`, as well as their `Equiv` variants, etc. However,
precisely because these lemmas are so widely applicable, they keys in the `simp` discrimination tree
are necessarily highly non-specific. For example, the key for `map_one` is
`@DFunLike.coe _ _ _ _ _ 1`.

Consequently, whenever lean sees `⇑f 1`, for some `f : F`, it will attempt to synthesize a
`OneHomClass F ?A ?B` instance. If no such instance exists, then Lean will need to traverse (almost)
the entirety of the `FunLike` hierarchy in order to determine this because so many classes have a
`OneHomClass` instance (in fact, this problem is likely worse for `ZeroHomClass`). This can lead to
a significant performance hit when `map_one` fails to apply.

To avoid this problem, we mark these widely applicable simp lemmas with key discimination tree keys
with `mid` priority in order to ensure that they are not tried first.

We do not use `low`, to allow bundled morphisms to unfold themselves with `low` priority such that
the generic morphism lemmas are applied first. For instance, we might have
```lean
def fooMonoidHom : M →* N where
  toFun := foo; map_one' := sorry; map_mul' := sorry

@[simp low] lemma fooMonoidHom_apply (x : M) : fooMonoidHom x = foo x := rfl
```
As `map_mul` is tagged `simp mid`, this means that it still fires before `fooMonoidHom_apply`, which
is the behavior we desire.
-/

variable [FunLike F M N]

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid)]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f

@[to_additive] lemma map_comp_one [OneHomClass F M N] (f : F) : f ∘ (1 : ι → M) = 1 := by simp

/-- In principle this could be an instance, but in practice it causes performance issues. -/
@[to_additive]
theorem Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] :
    Subsingleton F where
  allEq f g := DFunLike.ext _ _ fun x ↦ by simp [Subsingleton.elim x 1]

@[to_additive] instance [Subsingleton M] : Subsingleton (OneHom M N) := .of_oneHomClass

@[to_additive]
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f)
    {x : M} :
    f x = 1 ↔ x = 1 := hf.eq_iff' (map_one f)

@[to_additive]
theorem map_ne_one_iff {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x ≠ 1 ↔ x ≠ 1 := (map_eq_one_iff f hf).not

@[to_additive]
theorem ne_one_of_map {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S]
    {f : F} {x : R} (hx : f x ≠ 1) : x ≠ 1 := ne_of_apply_ne f <| (by rwa [(map_one f)])

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
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) :
    ((f : OneHom M N) : M → N) = f := rfl

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

/-- `M →ₙ* N` denotes the type of multiplication-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ* " => MulHom

/-- `MulHomClass F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `MulHom`.
-/
@[to_additive]
class MulHomClass (F : Type*) (M N : outParam Type*) [Mul M] [Mul N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves multiplication -/
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

@[to_additive]
instance MulHom.funLike : FunLike (M →ₙ* N) M N where
  coe := MulHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- `MulHom` is a type of multiplication-preserving homomorphisms -/
@[to_additive "`AddHom` is a type of addition-preserving homomorphisms"]
instance MulHom.mulHomClass : MulHomClass (M →ₙ* N) M N where
  map_mul := MulHom.map_mul'

variable [FunLike F M N]

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid)]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

@[to_additive (attr := simp)]
lemma map_comp_mul [MulHomClass F M N] (f : F) (g h : ι → M) : f ∘ (g * h) = f ∘ g * f ∘ h := by
  ext; simp

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

end Mul

section mul_one

variable [MulOneClass M] [MulOneClass N]

/-- `M →* N` is the type of functions `M → N` that preserve the `Monoid` structure.
`MonoidHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →* N)`,
you should parametrize over `(F : Type*) [MonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `MonoidHomClass`.
-/
@[to_additive]
structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

attribute [nolint docBlame] MonoidHom.toMulHom
attribute [nolint docBlame] MonoidHom.toOneHom

/-- `M →* N` denotes the type of monoid homomorphisms from `M` to `N`. -/
infixr:25 " →* " => MonoidHom

/-- `MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `MonoidHom`. -/
@[to_additive]
class MonoidHomClass (F : Type*) (M N : outParam Type*) [MulOneClass M] [MulOneClass N]
  [FunLike F M N] : Prop
  extends MulHomClass F M N, OneHomClass F M N

@[to_additive]
instance MonoidHom.instFunLike : FunLike (M →* N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

@[to_additive]
instance MonoidHom.instMonoidHomClass : MonoidHomClass (M →* N) M N where
  map_mul := MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'

@[to_additive] instance [Subsingleton M] : Subsingleton (M →* N) := .of_oneHomClass

variable [FunLike F M N]

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

@[to_additive]
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) :
    f a * f b = 1 := by
  rw [← map_mul, h, map_one]

variable [FunLike F G H]

@[to_additive]
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
    (f : F) (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, hf]

@[to_additive]
lemma map_comp_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F)
    (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (g h : ι → G) : f ∘ (g / h) = f ∘ g / f ∘ h := by
  ext; simp [map_div' f hf]

/-- Group homomorphisms preserve inverse.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid) "Additive group homomorphisms preserve negation."]
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| map_mul_eq_one f <| inv_mul_cancel _

@[to_additive (attr := simp)]
lemma map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι → G) :
    f ∘ g⁻¹ = (f ∘ g)⁻¹ := by ext; simp

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
theorem map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G) :
    f (a * b⁻¹) = f a * (f b)⁻¹ := by rw [map_mul, map_inv]

@[to_additive]
lemma map_comp_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι → G) :
    f ∘ (g * h⁻¹) = f ∘ g * (f ∘ h)⁻¹ := by simp

/-- Group homomorphisms preserve division.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid) "Additive group homomorphisms preserve subtraction."]
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b := map_div' _ <| map_inv f

@[to_additive (attr := simp)]
lemma map_comp_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι → G) :
    f ∘ (g / h) = f ∘ g / f ∘ h := by ext; simp

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid) (reorder := 9 10)]
theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow f a n]

@[to_additive (attr := simp)]
lemma map_comp_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (g : ι → G) (n : ℕ) :
    f ∘ (g ^ n) = f ∘ g ^ n := by ext; simp

@[to_additive]
theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by rw [zpow_natCast, map_pow, zpow_natCast]
  | Int.negSucc n => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc]

@[to_additive (attr := simp)]
lemma map_comp_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
    (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (g : ι → G) (n : ℤ) : f ∘ (g ^ n) = f ∘ g ^ n := by
  ext; simp [map_zpow' f hf]

/-- Group homomorphisms preserve integer power.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid) (reorder := 9 10)
"Additive group homomorphisms preserve integer scaling."]
theorem map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n := map_zpow' f (map_inv f) g n

@[to_additive]
lemma map_comp_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι → G)
    (n : ℤ) : f ∘ (g ^ n) = f ∘ g ^ n := by simp

end mul_one

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] MonoidHom.toOneHom
attribute [coe] AddMonoidHom.toZeroHom

/-- `MonoidHom` down-cast to a `OneHom`, forgetting the multiplicative property. -/
@[to_additive "`AddMonoidHom` down-cast to a `ZeroHom`, forgetting the additive property"]
instance MonoidHom.coeToOneHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (OneHom M N) := ⟨MonoidHom.toOneHom⟩

attribute [coe] MonoidHom.toMulHom
attribute [coe] AddMonoidHom.toAddHom

/-- `MonoidHom` down-cast to a `MulHom`, forgetting the 1-preserving property. -/
@[to_additive "`AddMonoidHom` down-cast to an `AddHom`, forgetting the 0-preserving property."]
instance MonoidHom.coeToMulHom [MulOneClass M] [MulOneClass N] :
  Coe (M →* N) (M →ₙ* N) := ⟨MonoidHom.toMulHom⟩

-- these must come after the coe_toFun definitions
initialize_simps_projections ZeroHom (toFun → apply)
initialize_simps_projections AddHom (toFun → apply)
initialize_simps_projections AddMonoidHom (toFun → apply)
initialize_simps_projections OneHom (toFun → apply)
initialize_simps_projections MulHom (toFun → apply)
initialize_simps_projections MonoidHom (toFun → apply)

@[to_additive (attr := simp)]
theorem OneHom.coe_mk [One M] [One N] (f : M → N) (h1) : (OneHom.mk f h1 : M → N) = f := rfl

@[to_additive (attr := simp)]
theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) (hmul) : (MulHom.mk f hmul : M → N) = f := rfl

@[to_additive (attr := simp)]
theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M →ₙ* N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
theorem MonoidHom.coe_mk [MulOneClass M] [MulOneClass N] (f hmul) :
    (MonoidHom.mk f hmul : M → N) = f := rfl

@[to_additive (attr := simp)]
theorem MonoidHom.toOneHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (f.toOneHom : M → N) = f := rfl

@[to_additive (attr := simp)]
theorem MonoidHom.toMulHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    f.toMulHom.toFun = f := rfl

@[to_additive]
theorem MonoidHom.toFun_eq_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : f.toFun = f := rfl

@[to_additive (attr := ext)]
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
theorem MonoidHom.ext [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

namespace MonoidHom

variable [Group G]
variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive (attr := simps -fullyApplied)
  "Makes an additive group homomorphism from a proof that the map preserves addition."]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]

end MonoidHom

@[to_additive (attr := simp)]
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MulHom.mk_coe [Mul M] [Mul N] (f : M →ₙ* N) (hmul) : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MonoidHom.mk_coe [MulOneClass M] [MulOneClass N] (f : M →* N) (hmul) :
    MonoidHom.mk f hmul = f := MonoidHom.ext fun _ => rfl

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

@[to_additive (attr := simp)]
theorem OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
theorem OneHom.coe_copy_eq {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MulHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  "Copy of an `AddHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities."]
protected def MulHom.copy [Mul M] [Mul N] (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    M →ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'

@[to_additive (attr := simp)]
theorem MulHom.coe_copy {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
theorem MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
  "Copy of an `AddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities."]
protected def MonoidHom.copy [MulOneClass M] [MulOneClass N] (f : M →* N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

@[to_additive (attr := simp)]
theorem MonoidHom.coe_copy {_ : MulOneClass M} {_ : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : (f.copy f' h) = f' :=
  rfl

@[to_additive]
theorem MonoidHom.copy_eq {_ : MulOneClass M} {_ : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[to_additive]
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive "If `f` is an additive monoid homomorphism then `f 0 = 0`."]
protected theorem MonoidHom.map_one [MulOneClass M] [MulOneClass N] (f : M →* N) : f 1 = 1 :=
  f.map_one'

@[to_additive]
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive "If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`."]
protected theorem MonoidHom.map_mul [MulOneClass M] [MulOneClass N] (f : M →* N) (a b : M) :
    f (a * b) = f a * f b := f.map_mul' a b

namespace MonoidHom

variable [MulOneClass M] [MulOneClass N] [FunLike F M N] [MonoidHomClass F M N]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  "Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a right inverse, then `f x` has a right inverse too."]
theorem map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  "Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
  `IsAddUnit.map`."]
theorem map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

end MonoidHom

/-- The identity map from a type with 1 to itself. -/
@[to_additive (attr := simps) "The identity map from a type with zero to itself."]
def OneHom.id (M : Type*) [One M] : OneHom M M where
  toFun x := x
  map_one' := rfl

/-- The identity map from a type with multiplication to itself. -/
@[to_additive (attr := simps) "The identity map from a type with addition to itself."]
def MulHom.id (M : Type*) [Mul M] : M →ₙ* M where
  toFun x := x
  map_mul' _ _ := rfl

/-- The identity map from a monoid to itself. -/
@[to_additive (attr := simps) "The identity map from an additive monoid to itself."]
def MonoidHom.id (M : Type*) [MulOneClass M] : M →* M where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
lemma OneHom.coe_id {M : Type*} [One M] : (OneHom.id M : M → M) = _root_.id := rfl

@[to_additive (attr := simp)]
lemma MulHom.coe_id {M : Type*} [Mul M] : (MulHom.id M : M → M) = _root_.id := rfl

@[to_additive (attr := simp)]
lemma MonoidHom.coe_id {M : Type*} [MulOneClass M] : (MonoidHom.id M : M → M) = _root_.id := rfl

/-- Composition of `OneHom`s as a `OneHom`. -/
@[to_additive "Composition of `ZeroHom`s as a `ZeroHom`."]
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun := hnp ∘ hmn
  map_one' := by simp

/-- Composition of `MulHom`s as a `MulHom`. -/
@[to_additive "Composition of `AddHom`s as an `AddHom`."]
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
  toFun := hnp ∘ hmn
  map_mul' x y := by simp

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive "Composition of additive monoid morphisms as an additive monoid morphism."]
def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
theorem MonoidHom.coe_comp [MulOneClass M] [MulOneClass N] [MulOneClass P]
    (g : N →* P) (f : M →* N) : ↑(g.comp f) = g ∘ f := rfl

@[to_additive]
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
theorem MonoidHom.comp_apply [MulOneClass M] [MulOneClass N] [MulOneClass P]
    (g : N →* P) (f : M →* N) (x : M) : g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive "Composition of additive monoid homomorphisms is associative."]
theorem OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q]
    (f : OneHom M N) (g : OneHom N P) (h : OneHom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
theorem MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
    (f : M →ₙ* N) (g : N →ₙ* P) (h : P →ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
theorem MonoidHom.comp_assoc {Q : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P]
    [MulOneClass Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N →ₙ* P} {f : M →ₙ* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem MonoidHom.cancel_right [MulOneClass M] [MulOneClass N] [MulOneClass P]
    {g₁ g₂ : N →* P} {f : M →* N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => OneHom.ext fun x => hg <| by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MulHom.ext fun x => hg <| by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
theorem MonoidHom.cancel_left [MulOneClass M] [MulOneClass N] [MulOneClass P]
    {g : N →* P} {f₁ f₂ : M →* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MonoidHom.ext fun x => hg <| by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

section

@[to_additive]
theorem MonoidHom.toOneHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[to_additive]
theorem MonoidHom.toMulHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → M →ₙ* N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

@[to_additive (attr := simp)]
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MulHom.comp_id [Mul M] [Mul N] (f : M →ₙ* N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MonoidHom.comp_id [MulOneClass M] [MulOneClass N] (f : M →* N) :
    f.comp (MonoidHom.id M) = f := MonoidHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MulHom.id_comp [Mul M] [Mul N] (f : M →ₙ* N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem MonoidHom.id_comp [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (MonoidHom.id N).comp f = f := MonoidHom.ext fun _ => rfl

@[to_additive]
protected theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = f a ^ n := map_pow f a n

@[to_additive]
protected theorem MonoidHom.map_zpow' [DivInvMonoid M] [DivInvMonoid N] (f : M →* N)
    (hf : ∀ x, f x⁻¹ = (f x)⁻¹) (a : M) (n : ℤ) :
    f (a ^ n) = f a ^ n := map_zpow' f hf a n

/-- Makes a `OneHom` inverse from the left inverse of a `OneHom` -/
@[to_additive (attr := simps)
  "Make a `ZeroHom` inverse from the left inverse of a `ZeroHom`"]
def OneHom.inverse [One M] [One N]
    (f : OneHom M N) (g : N → M)
    (h₁ : Function.LeftInverse g f) :
  OneHom N M :=
  { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

theorem OneHom.inverse_comp [One M] [One N] {f : OneHom M N} {g : N → M}
    {h : Function.LeftInverse g f} : (f.inverse g h).comp f = id M := OneHom.ext h

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive (attr := simps)
  "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y := h₁.injective <| by simp only [map_mul, h₂ x, h₂ y, h₂ (x * y)]

theorem MulHom.inverse_comp [Mul M] [Mul N] {f : M →ₙ* N} {g : N → M}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (f.inverse g h₁ h₂).comp f = id M := MulHom.ext h₁

theorem MulHom.comp_inverse [Mul M] [Mul N] {f : M →ₙ* N} {g : N → M}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (f.inverse g h₁ h₂) = id N := MulHom.ext h₂

/-- If `M` and `N` have multiplications, `f : M →ₙ* N` is a surjective multiplicative map,
and `M` is commutative, then `N` is commutative. -/
@[to_additive
"If `M` and `N` have additions, `f : M →ₙ+ N` is a surjective additive map,
and `M` is commutative, then `N` is commutative."]
theorem Function.Surjective.mul_comm [Mul M] [Mul N] {f : M →ₙ* N}
    (is_surj : Function.Surjective f) (is_comm : Std.Commutative (· * · : M → M → M)) :
    Std.Commutative (· * · : N → N → N) where
  comm := fun a b ↦ by
    obtain ⟨a', ha'⟩ := is_surj a
    obtain ⟨b', hb'⟩ := is_surj b
    simp only [← ha', ← hb', ← map_mul]
    rw [is_comm.comm]

/-- The inverse of a bijective `MonoidHom` is a `MonoidHom`. -/
@[to_additive (attr := simps)
  "The inverse of a bijective `AddMonoidHom` is an `AddMonoidHom`."]
def MonoidHom.inverse {A B : Type*} [Monoid A] [Monoid B] (f : A →* B) (g : B → A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : OneHom A B).inverse g h₁,
    (f : A →ₙ* B).inverse g h₁ h₂ with toFun := g }

theorem MonoidHom.inverse_comp [Monoid M] [Monoid N] {f : M →* N} {g : N → M}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (f.inverse g h₁ h₂).comp f = id M := MonoidHom.ext h₁

theorem MonoidHom.comp_inverse [Monoid M] [Monoid N] {f : M →* N} {g : N → M}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (f.inverse g h₁ h₂) = id N := MonoidHom.ext h₂

section Lift

namespace OneHom

variable [One M] [One N] [One P]

/-- If `p : OneHom M P` is a `MulHom`, `g : P → N` is a map, and `f : OneHom M N`
  is a `OneHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also a `OneHom`. -/
@[to_additive (attr := simps) " If `p : ZeroHom M P` is a `ZeroHom`, `g : P → N`
  is a map, and `f : ZeroHom M N` is an `ZeroHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also an
  `ZeroHom`. "]
def liftLeft (f : OneHom M N) (p : OneHom M P) (g : P → N) (hg : ∀ x, g (p x) = f x) :
    OneHom P N where toFun := g; map_one' := by simpa only [hg, map_one] using hg 1

/-- If `p : OneHom P N` is an injective `OneHom`, `g : M → P` is a map, and `f : OneHom M N`
  is a `OneHom` such that `⇑p ∘ g = ⇑f`, then `g` is also a `OneHom`. -/
@[to_additive (attr := simps) " If `p : ZeroHom P N` is an injective `ZeroHom`, `g : M → P`
  is a map, and `f : ZeroHom M N` is a `ZeroHom` such that `⇑p ∘ g = ⇑f`, then `g` is also an
  `ZeroHom`. "]
def liftRight (f : OneHom M N) {p : OneHom P N} (hp : Injective p) (g : M → P)
    (hg : ∀ x, p (g x) = f x) : OneHom M P where
  toFun := g; map_one' := hp <| by simpa only [map_one] using hg 1

end OneHom

namespace MulHom

variable [Mul M] [Mul N] [Mul P]

/-- If `p : M →ₙ* P` is a surjective `MulHom`, `g : P → N` is a map, and `f : M →ₙ* N`
  is a `MulHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also a `MulHom`. -/
@[to_additive (attr := simps) " If `p : M →ₙ+ P` is a surjective `AddMulHom`, `g : P → N`
  is a map, and `f : M →ₙ+ N` is an `AddMulHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also an
  `AddMulHom`. "]
def liftLeft (f : M →ₙ* N) {p : M →ₙ* P} (hp : Surjective p) (g : P → N)
    (hg : ∀ x, g (p x) = f x) : P →ₙ* N where
  toFun := g; map_mul' x y := by
    rcases hp x with ⟨x, rfl⟩
    rcases hp y with ⟨y, rfl⟩
    simp only [← map_mul p x y, hg, map_mul f]

/-- If `p : P →ₙ* N` is an injective `MulHom`, `g : M → P` is a map, and `f : M →ₙ* N`
  is a `MulHom` such that `⇑p ∘ g = ⇑f`, then `g` is also a `MulHom`. -/
@[to_additive (attr := simps) " If `p : P →ₙ+ N` is an injective `AddMulHom`, `g : M → P`
  is a map, and `f : M →ₙ+ N` is an `AddMulHom` such that `⇑p ∘ g = ⇑f`, then `g` is also an
  `AddMulHom`. "]
def liftRight (f : M →ₙ* N)
    {p : P →ₙ* N} (hp : Injective p) (g : M → P) (hg : ∀ x, p (g x) = f x) : M →ₙ* P where
  toFun := g; map_mul' x y := hp <| by simp only [hg, map_mul]

end MulHom

namespace MonoidHom

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

/-- If `p : M →* P` is a surjective `MonoidHom`, `g : P → N` is a map, and `f : M →* N`
  is a `MonoidHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also a `MonoidHom`. -/
@[to_additive (attr := simps) " If `p : M →+ P` is a surjective `AddMonoidHom`, `g : P → N`
  is a map, and `f : M →+ N` is an `AddMonoidHom` such that `g ∘ ⇑p = ⇑f`, then `g` is also an
  `AddMonoidHom`. "]
def liftLeft (f : M →* N) {p : M →* P} (hp : Surjective p) (g : P → N) (hg : ∀ x, g (p x) = f x) :
    P →* N where
  toFun := g; map_one' := by simpa only [hg, map_one] using hg 1
  map_mul' x y := by
    rcases hp x with ⟨x, rfl⟩
    rcases hp y with ⟨y, rfl⟩
    simp only [← map_mul p x y, hg, map_mul f]

/-- If `p : P →* N` is an injective `MonoidHom`, `g : M → P` is a map, and `f : M →* N`
  is a `MonoidHom` such that `⇑p ∘ g = ⇑f`, then `g` is also a `MonoidHom`. -/
@[to_additive (attr := simps) " If `p : P →+ N` is an injective `AddMonoidHom`, `g : M → P`
  is a map, and `f : M →+ N` is an `AddMonoidHom` such that `⇑p ∘ g = ⇑f`, then `g` is also an
  `AddMonoidHom`. "]
def liftRight (f : M →* N) {p : P →* N} (hp : Injective p) (g : M → P) (hg : ∀ x, p (g x) = f x) :
    M →* P where
  toFun := g; map_one' := hp <| by simpa only [map_one] using hg 1
  map_mul' x y := hp <| by simp only [hg, map_mul]

end MonoidHom

end Lift

section End

namespace Monoid

variable (M) [MulOneClass M]

/-- The monoid of endomorphisms. -/
@[to_additive "The monoid of endomorphisms.", to_additive_dont_translate]
protected def End := M →* M

namespace End

@[to_additive]
instance instFunLike : FunLike (Monoid.End M) M M := MonoidHom.instFunLike
@[to_additive]
instance instMonoidHomClass : MonoidHomClass (Monoid.End M) M M := MonoidHom.instMonoidHomClass

@[to_additive instOne]
instance instOne : One (Monoid.End M) where one := .id _
@[to_additive instMul]
instance instMul : Mul (Monoid.End M) where mul := .comp

@[to_additive instMonoid]
instance instMonoid : Monoid (Monoid.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *] <;> rfl
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _

@[to_additive]
instance : Inhabited (Monoid.End M) := ⟨1⟩

@[to_additive (attr := simp, norm_cast) coe_pow]
lemma coe_pow (f : Monoid.End M) (n : ℕ) : (↑(f ^ n) : M → M) = f^[n] := rfl

@[to_additive (attr := simp) coe_one]
theorem coe_one : ((1 : Monoid.End M) : M → M) = id := rfl

@[to_additive (attr := simp) coe_mul]
theorem coe_mul (f g) : ((f * g : Monoid.End M) : M → M) = f ∘ g := rfl

end End

@[deprecated (since := "2024-11-20")] protected alias coe_one := End.coe_one
@[deprecated (since := "2024-11-20")] protected alias coe_mul := End.coe_mul

end Monoid

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

@[to_additive (attr := simp)]
theorem MonoidHom.one_apply [MulOneClass M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 := rfl

@[to_additive (attr := simp)]
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl

@[to_additive (attr := simp)]
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [OneHom.map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

@[to_additive]
instance [One M] [One N] : Inhabited (OneHom M N) := ⟨1⟩

@[to_additive]
instance [Mul M] [MulOneClass N] : Inhabited (M →ₙ* N) := ⟨1⟩

@[to_additive]
instance [MulOneClass M] [MulOneClass N] : Inhabited (M →* N) := ⟨1⟩

namespace MonoidHom

@[to_additive (attr := simp)]
theorem one_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 := rfl

@[to_additive (attr := simp)]
theorem comp_one [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

/-- Group homomorphisms preserve inverse. -/
@[to_additive "Additive group homomorphisms preserve negation."]
protected theorem map_inv [Group α] [DivisionMonoid β] (f : α →* β) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f _

/-- Group homomorphisms preserve integer power. -/
@[to_additive "Additive group homomorphisms preserve integer scaling."]
protected theorem map_zpow [Group α] [DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ) :
    f (g ^ n) = f g ^ n := map_zpow f g n

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_div [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g / h) = f g / f h := map_div f g h

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ := by simp

end MonoidHom

@[to_additive (attr := simp)]
lemma iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x * y) = f^[n] x * f^[n] y :=
  Function.Semiconj₂.iterate (map_mul f) n x y

@[to_additive (attr := simp)]
lemma iterate_map_one {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M]
    (f : F) (n : ℕ) :
    f^[n] 1 = 1 :=
  iterate_fixed (map_one f) n

@[to_additive (attr := simp)]
lemma iterate_map_inv {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) :
    f^[n] x⁻¹ = (f^[n] x)⁻¹ :=
  Commute.iterate_left (map_inv f) n x

@[to_additive (attr := simp)]
lemma iterate_map_div {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x / y) = f^[n] x / f^[n] y :=
  Semiconj₂.iterate (map_div f) n x y

@[to_additive (attr := simp)]
lemma iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℕ) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_pow f · k) n x

@[to_additive (attr := simp)]
lemma iterate_map_zpow {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℤ) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_zpow f · k) n x
