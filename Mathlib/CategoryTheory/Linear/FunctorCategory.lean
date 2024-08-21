/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate

import Mathlib.Data.Nat.Cast.Defs

import Batteries.Tactic.ShowUnused
import Mathlib.Tactic.Linter.MinImports
import Mathlib.Util.CountHeartbeats
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists


universe x w v u v' u' v₁ v₂ v₃ u₁ u₂ u₃

section Mathlib.Algebra.Group.Hom.Defs

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
class AddMonoidHomClass (F M N : Type*) [AddZeroClass M] [AddZeroClass N] [FunLike F M N]
  extends AddHomClass F M N, ZeroHomClass F M N : Prop

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

variable [FunLike F M N]

@[to_additive (attr := simp)]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f

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

variable [FunLike F M N]

@[to_additive (attr := simp)]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

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
-- Porting note: remove once `to_additive` is updated
-- This is waiting on https://github.com/leanprover-community/mathlib4/issues/660
attribute [to_additive existing] MonoidHom.toMulHom

/-- `M →* N` denotes the type of monoid homomorphisms from `M` to `N`. -/
infixr:25 " →* " => MonoidHom

/-- `MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `MonoidHom`. -/
@[to_additive]
class MonoidHomClass (F : Type*) (M N : outParam Type*) [MulOneClass M] [MulOneClass N]
  [FunLike F M N]
  extends MulHomClass F M N, OneHomClass F M N : Prop

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

variable [FunLike F M N]

@[to_additive]
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) :
    f a * f b = 1 := by
  rw [← map_mul, h, map_one]

variable [FunLike F G H]

@[to_additive]
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, hf]

/-- Group homomorphisms preserve inverse. -/
@[to_additive (attr := simp) "Additive group homomorphisms preserve negation."]
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| map_mul_eq_one f <| inv_mul_cancel _

/-- Group homomorphisms preserve division. -/
@[to_additive (attr := simp) "Additive group homomorphisms preserve subtraction."]
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b := map_div' _ <| map_inv f

end mul_one

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

namespace MonoidHom

variable [Group G]
variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]

end MonoidHom

end Coes

end Mathlib.Algebra.Group.Hom.Defs


section Mathlib.Algebra.GroupWithZero.Defs

variable {G₀ : Type u} {M₀ M₀' G₀' : Type*}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

end Mathlib.Algebra.GroupWithZero.Defs


section Mathlib.Algebra.Group.Action.Defs

open Function (Injective Surjective)

variable {M N G H A B α β γ δ : Type*}

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

variable [Monoid M] [MulAction M α]

variable (M)

lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

end Mathlib.Algebra.Group.Action.Defs


section Mathlib.Algebra.GroupWithZero.Action.Defs

variable {M N G A B α β γ δ : Type*}

open Function (Injective Surjective)

/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0

section smul_zero

variable [Zero A] [SMulZeroClass M A]

@[simp]
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _

end smul_zero

/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
class DistribSMul (M A : Type*) [AddZeroClass A] extends SMulZeroClass M A where
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _

end DistribSMul

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- See note [lower instance priority]
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }

end Mathlib.Algebra.GroupWithZero.Action.Defs


section Mathlib.Algebra.Ring.Defs

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

end Mathlib.Algebra.Ring.Defs


section Mathlib.Algebra.SMulWithZero

variable {R R' M M' : Type*}

variable (R M)

/-- `SMulWithZero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SMulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0

variable {M} [Zero R] [Zero M] [SMulWithZero R M]

@[simp]
theorem zero_smul (m : M) : (0 : R) • m = 0 :=
  SMulWithZero.zero_smul m

variable [MonoidWithZero R] [MonoidWithZero R'] [Zero M]
variable (M)

/-- An action of a monoid with zero `R` on a Type `M`, also with `0`, extends `MulAction` and
is compatible with `0` (both in `R` and in `M`), with `1 ∈ R`, and with associativity of
multiplication on the monoid `M`. -/
class MulActionWithZero extends MulAction R M where
  -- these fields are copied from `SMulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : ∀ r : R, r • (0 : M) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero [m : MulActionWithZero R M] :
    SMulWithZero R M :=
  { m with }

end Mathlib.Algebra.SMulWithZero


section Mathlib.Algebra.Module.Defs

open Function Set

variable {α R k S M M₂ M₃ ι : Type*}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

export Module (add_smul zero_smul)

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
instance (priority := 100) Module.toMulActionWithZero : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := smul_zero
    zero_smul := Module.zero_smul }

end Mathlib.Algebra.Module.Defs


section Mathlib.Combinatorics.Quiver.Basic

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `Quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `Quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

end Mathlib.Combinatorics.Quiver.Basic


section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
@[pp_with_univ]
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [trans] CategoryStruct.comp

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic


section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

section

/-- `Functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See <https://stacks.math.columbia.edu/tag/001B>.
-/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The prefunctor between the underlying quivers. -/
add_decl_doc Functor.toPrefunctor

end

/-- Notation for a functor between categories. -/
-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
infixr:26 " ⥤ " => Functor -- type as \func

attribute [simp] Functor.map_id Functor.map_comp

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `NatTrans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality`.
-/
@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transformations moving earlier.
attribute [simp] NatTrans.naturality

@[simp]
theorem NatTrans.naturality_assoc {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) {Z : D}
    (h : G.obj Y ⟶ Z) : F.map f ≫ self.app Y ≫ h = self.app X ≫ G.map f ≫ h := by
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]

namespace NatTrans

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := by 
    intro X Y f
    simp_all only [Category.comp_id, Category.id_comp]

@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

open Category

open CategoryTheory.Functor

section

variable {F G H I : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := by 
    intro X Y f
    simp_all only [naturality_assoc, naturality, assoc]

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

end

/-- The diagram
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F U
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
commutes.
-/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  simp

end NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

attribute [local simp] vcomp_app

variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {F G H I : C ⥤ D}

/-- `Functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  id_comp := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', id_comp]
  comp_id := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', comp_id]
  assoc := by 
    intro W X Y Z f g h
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, assoc]

namespace NatTrans

-- Porting note: the behaviour of `ext` has changed here.
-- We need to provide a copy of the `NatTrans.ext` lemma,
-- written in terms of `F ⟶ G` rather than `NatTrans F G`,
-- or `ext` will not retrieve it from the cache.
@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

end NatTrans

open NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.Functor.Category

noncomputable
section Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open scoped Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

attribute [instance] HasZeroMorphisms.zero

variable {C}

@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f

end CategoryTheory.Limits

end Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

section Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance] Preadditive.homGroup

attribute [simp] Preadditive.add_comp

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] Preadditive.comp_add

end CategoryTheory

namespace CategoryTheory

namespace Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

@[simp]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

@[simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

@[simp]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

@[simp]
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

end Preadditive

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero :=
   { app := fun X => 0
     naturality := by 
       intro X Y f
       simp_all only [comp_zero, zero_comp] }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β :=
  { app := fun X => α.app X + β.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_add, NatTrans.naturality, add_comp] }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α :=
  { app := fun X => -α.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_neg, NatTrans.naturality, neg_comp] }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul := nsmulRec
      zsmul := zsmulRec
      sub := fun α β =>
      { app := fun X => α.app X - β.app X
        naturality := by 
          intro X Y f
          simp_all only [comp_sub, NatTrans.naturality, sub_comp] }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        dsimp
        ext
        apply zero_add
      add_zero := by
        intros
        dsimp
        ext
        apply add_zero
      add_comm := by
        intros
        dsimp
        ext
        apply add_comm
      sub_eq_add_neg := by
        intros
        dsimp
        ext
        apply sub_eq_add_neg
      neg_add_cancel := by
        intros
        dsimp
        ext
        apply neg_add_cancel }
  add_comp := by
    intros
    dsimp
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp
    ext
    apply comp_add

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory.Limits

namespace CategoryTheory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

attribute [instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

end Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory

namespace CategoryTheory

open CategoryTheory.Limits Linear
open CategoryTheory.Linear

variable {R : Type*} [Semiring R]
variable {C D : Type*} [Category C] [Category D] [Preadditive D] [Linear R D]

#adaptation_note
/--
At nightly-2024-08-08 we needed to significantly increase the maxHeartbeats here.
-/
count_heartbeats in
instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    { 
      smul := fun r α ↦ 
        { app := fun X ↦ r • α.app X
          naturality := by
            intros
            rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }
      one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

instance functorCategorySMul (F G : C ⥤ D) : SMul R (F ⟶ G) where
  smul r α := 
    { app := fun X => r • α.app X
      naturality := by
        intros
        rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }

instance functorCategoryLinear' : Linear R (C ⥤ D) where
  homModule F G :=
    { one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

end CategoryTheory

#show_unused  CategoryTheory.functorCategoryLinear CategoryTheory.functorCategoryLinear'
#min_imports
