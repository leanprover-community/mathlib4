/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Algebras over commutative semirings

In this file we define associative unital `Algebra`s over commutative (semi)rings.

* algebra homomorphisms `AlgHom` are defined in `Mathlib/Algebra/Algebra/Hom.lean`;

* algebra equivalences `AlgEquiv` are defined in `Mathlib/Algebra/Algebra/Equiv.lean`;

* `Subalgebra`s are defined in `Mathlib/Algebra/Algebra/Subalgebra.lean`;

* The category `AlgCat R` of `R`-algebras is defined in the file
  `Mathlib/Algebra/Category/Algebra/Basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `Algebra R A`: the algebra typeclass.
* `algebraMap R A : R →+* A`: the canonical map from `R` to `A`, as a `RingHom`. This is the
  preferred spelling of this map, it is also available as:
  * `Algebra.linearMap R A : R →ₗ[R] A`, a `LinearMap`.
  * `Algebra.ofId R A : R →ₐ[R] A`, an `AlgHom` (defined in a later file).

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebraMap R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `Algebra R A` in a way that subsumes both definitions, by extending `SMul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebraMap R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Algebra R A]
   ```
2. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebraMap R A` is available, and `AlgHom R A B` and
`Subalgebra R A` can be used. For concrete `R` and `A`, `algebraMap R A` is often definitionally
convenient.

The advantage of the second approach is that `CommSemiring R`, `Semiring A`, and `Module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `Semiring A` with `NonUnitalNonAssocSemiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `CommSemiring R` and `Module R A` with `CommGroup R'` and `DistribMulAction R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `AlgHom R A B` cannot be used in the second approach, `NonUnitalAlgHom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/

assert_not_exists Field Finset Module.End

universe u v w u₁ v₁

section Prio

/-- An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  /-- Embedding `R →+* A` given by `Algebra` structure.
  Use `algebraMap` from the root namespace instead. -/
  protected algebraMap : R →+* A
  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r
  smul_def' : ∀ r x, r • x = algebraMap r * x

end Prio

/-- Embedding `R →+* A` given by `Algebra` structure. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.algebraMap

/-- Coercion from a commutative semiring to an algebra over this semiring. -/
@[coe, reducible]
def Algebra.cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : R → A :=
  algebraMap R A

namespace algebraMap

scoped instance coeHTCT (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    CoeHTCT R A :=
  ⟨Algebra.cast⟩

section CommSemiringSemiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[norm_cast]
theorem coe_zero : (↑(0 : R) : A) = 0 :=
  map_zero (algebraMap R A)

@[norm_cast]
theorem coe_one : (↑(1 : R) : A) = 1 :=
  map_one (algebraMap R A)

@[norm_cast]
theorem coe_natCast (a : ℕ) : (↑(a : R) : A) = a :=
  map_natCast (algebraMap R A) a

@[norm_cast]
theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
  map_add (algebraMap R A) a b

@[norm_cast]
theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
  map_mul (algebraMap R A) a b

@[norm_cast]
theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n :=
  map_pow (algebraMap R A) _ _

end CommSemiringSemiring

section CommRingRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[norm_cast]
theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
  map_neg (algebraMap R A) x

@[norm_cast]
theorem coe_sub (a b : R) :
    (↑(a - b : R) : A) = ↑a - ↑b :=
  map_sub (algebraMap R A) a b

end CommRingRing

end algebraMap

/-- Creating an algebra from a morphism to the center of a semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `RingHom` and
this will likely create a diamond. -/
abbrev RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) : Algebra R S where
  smul c x := i c * x
  commutes' := h
  smul_def' _ _ := rfl
  algebraMap := i

-- just simple lemmas for a declaration that is itself primed, no need for docstrings
set_option linter.docPrime false in
theorem RingHom.smul_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) (r : R) (s : S) :
    let _ := RingHom.toAlgebra' i h
    r • s = i r * s := rfl

set_option linter.docPrime false in
theorem RingHom.algebraMap_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) :
    @algebraMap R S _ _ (i.toAlgebra' h) = i :=
  rfl

/-- Creating an algebra from a morphism to a commutative semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `RingHom` and
this will likely create a diamond. -/
abbrev RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra' fun _ => mul_comm _

theorem RingHom.smul_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S)
    (r : R) (s : S) :
    let _ := RingHom.toAlgebra i
    r • s = i r * s := rfl

theorem RingHom.algebraMap_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) :
    @algebraMap R S _ _ i.toAlgebra = i :=
  rfl

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `Algebra`
over `R`.

See note [reducible non-instances]. -/
abbrev ofModule' [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x : A), r • (1 : A) * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * r • (1 : A) = r • x) : Algebra R A where
  algebraMap :=
  { toFun r := r • (1 : A)
    map_one' := one_smul _ _
    map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
    map_zero' := zero_smul _ _
    map_add' r₁ r₂ := add_smul r₁ r₂ 1 }
  commutes' r x := by simp [h₁, h₂]
  smul_def' r x := by simp [h₁]

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `Algebra` over `R`.

See note [reducible non-instances]. -/
abbrev ofModule [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

-- We'll later use this to show `Algebra ℤ M` is a subsingleton.
/-- To prove two algebra structures on a fixed `[CommSemiring R] [Semiring A]` agree,
it suffices to check the `algebraMap`s agree.
-/
@[ext]
theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
    (h : ∀ r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :
    P = Q := by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R → A → A) = (haveI := Q; (· • ·) : R → A → A) := by
    funext r a
    rw [P.smul_def', Q.smul_def', h]
  rcases P with @⟨⟨P⟩⟩
  rcases Q with @⟨⟨Q⟩⟩
  congr

-- see Note [lower instance priority]
instance (priority := 200) toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] :
    Module R A where
  one_smul _ := by simp [smul_def']
  mul_smul := by simp [smul_def', mul_assoc]
  smul_add := by simp [smul_def', mul_add]
  smul_zero := by simp [smul_def']
  add_smul := by simp [smul_def', add_mul]
  zero_smul := by simp [smul_def']

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x

theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm

theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebraMap_eq_smul_one

/-- `mul_comm` for `Algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x

lemma commute_algebraMap_left (r : R) (x : A) : Commute (algebraMap R A r) x :=
  Algebra.commutes r x

lemma commute_algebraMap_right (r : R) (x : A) : Commute x (algebraMap R A r) :=
  (Algebra.commutes r x).symm

/-- `mul_left_comm` for `Algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `Algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc, commutes, ← mul_assoc]

instance _root_.IsScalarTower.right : IsScalarTower R A A :=
  ⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

@[simp]
theorem _root_.RingHom.smulOneHom_eq_algebraMap : RingHom.smulOneHom = algebraMap R A :=
  RingHom.ext fun r => (algebraMap_eq_smul_one r).symm

-- TODO: set up `IsScalarTower.smulCommClass` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y

@[simp]
theorem _root_.smul_algebraMap {α : Type*} [Monoid α] [MulDistribMulAction α A]
    [SMulCommClass α R A] (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [algebraMap_eq_smul_one, smul_comm a r (1 : A), smul_one]

section compHom

variable (A) (f : S →+* R)

/--
Compose an `Algebra` with a `RingHom`, with action `f s • m`.

This is the algebra version of `Module.compHom`.
-/
abbrev compHom : Algebra S A where
  smul s a := f s • a
  algebraMap := (algebraMap R A).comp f
  commutes' _ _ := Algebra.commutes _ _
  smul_def' _ _ := Algebra.smul_def _ _

theorem compHom_smul_def (s : S) (x : A) :
    letI := compHom A f
    s • x = f s • x := rfl

theorem compHom_algebraMap_eq :
    letI := compHom A f
    algebraMap S A = (algebraMap R A).comp f := rfl

theorem compHom_algebraMap_apply (s : S) :
    letI := compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

end compHom


variable (R A)

/-- The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linearMap : R →ₗ[R] A :=
  { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }

@[simp]
theorem linearMap_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl

theorem coe_linearMap : ⇑(Algebra.linearMap R A) = algebraMap R A :=
  rfl

/-- The identity map inducing an `Algebra` structure. -/
instance (priority := 1100) id : Algebra R R where
  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot
  -- be made so without a significant performance hit.
  -- see library note [reducible non-instances].
  toSMul := Mul.toSMul _
  __ := ({RingHom.id R with toFun x := x}).toAlgebra

@[simp] lemma linearMap_self : Algebra.linearMap R R = .id := rfl

variable {R A}

@[simp] lemma algebraMap_self : algebraMap R R = .id _ := rfl
lemma algebraMap_self_apply (x : R) : algebraMap R R x = x := rfl

namespace id

@[deprecated algebraMap_self (since := "2025-07-17")]
theorem map_eq_id : algebraMap R R = RingHom.id _ :=
  rfl

@[deprecated algebraMap_self_apply (since := "2025-07-17")]
theorem map_eq_self (x : R) : algebraMap R R x = x :=
  rfl

@[simp]
theorem smul_eq_mul (x y : R) : x • y = x * y :=
  rfl

end id

end Semiring

end Algebra

@[norm_cast]
theorem algebraMap.coe_smul (A B C : Type*) [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]
    [SMul A C] [IsScalarTower A B C] (a : A) (b : B) : (a • b : B) = a • (b : C) := calc
  ((a • b : B) : C) = (a • b) • 1 := Algebra.algebraMap_eq_smul_one _
  _ = a • (b • 1) := smul_assoc ..
  _ = a • (b : C) := congrArg _ (Algebra.algebraMap_eq_smul_one b).symm

