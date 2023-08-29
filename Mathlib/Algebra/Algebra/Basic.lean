/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.PUnitInstances
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.LinearAlgebra.Basic
import Mathlib.RingTheory.Subring.Basic

#align_import algebra.algebra.basic from "leanprover-community/mathlib"@"36b8aa61ea7c05727161f96a0532897bd72aedab"

/-!
# Algebras over commutative semirings

In this file we define associative unital `Algebra`s over commutative (semi)rings.

* algebra homomorphisms `AlgHom` are defined in `Mathlib.Algebra.Algebra.Hom`;

* algebra equivalences `AlgEquiv` are defined in `Mathlib.Algebra.Algebra.Equiv`;

* `Subalgebra`s are defined in `Mathlib.Algebra.Algebra.Subalgebra`;

* The category `AlgebraCat R` of `R`-algebras is defined in the file
  `Mathlib.Algebra.Category.Algebra.Basic`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `Algebra R A`: the algebra typeclass.
* `algebraMap R A : R →+* A`: the canonical map from `R` to `A`, as a `RingHom`. This is the
  preferred spelling of this map, it is also available as:
  * `Algebra.linearMap R A : R →ₗ[R] A`, a `LinearMap`.
  * `algebra.ofId R A : R →ₐ[R] A`, an `AlgHom` (defined in a later file).
* Instances of `Algebra` in this file:
  * `Algebra.id`
  * `algebraNat`
  * `algebraInt`
  * `algebraRat`
  * `module.End.algebra`

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
   variables [CommSemiring R] [Semiring A]
   variables [Algebra R A]
   ```
2. ```lean
   variables [CommSemiring R] [Semiring A]
   variables [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
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

universe u v w u₁ v₁

open BigOperators

section Prio

-- We set this priority to 0 later in this file
-- porting note: unsupported set_option extends_priority 200

/- control priority of
`instance [Algebra R A] : SMul R A` -/
/-- An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
-- porting note: unsupported @[nolint has_nonempty_instance]
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where
  commutes' : ∀ r x, toRingHom r * x = x * toRingHom r
  smul_def' : ∀ r x, r • x = toRingHom r * x
#align algebra Algebra

end Prio

/-- Embedding `R →+* A` given by `Algebra` structure. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom
#align algebra_map algebraMap

/-- Coercion from a commutative semiring to an algebra over this semiring. -/
@[coe] def Algebra.cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : R → A :=
  algebraMap R A

namespace algebraMap

scoped instance coeHTCT (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    CoeHTCT R A :=
  ⟨Algebra.cast⟩
#align algebra_map.has_lift_t algebraMap.coeHTCT

section CommSemiringSemiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : A) = 0 :=
  map_zero (algebraMap R A)
#align algebra_map.coe_zero algebraMap.coe_zero

@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : A) = 1 :=
  map_one (algebraMap R A)
#align algebra_map.coe_one algebraMap.coe_one

@[norm_cast]
theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
  map_add (algebraMap R A) a b
#align algebra_map.coe_add algebraMap.coe_add

@[norm_cast]
theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
  map_mul (algebraMap R A) a b
#align algebra_map.coe_mul algebraMap.coe_mul

@[norm_cast]
theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n :=
  map_pow (algebraMap R A) _ _
#align algebra_map.coe_pow algebraMap.coe_pow

end CommSemiringSemiring

section CommRingRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[norm_cast]
theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
  map_neg (algebraMap R A) x
#align algebra_map.coe_neg algebraMap.coe_neg

end CommRingRing

section CommSemiringCommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

open BigOperators

-- direct to_additive fails because of some mix-up with polynomials
@[norm_cast]
theorem coe_prod {ι : Type*} {s : Finset ι} (a : ι → R) :
    (↑(∏ i : ι in s, a i : R) : A) = ∏ i : ι in s, (↑(a i) : A) :=
  map_prod (algebraMap R A) a s
#align algebra_map.coe_prod algebraMap.coe_prod

-- to_additive fails for some reason
@[norm_cast]
theorem coe_sum {ι : Type*} {s : Finset ι} (a : ι → R) :
    ↑(∑ i : ι in s, a i) = ∑ i : ι in s, (↑(a i) : A) :=
  map_sum (algebraMap R A) a s
#align algebra_map.coe_sum algebraMap.coe_sum

-- porting note: removed attribute [to_additive] coe_prod; why should this be a `to_additive`?

end CommSemiringCommSemiring

section FieldNontrivial

variable {R A : Type*} [Field R] [CommSemiring A] [Nontrivial A] [Algebra R A]

@[norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (algebraMap R A).injective.eq_iff
#align algebra_map.coe_inj algebraMap.coe_inj

@[norm_cast, simp]
theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
  map_eq_zero_iff _ (algebraMap R A).injective
#align algebra_map.lift_map_eq_zero_iff algebraMap.lift_map_eq_zero_iff

end FieldNontrivial

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r
#align algebra_map.coe_inv algebraMap.coe_inv

@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s
#align algebra_map.coe_div algebraMap.coe_div

@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z :=
  map_zpow₀ (algebraMap R A) r z
#align algebra_map.coe_zpow algebraMap.coe_zpow

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

-- porting note: todo: drop implicit args
@[norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) :=
  @map_ratCast (R →+* A) R A _ _ _ (algebraMap R A) q
#align algebra_map.coe_rat_cast algebraMap.coe_ratCast

end FieldDivisionRing

end algebraMap

/-- Creating an algebra from a morphism to the center of a semiring. -/
def RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) : Algebra R S where
  smul c x := i c * x
  commutes' := h
  smul_def' _ _ := rfl
  toRingHom := i
#align ring_hom.to_algebra' RingHom.toAlgebra'

/-- Creating an algebra from a morphism to a commutative semiring. -/
def RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra' fun _ => mul_comm _
#align ring_hom.to_algebra RingHom.toAlgebra

theorem RingHom.algebraMap_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) :
    @algebraMap R S _ _ i.toAlgebra = i :=
  rfl
#align ring_hom.algebra_map_to_algebra RingHom.algebraMap_toAlgebra

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `Algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule' [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x : A), r • (1 : A) * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * r • (1 : A) = r • x) : Algebra R A where
  toFun r := r • (1 : A)
  map_one' := one_smul _ _
  map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
                       -- 🎉 no goals
  map_zero' := zero_smul _ _
  map_add' r₁ r₂ := add_smul r₁ r₂ 1
  commutes' r x := by simp [h₁, h₂]
                      -- 🎉 no goals
  smul_def' r x := by simp [h₁]
                      -- 🎉 no goals
#align algebra.of_module' Algebra.ofModule'

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `Algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]
                           -- 🎉 no goals
                                                           -- 🎉 no goals
#align algebra.of_module Algebra.ofModule

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

-- porting note: deleted a private lemma

-- We'll later use this to show `Algebra ℤ M` is a subsingleton.
/-- To prove two algebra structures on a fixed `[CommSemiring R] [Semiring A]` agree,
it suffices to check the `algebraMap`s agree.
-/
@[ext]
theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
    (h : ∀ r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :
    P = Q := by
  replace h : P.toRingHom = Q.toRingHom := FunLike.ext _ _ h
  -- ⊢ P = Q
  have h' : (haveI := P; (· • ·) : R → A → A) = (haveI := Q; (· • ·) : R → A → A) := by
    funext r a
    rw [P.smul_def', Q.smul_def', h]
  rcases P with @⟨⟨P⟩⟩
  -- ⊢ mk toRingHom✝ commutes'✝ smul_def'✝ = Q
  rcases Q with @⟨⟨Q⟩⟩
  -- ⊢ mk toRingHom✝¹ commutes'✝¹ smul_def'✝¹ = mk toRingHom✝ commutes'✝ smul_def'✝
  congr
  -- 🎉 no goals
#align algebra.algebra_ext Algebra.algebra_ext

-- see Note [lower instance priority]
instance (priority := 200) toModule : Module R A where
  one_smul _ := by simp [smul_def']
                   -- 🎉 no goals
  mul_smul := by simp [smul_def', mul_assoc]
                 -- 🎉 no goals
  smul_add := by simp [smul_def', mul_add]
                 -- 🎉 no goals
                  -- 🎉 no goals
  smul_zero := by simp [smul_def']
  add_smul := by simp [smul_def', add_mul]
                 -- 🎉 no goals
  zero_smul := by simp [smul_def']
                  -- 🎉 no goals
#align algebra.to_module Algebra.toModule

-- porting note: this caused deterministic timeouts later in mathlib3 but not in mathlib 4.
-- attribute [instance 0] Algebra.toSMul

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x
#align algebra.smul_def Algebra.smul_def

theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm
#align algebra.algebra_map_eq_smul_one Algebra.algebraMap_eq_smul_one

theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebraMap_eq_smul_one
#align algebra.algebra_map_eq_smul_one' Algebra.algebraMap_eq_smul_one'

/-- `mul_comm` for `Algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x
#align algebra.commutes Algebra.commutes

/-- `mul_left_comm` for `Algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← commutes, mul_assoc]
  -- 🎉 no goals
#align algebra.left_comm Algebra.left_comm

/-- `mul_right_comm` for `Algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) : x * algebraMap R A r * y = x * y * algebraMap R A r :=
  by rw [mul_assoc, commutes, ← mul_assoc]
     -- 🎉 no goals
#align algebra.right_comm Algebra.right_comm

instance _root_.IsScalarTower.right : IsScalarTower R A A :=
  ⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩
                   -- 🎉 no goals
#align is_scalar_tower.right IsScalarTower.right

-- TODO: set up `IsScalarTower.smulCommClass` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  rw [smul_def, smul_def, left_comm]
  -- 🎉 no goals
#align algebra.mul_smul_comm Algebra.mul_smul_comm

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y
#align algebra.smul_mul_assoc Algebra.smul_mul_assoc

@[simp]
theorem _root_.smul_algebraMap {α : Type*} [Monoid α] [MulDistribMulAction α A]
    [SMulCommClass α R A] (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [algebraMap_eq_smul_one, smul_comm a r (1 : A), smul_one]
  -- 🎉 no goals
#align smul_algebra_map smul_algebraMap

section

#noalign algebra.bit0_smul_one
#noalign algebra.bit0_smul_one'
#noalign algebra.bit0_smul_bit0
#noalign algebra.bit0_smul_bit1
#noalign algebra.bit1_smul_one
#noalign algebra.bit1_smul_one'
#noalign algebra.bit1_smul_bit0
#noalign algebra.bit1_smul_bit1

end

variable (R A)

/-- The canonical ring homomorphism `algebraMap R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linearMap : R →ₗ[R] A :=
  { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }
                                                   -- 🎉 no goals
#align algebra.linear_map Algebra.linearMap

@[simp]
theorem linearMap_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl
#align algebra.linear_map_apply Algebra.linearMap_apply

theorem coe_linearMap : ⇑(Algebra.linearMap R A) = algebraMap R A :=
  rfl
#align algebra.coe_linear_map Algebra.coe_linearMap

instance id : Algebra R R :=
  (RingHom.id R).toAlgebra
#align algebra.id Algebra.id

variable {R A}

namespace id

@[simp]
theorem map_eq_id : algebraMap R R = RingHom.id _ :=
  rfl
#align algebra.id.map_eq_id Algebra.id.map_eq_id

theorem map_eq_self (x : R) : algebraMap R R x = x :=
  rfl
#align algebra.id.map_eq_self Algebra.id.map_eq_self

@[simp]
theorem smul_eq_mul (x y : R) : x • y = x * y :=
  rfl
#align algebra.id.smul_eq_mul Algebra.id.smul_eq_mul

end id

section PUnit

instance _root_.PUnit.algebra : Algebra R PUnit where
  toFun _ := PUnit.unit
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ _ := rfl
  smul_def' _ _ := rfl
#align punit.algebra PUnit.algebra

@[simp]
theorem algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit :=
  rfl
#align algebra.algebra_map_punit Algebra.algebraMap_pUnit

end PUnit

section ULift

instance _root_.ULift.algebra : Algebra R (ULift A) :=
  { ULift.module',
    (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
    toFun := fun r => ULift.up (algebraMap R A r)
    commutes' := fun r x => ULift.down_injective <| Algebra.commutes r x.down
    smul_def' := fun r x => ULift.down_injective <| Algebra.smul_def' r x.down }
#align ulift.algebra ULift.algebra

theorem _root_.ULift.algebraMap_eq (r : R) :
    algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl
#align ulift.algebra_map_eq ULift.algebraMap_eq

@[simp]
theorem _root_.ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl
#align ulift.down_algebra_map ULift.down_algebraMap

end ULift

/-- Algebra over a subsemiring. This builds upon `Subsemiring.module`. -/
instance ofSubsemiring (S : Subsemiring R) : Algebra S A where
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x
#align algebra.of_subsemiring Algebra.ofSubsemiring

theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S →+* R) = Subsemiring.subtype S :=
  rfl
#align algebra.algebra_map_of_subsemiring Algebra.algebraMap_ofSubsemiring

theorem coe_algebraMap_ofSubsemiring (S : Subsemiring R) : (algebraMap S R : S → R) = Subtype.val :=
  rfl
#align algebra.coe_algebra_map_of_subsemiring Algebra.coe_algebraMap_ofSubsemiring

theorem algebraMap_ofSubsemiring_apply (S : Subsemiring R) (x : S) : algebraMap S R x = x :=
  rfl
#align algebra.algebra_map_of_subsemiring_apply Algebra.algebraMap_ofSubsemiring_apply

/-- Algebra over a subring. This builds upon `Subring.module`. -/
instance ofSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subring R) :
    Algebra S A where -- porting note: don't use `toSubsemiring` because of a timeout
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x
#align algebra.of_subring Algebra.ofSubring

theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl
#align algebra.algebra_map_of_subring Algebra.algebraMap_ofSubring

theorem coe_algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S → R) = Subtype.val :=
  rfl
#align algebra.coe_algebra_map_of_subring Algebra.coe_algebraMap_ofSubring

theorem algebraMap_ofSubring_apply {R : Type*} [CommRing R] (S : Subring R) (x : S) :
    algebraMap S R x = x :=
  rfl
#align algebra.algebra_map_of_subring_apply Algebra.algebraMap_ofSubring_apply

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)
#align algebra.algebra_map_submonoid Algebra.algebraMapSubmonoid

theorem mem_algebraMapSubmonoid_of_mem {S : Type*} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2
#align algebra.mem_algebra_map_submonoid_of_mem Algebra.mem_algebraMapSubmonoid_of_mem

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]
                                                                  -- 🎉 no goals
#align algebra.mul_sub_algebra_map_commutes Algebra.mul_sub_algebraMap_commutes

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction' n with n ih
  -- ⊢ x * (x - ↑(algebraMap R A) r) ^ Nat.zero = (x - ↑(algebraMap R A) r) ^ Nat.z …
  · simp
    -- 🎉 no goals
  · rw [pow_succ, ← mul_assoc, mul_sub_algebraMap_commutes, mul_assoc, ih, ← mul_assoc]
    -- 🎉 no goals
#align algebra.mul_sub_algebra_map_pow_commutes Algebra.mul_sub_algebraMap_pow_commutes

end CommSemiring

section Ring

variable [CommRing R]

variable (R)

/-- A `Semiring` that is an `Algebra` over a commutative ring carries a natural `Ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiringToRing [Semiring A] [Algebra R A] : Ring A :=
  { Module.addCommMonoidToAddCommGroup R, (inferInstance : Semiring A) with
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_ofNat, map_natCast]
                                 -- 🎉 no goals
    intCast_negSucc := fun z => by simp }
                                   -- 🎉 no goals
#align algebra.semiring_to_ring Algebra.semiringToRing

end Ring

end Algebra

open scoped Algebra

namespace Module

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

instance End.instAlgebra : Algebra R (Module.End S M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

-- to prove this is a special case of the above
example : Algebra R (Module.End R M) := End.instAlgebra _ _ _

theorem algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearMap.id :=
  rfl

@[simp]
theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m :=
  rfl
#align module.algebra_map_End_apply Module.algebraMap_end_applyₓ

@[simp]
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] (a : K)
    (ha : a ≠ 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ :=
  LinearMap.ker_smul _ _ ha
#align module.ker_algebra_map_End Module.ker_algebraMap_end

section

variable {R M}

theorem End_algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    (↑(h.unit⁻¹) : Module.End S M) m = m' ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).symm.trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun ⇑h.unit.val using ((Module.End_isUnit_iff _).mp h).injective
        -- ⊢ ↑↑(IsUnit.unit h) (↑↑(IsUnit.unit h)⁻¹ (x • m')) = ↑↑(IsUnit.unit h) m'
        erw [End_isUnit_apply_inv_apply_of_isUnit]
        -- ⊢ x • m' = ↑↑(IsUnit.unit h) m'
        rfl }
        -- 🎉 no goals
#align module.End_algebra_map_is_unit_inv_apply_eq_iff Module.End_algebraMap_isUnit_inv_apply_eq_iff

theorem End_algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun (↑h.unit : M → M) using ((Module.End_isUnit_iff _).mp h).injective
        -- ⊢ ↑↑(IsUnit.unit h) m' = ↑↑(IsUnit.unit h) (↑↑(IsUnit.unit h)⁻¹ (x • m'))
        erw [End_isUnit_apply_inv_apply_of_isUnit]
        -- ⊢ ↑↑(IsUnit.unit h) m' = x • m'
        rfl }
        -- 🎉 no goals
#align module.End_algebra_map_is_unit_inv_apply_eq_iff' Module.End_algebraMap_isUnit_inv_apply_eq_iff'

end

end Module

namespace LinearMap

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An alternate statement of `LinearMap.map_smul` for when `algebraMap` is more convenient to
work with than `•`. -/
theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  -- 🎉 no goals
#align linear_map.map_algebra_map_mul LinearMap.map_algebraMap_mul

theorem map_mul_algebraMap (f : A →ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes, ← Algebra.commutes, map_algebraMap_mul]
  -- 🎉 no goals
#align linear_map.map_mul_algebra_map LinearMap.map_mul_algebraMap

end LinearMap

section Nat

variable {R : Type*} [Semiring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `Algebra.id` and `algebraNat` are not yet defeq.
-- TODO: fix this by adding an `ofNat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99) algebraNat : Algebra ℕ R where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  toRingHom := Nat.castRingHom R
#align algebra_nat algebraNat

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by ext; simp⟩
                 -- ⊢ ↑(algebraMap ℕ R) r✝ = ↑(algebraMap ℕ R) r✝
                      -- 🎉 no goals
#align nat_algebra_subsingleton nat_algebra_subsingleton

end Nat

namespace RingHom

variable {R S : Type*}

-- porting note: changed `[Ring R] [Ring S]` to `[Semiring R] [Semiring S]`
-- otherwise, Lean failed to find a `Subsingleton (ℚ →+* S)` instance
@[simp]
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r
#align ring_hom.map_rat_algebra_map RingHom.map_rat_algebraMap

end RingHom

section Rat

instance algebraRat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α where
  smul := (· • ·)
  smul_def' := DivisionRing.qsmul_eq_mul'
  toRingHom := Rat.castHom α
  commutes' := Rat.cast_commute
#align algebra_rat algebraRat

/-- The two `Algebra ℚ ℚ` instances should coincide. -/
example : algebraRat = Algebra.id ℚ :=
  rfl

@[simp] theorem algebraMap_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ := rfl
#align algebra_map_rat_rat algebraMap_rat_rat

instance algebra_rat_subsingleton {α} [Semiring α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align algebra_rat_subsingleton algebra_rat_subsingleton

end Rat

section Int

variable (R : Type*) [Ring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `Algebra.id ℤ` and `algebraInt ℤ` are not yet defeq.
-- TODO: fix this by adding an `ofInt` field to rings.
/-- Ring ⥤ ℤ-Alg -/
instance (priority := 99) algebraInt : Algebra ℤ R where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  toRingHom := Int.castRingHom R
#align algebra_int algebraInt

/-- A special case of `eq_intCast'` that happens to be true definitionally -/
@[simp]
theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl
#align algebra_map_int_eq algebraMap_int_eq

variable {R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => Algebra.algebra_ext P Q <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align int_algebra_subsingleton int_algebra_subsingleton

end Int

namespace NoZeroSMulDivisors

variable {R A : Type*}

open Algebra

/-- If `algebraMap R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `Injective (algebraMap R A)` typeclass.
-/
theorem of_algebraMap_injective [CommSemiring R] [Semiring A] [Algebra R A] [NoZeroDivisors A]
    (h : Function.Injective (algebraMap R A)) : NoZeroSMulDivisors R A :=
  ⟨fun hcx => (mul_eq_zero.mp ((smul_def _ _).symm.trans hcx)).imp_left
    (map_eq_zero_iff (algebraMap R A) h).mp⟩
#align no_zero_smul_divisors.of_algebra_map_injective NoZeroSMulDivisors.of_algebraMap_injective

variable (R A)

theorem algebraMap_injective [CommRing R] [Ring A] [Nontrivial A] [Algebra R A]
    [NoZeroSMulDivisors R A] : Function.Injective (algebraMap R A) := by
  -- porting note: todo: drop implicit args
  have := @smul_left_injective R A CommRing.toRing Ring.toAddCommGroup Algebra.toModule
    ‹_› 1 one_ne_zero
  simpa only [algebraMap_eq_smul_one'] using this
  -- 🎉 no goals
#align no_zero_smul_divisors.algebra_map_injective NoZeroSMulDivisors.algebraMap_injective

theorem _root_.NeZero.of_noZeroSMulDivisors (n : ℕ) [CommRing R] [NeZero (n : R)] [Ring A]
    [Nontrivial A] [Algebra R A] [NoZeroSMulDivisors R A] : NeZero (n : A) :=
  -- porting note: todo: drop implicit args
  @NeZero.nat_of_injective R A (R →+* A) _ _ n ‹_› _ _ <|
    NoZeroSMulDivisors.algebraMap_injective R A
#align ne_zero.of_no_zero_smul_divisors NeZero.of_noZeroSMulDivisors

variable {R A}

theorem iff_algebraMap_injective [CommRing R] [Ring A] [IsDomain A] [Algebra R A] :
    NoZeroSMulDivisors R A ↔ Function.Injective (algebraMap R A) :=
  ⟨@NoZeroSMulDivisors.algebraMap_injective R A _ _ _ _, NoZeroSMulDivisors.of_algebraMap_injective⟩
#align no_zero_smul_divisors.iff_algebra_map_injective NoZeroSMulDivisors.iff_algebraMap_injective

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_nat [Semiring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℕ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℕ R).injective_nat
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_nat NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_nat

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_int [Ring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℤ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℤ R).injective_int
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_int NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_int

section Field

variable [Field R] [Semiring A] [Algebra R A]

-- see note [lower instance priority]
instance (priority := 100) Algebra.noZeroSMulDivisors [Nontrivial A] [NoZeroDivisors A] :
    NoZeroSMulDivisors R A :=
  NoZeroSMulDivisors.of_algebraMap_injective (algebraMap R A).injective
#align no_zero_smul_divisors.algebra.no_zero_smul_divisors NoZeroSMulDivisors.Algebra.noZeroSMulDivisors

end Field

end NoZeroSMulDivisors

section IsScalarTower

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_one, one_smul]
  -- 🎉 no goals
#align algebra_compatible_smul algebra_compatible_smul

@[simp]
theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm
#align algebra_map_smul algebraMap_smul

theorem intCast_smul {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V] (r : ℤ) (x : V) :
    (r : k) • x = r • x :=
  algebraMap_smul k r x
#align int_cast_smul intCast_smul

theorem NoZeroSMulDivisors.trans (R A M : Type*) [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [NoZeroSMulDivisors R A]
    [NoZeroSMulDivisors A M] : NoZeroSMulDivisors R M := by
  refine' ⟨fun {r m} h => _⟩
  -- ⊢ r = 0 ∨ m = 0
  rw [algebra_compatible_smul A r m] at h
  -- ⊢ r = 0 ∨ m = 0
  cases' smul_eq_zero.1 h with H H
  -- ⊢ r = 0 ∨ m = 0
  · have : Function.Injective (algebraMap R A) :=
      NoZeroSMulDivisors.iff_algebraMap_injective.1 inferInstance
    left
    -- ⊢ r = 0
    exact (injective_iff_map_eq_zero _).1 this _ H
    -- 🎉 no goals
  · right
    -- ⊢ m = 0
    exact H
    -- 🎉 no goals
#align no_zero_smul_divisors.trans NoZeroSMulDivisors.trans

variable {A}

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←
      algebra_compatible_smul]⟩
#align is_scalar_tower.to_smul_comm_class IsScalarTower.to_smulCommClass

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_smulCommClass' : SMulCommClass A R M :=
  SMulCommClass.symm _ _ _
#align is_scalar_tower.to_smul_comm_class' IsScalarTower.to_smulCommClass'

-- see Note [lower instance priority]
instance (priority := 200) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]
    [Algebra R A] : SMulCommClass R A A :=
  IsScalarTower.to_smulCommClass
#align algebra.to_smul_comm_class Algebra.to_smulCommClass

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _
#align smul_algebra_smul_comm smul_algebra_smul_comm

namespace LinearMap

variable (R)

#align linear_map.coe_restrict_scalars_eq_coe LinearMap.coe_restrictScalars
#align linear_map.coe_coe_is_scalar_tower LinearMap.coe_restrictScalars

-- porting note: todo: generalize to `CompatibleSMul`
/-- `A`-linearly coerce an `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def ltoFun (R : Type u) (M : Type v) (A : Type w) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] : (M →ₗ[R] A) →ₗ[A] M → A where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.lto_fun LinearMap.ltoFun

end LinearMap

end IsScalarTower

/-! TODO: The following lemmas no longer involve `Algebra` at all, and could be moved closer
to `Algebra/Module/Submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `LinearAlgebra/Basic.lean`. -/

section Module

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
theorem LinearMap.ker_restrictScalars (f : M →ₗ[S] N) :
    LinearMap.ker (f.restrictScalars R) = f.ker.restrictScalars R :=
  rfl
#align linear_map.ker_restrict_scalars LinearMap.ker_restrictScalars

end Module

example {R A} [CommSemiring R] [Semiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm
