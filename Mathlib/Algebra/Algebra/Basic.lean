/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.basic
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Module.Ulift
import Mathbin.Algebra.NeZero
import Mathbin.Algebra.PunitInstances
import Mathbin.Algebra.Ring.Aut
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Algebra.CharZero.Lemmas
import Mathbin.LinearAlgebra.Basic
import Mathbin.RingTheory.Subring.Basic
import Mathbin.Tactic.Abel

/-!
# Algebras over commutative semirings

In this file we define associative unital `algebra`s over commutative (semi)rings, algebra
homomorphisms `alg_hom`, and algebra equivalences `alg_equiv`.

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `algebra R A`: the algebra typeclass.
* `algebra_map R A : R →+* A`: the canonical map from `R` to `A`, as a `ring_hom`. This is the
  preferred spelling of this map, it is also available as:
  * `algebra.linear_map R A : R →ₗ[R] A`, a `linear_map`.
  * `algebra.of_id R A : R →ₐ[R] A`, an `alg_hom` (defined in a later file).
* Instances of `algebra` in this file:
  * `algebra.id`
  * `algebra_nat`
  * `algebra_int`
  * `algebra_rat`
  * `mul_opposite.algebra`
  * `module.End.algebra`

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebra_map R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `algebra R A` in a way that subsumes both definitions, by extending `has_smul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebra_map R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variables [comm_semiring R] [semiring A]
   variables [algebra R A]
   ```
2. ```lean
   variables [comm_semiring R] [semiring A]
   variables [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebra_map R A` is available, and `alg_hom R A B` and
`subalgebra R A` can be used. For concrete `R` and `A`, `algebra_map R A` is often definitionally
convenient.

The advantage of the second approach is that `comm_semiring R`, `semiring A`, and `module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `semiring A` with `non_unital_non_assoc_semiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `comm_semiring R` and `module R A` with `comm_group R'` and `distrib_mul_action R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `alg_hom R A B` cannot be used in the second approach, `non_unital_alg_hom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/


universe u v w u₁ v₁

open BigOperators

section Prio

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
-- We set this priority to 0 later in this file
set_option extends_priority 200

/- control priority of
`instance [algebra R A] : has_smul R A` -/
/-- An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
@[nolint has_nonempty_instance]
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where
  commutes' : ∀ r x, to_fun r * x = x * to_fun r
  smul_def' : ∀ r x, r • x = to_fun r * x
#align algebra Algebra

end Prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom
#align algebra_map algebraMap

namespace algebraMap

def hasLiftT (R A : Type _) [CommSemiring R] [Semiring A] [Algebra R A] : HasLiftT R A :=
  ⟨fun r => algebraMap R A r⟩
#align algebra_map.has_lift_t algebraMap.hasLiftT

attribute [instance] algebraMap.hasLiftT

section CommSemiringSemiring

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

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
theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = ↑a ^ n :=
  map_pow (algebraMap R A) _ _
#align algebra_map.coe_pow algebraMap.coe_pow

end CommSemiringSemiring

section CommRingRing

variable {R A : Type _} [CommRing R] [Ring A] [Algebra R A]

@[norm_cast]
theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
  map_neg (algebraMap R A) x
#align algebra_map.coe_neg algebraMap.coe_neg

end CommRingRing

section CommSemiringCommSemiring

variable {R A : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A]

open BigOperators

-- direct to_additive fails because of some mix-up with polynomials
@[norm_cast]
theorem coe_prod {ι : Type _} {s : Finset ι} (a : ι → R) :
    (↑(∏ i : ι in s, a i : R) : A) = ∏ i : ι in s, (↑(a i) : A) :=
  map_prod (algebraMap R A) a s
#align algebra_map.coe_prod algebraMap.coe_prod

-- to_additive fails for some reason
@[norm_cast]
theorem coe_sum {ι : Type _} {s : Finset ι} (a : ι → R) :
    ↑(∑ i : ι in s, a i) = ∑ i : ι in s, (↑(a i) : A) :=
  map_sum (algebraMap R A) a s
#align algebra_map.coe_sum algebraMap.coe_sum

attribute [to_additive] coe_prod

end CommSemiringCommSemiring

section FieldNontrivial

variable {R A : Type _} [Field R] [CommSemiring A] [Nontrivial A] [Algebra R A]

@[norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (algebraMap R A).Injective.eq_iff
#align algebra_map.coe_inj algebraMap.coe_inj

@[norm_cast, simp]
theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
  map_eq_zero_iff _ (algebraMap R A).Injective
#align algebra_map.lift_map_eq_zero_iff algebraMap.lift_map_eq_zero_iff

end FieldNontrivial

section SemifieldSemidivisionRing

variable {R : Type _} (A : Type _) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r
#align algebra_map.coe_inv algebraMap.coe_inv

@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s
#align algebra_map.coe_div algebraMap.coe_div

@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (↑r ^ z : A) :=
  map_zpow₀ (algebraMap R A) r z
#align algebra_map.coe_zpow algebraMap.coe_zpow

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type _) [Field R] [DivisionRing A] [Algebra R A]

@[norm_cast]
theorem coe_rat_cast (q : ℚ) : ↑(q : R) = (q : A) :=
  map_ratCast (algebraMap R A) q
#align algebra_map.coe_rat_cast algebraMap.coe_rat_cast

end FieldDivisionRing

end algebraMap

/-- Creating an algebra from a morphism to the center of a semiring. -/
def RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) : Algebra R S
    where
  smul c x := i c * x
  commutes' := h
  smul_def' c x := rfl
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

variable {R : Type u} {S : Type v} {A : Type w} {B : Type _}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule' [CommSemiring R] [Semiring A] [Module R A] (h₁ : ∀ (r : R) (x : A), r • 1 * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * r • 1 = r • x) : Algebra R A
    where
  toFun r := r • 1
  map_one' := one_smul _ _
  map_mul' r₁ r₂ := by rw [h₁, mul_smul]
  map_zero' := zero_smul _ _
  map_add' r₁ r₂ := add_smul r₁ r₂ 1
  commutes' r x := by simp only [h₁, h₂]
  smul_def' r x := by simp only [h₁]
#align algebra.of_module' Algebra.ofModule'

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]
#align algebra.of_module Algebra.ofModule

section Semiring

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- We keep this lemma private because it picks up the `algebra.to_has_smul` instance
which we set to priority 0 shortly. See `smul_def` below for the public version. -/
private theorem smul_def'' (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x
#align algebra.smul_def'' algebra.smul_def''

-- We'll later use this to show `algebra ℤ M` is a subsingleton.
/-- To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
@[ext]
theorem algebra_ext {R : Type _} [CommSemiring R] {A : Type _} [Semiring A] (P Q : Algebra R A)
    (w :
      ∀ r : R,
        (haveI := P
          algebraMap R A r) =
          haveI := Q
          algebraMap R A r) :
    P = Q := by
  rcases P with @⟨⟨P⟩⟩
  rcases Q with @⟨⟨Q⟩⟩
  congr
  · funext r a
    replace w := congr_arg (fun s => s * a) (w r)
    simp only [← smul_def''] at w
    apply w
  · ext r
    exact w r
  · apply proof_irrel_heq
  · apply proof_irrel_heq
#align algebra.algebra_ext Algebra.algebra_ext

-- see Note [lower instance priority]
instance (priority := 200) toModule : Module R A
    where
  one_smul := by simp [smul_def'']
  mul_smul := by simp [smul_def'', mul_assoc]
  smul_add := by simp [smul_def'', mul_add]
  smul_zero := by simp [smul_def'']
  add_smul := by simp [smul_def'', add_mul]
  zero_smul := by simp [smul_def'']
#align algebra.to_module Algebra.toModule

-- From now on, we don't want to use the following instance anymore.
-- Unfortunately, leaving it in place causes deterministic timeouts later in mathlib.
attribute [instance] Algebra.toHasSmul

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x
#align algebra.smul_def Algebra.smul_def

theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • 1 :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • 1 := (Algebra.smul_def r 1).symm
    
#align algebra.algebra_map_eq_smul_one Algebra.algebraMap_eq_smul_one

theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebraMap_eq_smul_one
#align algebra.algebra_map_eq_smul_one' Algebra.algebraMap_eq_smul_one'

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x
#align algebra.commutes Algebra.commutes

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← commutes, mul_assoc]
#align algebra.left_comm Algebra.left_comm

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) : x * algebraMap R A r * y = x * y * algebraMap R A r :=
  by rw [mul_assoc, commutes, ← mul_assoc]
#align algebra.right_comm Algebra.right_comm

instance IsScalarTower.right : IsScalarTower R A A :=
  ⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩
#align is_scalar_tower.right IsScalarTower.right

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) :=
  by-- TODO: set up `is_scalar_tower.smul_comm_class` earlier so that we can actually prove this using
  -- `mul_smul_comm s x y`.
  rw [smul_def, smul_def, left_comm]
#align algebra.mul_smul_comm Algebra.mul_smul_comm

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y
#align algebra.smul_mul_assoc Algebra.smul_mul_assoc

@[simp]
theorem smul_algebraMap {α : Type _} [Monoid α] [MulDistribMulAction α A] [SMulCommClass α R A]
    (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [algebra_map_eq_smul_one, smul_comm a r (1 : A), smul_one]
#align smul_algebra_map smul_algebraMap

section

variable {r : R} {a : A}

@[simp]
theorem bit0_smul_one : bit0 r • (1 : A) = bit0 (r • (1 : A)) := by simp [bit0, add_smul]
#align algebra.bit0_smul_one Algebra.bit0_smul_one

theorem bit0_smul_one' : bit0 r • (1 : A) = r • 2 := by simp [bit0, add_smul, smul_add]
#align algebra.bit0_smul_one' Algebra.bit0_smul_one'

@[simp]
theorem bit0_smul_bit0 : bit0 r • bit0 a = r • bit0 (bit0 a) := by simp [bit0, add_smul, smul_add]
#align algebra.bit0_smul_bit0 Algebra.bit0_smul_bit0

@[simp]
theorem bit0_smul_bit1 : bit0 r • bit1 a = r • bit0 (bit1 a) := by simp [bit0, add_smul, smul_add]
#align algebra.bit0_smul_bit1 Algebra.bit0_smul_bit1

@[simp]
theorem bit1_smul_one : bit1 r • (1 : A) = bit1 (r • (1 : A)) := by simp [bit1, add_smul]
#align algebra.bit1_smul_one Algebra.bit1_smul_one

theorem bit1_smul_one' : bit1 r • (1 : A) = r • 2 + 1 := by simp [bit1, bit0, add_smul, smul_add]
#align algebra.bit1_smul_one' Algebra.bit1_smul_one'

@[simp]
theorem bit1_smul_bit0 : bit1 r • bit0 a = r • bit0 (bit0 a) + bit0 a := by
  simp [bit1, add_smul, smul_add]
#align algebra.bit1_smul_bit0 Algebra.bit1_smul_bit0

@[simp]
theorem bit1_smul_bit1 : bit1 r • bit1 a = r • bit0 (bit1 a) + bit1 a :=
  by
  simp only [bit0, bit1, add_smul, smul_add, one_smul]
  abel
#align algebra.bit1_smul_bit1 Algebra.bit1_smul_bit1

end

variable (R A)

/-- The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linearMap : R →ₗ[R] A :=
  { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }
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

instance PUnit.algebra : Algebra R PUnit
    where
  toFun x := PUnit.unit
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

instance ULift.algebra : Algebra R (ULift A) :=
  { ULift.module',
    (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp
      (algebraMap R A) with
    toFun := fun r => ULift.up (algebraMap R A r)
    commutes' := fun r x => ULift.down_injective <| Algebra.commutes r x.down
    smul_def' := fun r x => ULift.down_injective <| Algebra.smul_def' r x.down }
#align ulift.algebra ULift.algebra

theorem ULift.algebraMap_eq (r : R) : algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl
#align ulift.algebra_map_eq ULift.algebraMap_eq

@[simp]
theorem ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl
#align ulift.down_algebra_map ULift.down_algebraMap

end ULift

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance ofSubsemiring (S : Subsemiring R) : Algebra S A :=
  { (algebraMap R A).comp S.Subtype with
    smul := (· • ·)
    commutes' := fun r x => Algebra.commutes r x
    smul_def' := fun r x => Algebra.smul_def r x }
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

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance ofSubring {R A : Type _} [CommRing R] [Ring A] [Algebra R A] (S : Subring R) :
    Algebra S A :=
  { Algebra.ofSubsemiring S.toSubsemiring, (algebraMap R A).comp S.Subtype with smul := (· • ·) }
#align algebra.of_subring Algebra.ofSubring

theorem algebraMap_ofSubring {R : Type _} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl
#align algebra.algebra_map_of_subring Algebra.algebraMap_ofSubring

theorem coe_algebraMap_ofSubring {R : Type _} [CommRing R] (S : Subring R) :
    (algebraMap S R : S → R) = Subtype.val :=
  rfl
#align algebra.coe_algebra_map_of_subring Algebra.coe_algebraMap_ofSubring

theorem algebraMap_ofSubring_apply {R : Type _} [CommRing R] (S : Subring R) (x : S) :
    algebraMap S R x = x :=
  rfl
#align algebra.algebra_map_of_subring_apply Algebra.algebraMap_ofSubring_apply

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebraMapSubmonoid (S : Type _) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)
#align algebra.algebra_map_submonoid Algebra.algebraMapSubmonoid

theorem mem_algebraMapSubmonoid_of_mem {S : Type _} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2
#align algebra.mem_algebra_map_submonoid_of_mem Algebra.mem_algebraMapSubmonoid_of_mem

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]
#align algebra.mul_sub_algebra_map_commutes Algebra.mul_sub_algebraMap_commutes

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x :=
  by
  induction' n with n ih
  · simp
  · rw [pow_succ, ← mul_assoc, mul_sub_algebra_map_commutes, mul_assoc, ih, ← mul_assoc]
#align algebra.mul_sub_algebra_map_pow_commutes Algebra.mul_sub_algebraMap_pow_commutes

end CommSemiring

section Ring

variable [CommRing R]

variable (R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiringToRing [Semiring A] [Algebra R A] : Ring A :=
  { Module.addCommMonoidToAddCommGroup R, (inferInstance : Semiring A) with }
#align algebra.semiring_to_ring Algebra.semiringToRing

end Ring

end Algebra

namespace MulOpposite

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

instance : Algebra R Aᵐᵒᵖ :=
  {
    MulOpposite.hasSmul A
      R with
    toRingHom := (algebraMap R A).toOpposite fun x y => Algebra.commutes _ _
    smul_def' := fun c x =>
      unop_injective <| by
        dsimp
        simp only [op_mul, Algebra.smul_def, Algebra.commutes, op_unop]
    commutes' := fun r =>
      MulOpposite.rec' fun x => by dsimp <;> simp only [← op_mul, Algebra.commutes] }

@[simp]
theorem algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) :=
  rfl
#align mul_opposite.algebra_map_apply MulOpposite.algebraMap_apply

end MulOpposite

namespace Module

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

instance : Algebra R (Module.End R M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

theorem algebraMap_end_eq_smul_id (a : R) : (algebraMap R (End R M)) a = a • LinearMap.id :=
  rfl
#align module.algebra_map_End_eq_smul_id Module.algebraMap_end_eq_smul_id

@[simp]
theorem algebraMap_end_apply (a : R) (m : M) : (algebraMap R (End R M)) a m = a • m :=
  rfl
#align module.algebra_map_End_apply Module.algebraMap_end_apply

@[simp]
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] (a : K)
    (ha : a ≠ 0) : ((algebraMap K (End K V)) a).ker = ⊥ :=
  LinearMap.ker_smul _ _ ha
#align module.ker_algebra_map_End Module.ker_algebraMap_end

section

variable {R M}

theorem end_isUnit_apply_inv_apply_of_isUnit {f : Module.End R M} (h : IsUnit f) (x : M) :
    f (h.Unit.inv x) = x :=
  show (f * h.Unit.inv) x = x by simp
#align module.End_is_unit_apply_inv_apply_of_is_unit Module.end_isUnit_apply_inv_apply_of_isUnit

theorem end_isUnit_inv_apply_apply_of_isUnit {f : Module.End R M} (h : IsUnit f) (x : M) :
    h.Unit.inv (f x) = x :=
  (by simp : (h.Unit.inv * f) x = x)
#align module.End_is_unit_inv_apply_apply_of_is_unit Module.end_isUnit_inv_apply_apply_of_isUnit

theorem end_isUnit_iff (f : Module.End R M) : IsUnit f ↔ Function.Bijective f :=
  ⟨fun h =>
    Function.bijective_iff_has_inverse.mpr <|
      ⟨h.Unit.inv,
        ⟨end_isUnit_inv_apply_apply_of_isUnit h, end_isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H =>
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, LinearMap.ext e.left_inv⟩, rfl⟩⟩
#align module.End_is_unit_iff Module.end_isUnit_iff

theorem end_algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End R M) x)) (m m' : M) : h.Unit⁻¹ m = m' ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.Unit H).symm.trans (end_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun h.unit using ((Module.end_isUnit_iff _).mp h).Injective
        erw [End_is_unit_apply_inv_apply_of_is_unit]
        rfl }
#align module.End_algebra_map_is_unit_inv_apply_eq_iff Module.end_algebraMap_isUnit_inv_apply_eq_iff

theorem end_algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End R M) x)) (m m' : M) : m' = h.Unit⁻¹ m ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.Unit H).trans (end_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun h.unit using ((Module.end_isUnit_iff _).mp h).Injective
        erw [End_is_unit_apply_inv_apply_of_is_unit]
        rfl }
#align module.End_algebra_map_is_unit_inv_apply_eq_iff' Module.end_algebraMap_isUnit_inv_apply_eq_iff'

end

end Module

namespace LinearMap

variable {R : Type _} {A : Type _} {B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An alternate statement of `linear_map.map_smul` for when `algebra_map` is more convenient to
work with than `•`. -/
theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul]
#align linear_map.map_algebra_map_mul LinearMap.map_algebraMap_mul

theorem map_mul_algebraMap (f : A →ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes, ← Algebra.commutes, map_algebra_map_mul]
#align linear_map.map_mul_algebra_map LinearMap.map_mul_algebraMap

end LinearMap

@[simp]
theorem Rat.smul_one_eq_coe {A : Type _} [DivisionRing A] [Algebra ℚ A] (m : ℚ) :
    @SMul.smul Algebra.toHasSmul m (1 : A) = ↑m := by rw [Algebra.smul_def, mul_one, eq_ratCast]
#align rat.smul_one_eq_coe Rat.smul_one_eq_coe

section Nat

variable {R : Type _} [Semiring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `algebra.id` and `algebra_nat` are not yet defeq.
-- TODO: fix this by adding an `of_nat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99) algebraNat : Algebra ℕ R
    where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  toRingHom := Nat.castRingHom R
#align algebra_nat algebraNat

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by
    ext
    simp⟩
#align nat_algebra_subsingleton nat_algebra_subsingleton

end Nat

namespace RingHom

variable {R S : Type _}

-- note that `R`, `S` could be `semiring`s but this is useless mathematically speaking -
-- a ℚ-algebra is a ring. furthermore, this change probably slows down elaboration.
@[simp]
theorem map_rat_algebraMap [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) (r : ℚ) :
    f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r
#align ring_hom.map_rat_algebra_map RingHom.map_rat_algebraMap

end RingHom

section Rat

instance algebraRat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α
    where
  smul := (· • ·)
  smul_def' := DivisionRing.qsmul_eq_mul'
  toRingHom := Rat.castHom α
  commutes' := Rat.cast_commute
#align algebra_rat algebraRat

/-- The two `algebra ℚ ℚ` instances should coincide. -/
example : algebraRat = Algebra.id ℚ :=
  rfl

@[simp]
theorem algebraMap_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ :=
  Subsingleton.elim _ _
#align algebra_map_rat_rat algebraMap_rat_rat

instance algebra_rat_subsingleton {α} [Semiring α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align algebra_rat_subsingleton algebra_rat_subsingleton

end Rat

section Int

variable (R : Type _) [Ring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `algebra.id ℤ` and `algebra_int ℤ` are not yet defeq.
-- TODO: fix this by adding an `of_int` field to rings.
/-- Ring ⥤ ℤ-Alg -/
instance (priority := 99) algebraInt : Algebra ℤ R
    where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  toRingHom := Int.castRingHom R
#align algebra_int algebraInt

/-- A special case of `eq_int_cast'` that happens to be true definitionally -/
@[simp]
theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl
#align algebra_map_int_eq algebraMap_int_eq

variable {R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => by
    ext
    simp⟩
#align int_algebra_subsingleton int_algebra_subsingleton

end Int

namespace NoZeroSMulDivisors

variable {R A : Type _}

open Algebra

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
theorem of_algebraMap_injective [CommSemiring R] [Semiring A] [Algebra R A] [NoZeroDivisors A]
    (h : Function.Injective (algebraMap R A)) : NoZeroSMulDivisors R A :=
  ⟨fun c x hcx =>
    (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left
      (map_eq_zero_iff (algebraMap R A) h).mp⟩
#align no_zero_smul_divisors.of_algebra_map_injective NoZeroSMulDivisors.of_algebraMap_injective

variable (R A)

theorem algebraMap_injective [CommRing R] [Ring A] [Nontrivial A] [Algebra R A]
    [NoZeroSMulDivisors R A] : Function.Injective (algebraMap R A) :=
  suffices Function.Injective fun c : R => c • (1 : A)
    by
    convert this
    ext
    rw [Algebra.smul_def, mul_one]
  smul_left_injective R one_ne_zero
#align no_zero_smul_divisors.algebra_map_injective NoZeroSMulDivisors.algebraMap_injective

theorem NeZero.of_noZeroSMulDivisors (n : ℕ) [CommRing R] [NeZero (n : R)] [Ring A] [Nontrivial A]
    [Algebra R A] [NoZeroSMulDivisors R A] : NeZero (n : A) :=
  NeZero.nat_of_injective <| NoZeroSMulDivisors.algebraMap_injective R A
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
  NoZeroSMulDivisors.of_algebraMap_injective (algebraMap R A).Injective
#align no_zero_smul_divisors.algebra.no_zero_smul_divisors NoZeroSMulDivisors.Algebra.noZeroSMulDivisors

end Field

end NoZeroSMulDivisors

section IsScalarTower

variable {R : Type _} [CommSemiring R]

variable (A : Type _) [Semiring A] [Algebra R A]

variable {M : Type _} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

variable {N : Type _} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_one, one_smul]
#align algebra_compatible_smul algebra_compatible_smul

@[simp]
theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm
#align algebra_map_smul algebraMap_smul

theorem int_cast_smul {k V : Type _} [CommRing k] [AddCommGroup V] [Module k V] (r : ℤ) (x : V) :
    (r : k) • x = r • x :=
  algebraMap_smul k r x
#align int_cast_smul int_cast_smul

theorem NoZeroSMulDivisors.trans (R A M : Type _) [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [NoZeroSMulDivisors R A]
    [NoZeroSMulDivisors A M] : NoZeroSMulDivisors R M :=
  by
  refine' ⟨fun r m h => _⟩
  rw [algebra_compatible_smul A r m] at h
  cases' smul_eq_zero.1 h with H H
  · have : Function.Injective (algebraMap R A) :=
      NoZeroSMulDivisors.iff_algebraMap_injective.1 inferInstance
    left
    exact (injective_iff_map_eq_zero _).1 this _ H
  · right
    exact H
#align no_zero_smul_divisors.trans NoZeroSMulDivisors.trans

variable {A}

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_sMulCommClass : SMulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←
      algebra_compatible_smul]⟩
#align is_scalar_tower.to_smul_comm_class IsScalarTower.to_sMulCommClass

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_smul_comm_class' : SMulCommClass A R M :=
  SMulCommClass.symm _ _ _
#align is_scalar_tower.to_smul_comm_class' IsScalarTower.to_smul_comm_class'

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _
#align smul_algebra_smul_comm smul_algebra_smul_comm

namespace LinearMap

instance coeIsScalarTower : Coe (M →ₗ[A] N) (M →ₗ[R] N) :=
  ⟨restrictScalars R⟩
#align linear_map.coe_is_scalar_tower LinearMap.coeIsScalarTower

variable (R) {A M N}

@[simp, norm_cast squash]
theorem coe_restrictScalars_eq_coe (f : M →ₗ[A] N) : (f.restrictScalars R : M → N) = f :=
  rfl
#align linear_map.coe_restrict_scalars_eq_coe LinearMap.coe_restrictScalars_eq_coe

@[simp, norm_cast squash]
theorem coe_coeIsScalarTower (f : M →ₗ[A] N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl
#align linear_map.coe_coe_is_scalar_tower LinearMap.coe_coeIsScalarTower

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def ltoFun (R : Type u) (M : Type v) (A : Type w) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommRing A] [Algebra R A] : (M →ₗ[R] A) →ₗ[A] M → A
    where
  toFun := LinearMap.toFun
  map_add' f g := rfl
  map_smul' c f := rfl
#align linear_map.lto_fun LinearMap.ltoFun

end LinearMap

end IsScalarTower

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/


section Module

open Module

variable (R S M N : Type _) [Semiring R] [Semiring S] [SMul R S]

variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

variable {S M N}

@[simp]
theorem LinearMap.ker_restrictScalars (f : M →ₗ[S] N) :
    (f.restrictScalars R).ker = f.ker.restrictScalars R :=
  rfl
#align linear_map.ker_restrict_scalars LinearMap.ker_restrictScalars

end Module

example {R A} [CommSemiring R] [Semiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

