/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Star.Center

/-!
# Non-unital Star Subsemirings

In this file we define `NonUnitalStarSubsemiring`s and the usual operations on them.

## Implementation

This file is heavily inspired by `Mathlib.Algebra.Star.NonUnitalSubalgebra`.

-/

universe v w w'

variable {A : Type v} {B : Type w} {C : Type w'}

/-- A non-unital star subset is a subset which is closed under the `star`
operation. -/
structure StarSubset (A : Type v) [Star A] : Type v where
  /-- The underlying set of a `SubStar`. -/
  carrier : Set A
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : A} (_ha : a ∈ carrier), star a ∈ carrier

/-- A sub star magma is a subset of a magma which is closed under the `star`-/
structure SubStarmagma (M : Type v) [Mul M] [Star M] extends Subsemigroup M : Type v where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `SubStarmagma` as a `Subsemigroup`. -/
add_decl_doc SubStarmagma.toSubsemigroup

/-- A non-unital star subsemiring is a non-unital subsemiring which also is closed under the
`star` operation. -/
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R]
    extends NonUnitalSubsemiring R, StarSubset R : Type v

/-- Reinterpret a `NonUnitalStarSubsemiring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring
/-- Reinterpret a `NonUnitalStarSubsemiring` as a `StarSubset`. -/
add_decl_doc NonUnitalStarSubsemiring.toStarSubset

/-- A (unital) star subsemiring is a non-associative ring which is closed under the `star`
operation. -/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R]
    extends Subsemiring R, StarSubset R : Type v

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring
/-- Reinterpret a `StarSubsemiring` as a `StarSubset`. -/
add_decl_doc StarSubsemiring.toStarSubset

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

instance instSetLike : SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
def center (R) [NonUnitalNonAssocSemiring R][StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end NonUnitalStarSubsemiring

end NonUnitalStarSubsemiring

section StarSubsemiring

namespace StarSubsemiring

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

instance instSetLike : SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instSubsemiringClass : SubsemiringClass (StarSubsemiring R) R
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

instance instStarMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    StarSubsemiring R :=
  { S.toSubsemiring.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
def center (R) [NonAssocSemiring R][StarRing R] : StarSubsemiring R where
  toSubsemiring := Subsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end StarSubsemiring

end StarSubsemiring

section StarSubset

namespace StarSubset

variable [Star A]
variable [Star B]
variable [Star C]

instance instSetLike : SetLike (StarSubset A) A where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr

instance instStarMemClass : StarMemClass (StarSubset A) A where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : StarSubset A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : StarSubset A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : StarSubset A) (s : Set A) (hs : s = ↑S) :
    StarSubset A :=
  { star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : StarSubset A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : StarSubset A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

end StarSubset

end StarSubset

section SubStarmagma

variable (A) [Mul A] [StarMul A]

namespace SubStarmagma

/-- The center of `A` is the set of elements that commute and associate
with everything in `A` -/
def center : SubStarmagma A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarmagma

end SubStarmagma
