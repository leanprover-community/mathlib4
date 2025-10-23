/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
import Mathlib.Algebra.Star.Center

/-!
# Non-unital Star Subsemirings

In this file we define `NonUnitalStarSubsemiring`s and the usual operations on them.

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`.

-/

universe v w w'

variable {A : Type v} {B : Type w} {C : Type w'}

/-- A sub star semigroup is a subset of a magma which is closed under the `star`. -/
structure SubStarSemigroup (M : Type v) [Mul M] [Star M] : Type v
    extends Subsemigroup M where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `SubStarSemigroup` as a `Subsemigroup`. -/
add_decl_doc SubStarSemigroup.toSubsemigroup

/-- A non-unital star subsemiring is a non-unital subsemiring which also is closed under the
`star` operation. -/
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R] : Type v
    extends NonUnitalSubsemiring R where
  /-- The `carrier` of a `NonUnitalStarSubsemiring` is closed under the `star` operation. -/
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubsemiring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

instance instSetLike {R : Type v} [NonUnitalNonAssocSemiring R] [Star R] :
    SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

initialize_simps_projections NonUnitalStarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

/-- The actual `NonUnitalStarSubsemiring` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `StarMemClass`. -/
@[simps]
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : NonUnitalStarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalStarSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      ∀ {x}, x ∈ s → star x ∈ s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩

instance instNonUnitalSubsemiringClass :
    NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subsemiring with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x ∈ s) => by
      change star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a non-unital non-associative semiring `R` is the set of elements that
commute and associate with everything in `R`, here realized as non-unital star
subsemiring. -/
def center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end NonUnitalStarSubsemiring

end NonUnitalStarSubsemiring
