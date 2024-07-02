/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Star.Basic

/-!
# The *-ring structure on suitable quotients of a *-ring.
-/

namespace RingQuot

universe u

variable {R : Type u} [Semiring R] (r : R → R → Prop)

section StarRing

variable [StarRing R] (hr : ∀ a b, r a b → r (star a) (star b))

theorem Rel.star ⦃a b : R⦄ (h : Rel r a b) : Rel r (star a) (star b) := by
  induction h with
  | of h          => exact Rel.of (hr _ _ h)
  | add_left _ h  => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h  => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h
#align ring_quot.rel.star RingQuot.Rel.star

private irreducible_def star' : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (star : R → R) (Rel.star r hr) a⟩

theorem star'_quot (hr : ∀ a b, r a b → r (star a) (star b)) {a} :
    (star' r hr ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (star a)⟩ := star'_def _ _ _
#align ring_quot.star'_quot RingQuot.star'_quot

/-- Transfer a star_ring instance through a quotient, if the quotient is invariant to `star` -/
def starRing {R : Type u} [Semiring R] [StarRing R] (r : R → R → Prop)
    (hr : ∀ a b, r a b → r (star a) (star b)) : StarRing (RingQuot r) where
  star := star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]
#align ring_quot.star_ring RingQuot.starRing

end StarRing

end RingQuot
