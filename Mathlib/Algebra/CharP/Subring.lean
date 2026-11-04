/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Algebra

/-!
# Characteristic of subrings
-/

public section


universe u v

section CharP

theorem SubsemiringClass.charP_iff {R : Type u} {S : Type v} [SetLike S R]
    [NonAssocSemiring R] [SubsemiringClass S R] {p : ℕ} {s : S} :
    CharP s p ↔ CharP R p :=
  (Subsemiring.subtype (.ofClass s)).charP_iff (Subsemiring.subtype_injective _) p

/-- The characteristic of a division ring is equal to the characteristic
  of its center -/
@[deprecated SubsemiringClass.charP_iff +typeChanged (since := "2026-10-15")]
theorem CharP.charP_center_iff {R : Type u} [Ring R] {p : ℕ} :
    CharP (Subring.center R) p ↔ CharP R p := SubsemiringClass.charP_iff

instance {R : Type u} {S : Type v} [SetLike S R]
    [NonAssocSemiring R] [SubsemiringClass S R] {p : ℕ} [CharP R p] (s : S) :
    CharP s p := SubsemiringClass.charP_iff.2 ‹_›

end CharP

section ExpChar

theorem SubsemiringClass.expChar_iff {R : Type u} {S : Type v} [SetLike S R]
    [NonAssocSemiring R] [SubsemiringClass S R] {p : ℕ} {s : S} :
    ExpChar s p ↔ ExpChar R p :=
  (Subsemiring.subtype (.ofClass s)).expChar_iff (Subsemiring.subtype_injective _) p

@[deprecated SubsemiringClass.expChar_iff +typeChanged (since := "2026-10-15")]
theorem ExpChar.expChar_center_iff {R : Type u} [Ring R] {p : ℕ} :
    ExpChar (Subring.center R) p ↔ ExpChar R p :=
  (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

instance {R : Type u} {S : Type v} [SetLike S R]
    [NonAssocSemiring R] [SubsemiringClass S R] {p : ℕ} [ExpChar R p] (s : S) :
    ExpChar s p := SubsemiringClass.expChar_iff.2 ‹_›

end ExpChar
