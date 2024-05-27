/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.RingTheory.Artinian

#align_import ring_theory.localization.cardinality from "leanprover-community/mathlib"@"3b09a2601bb7690643936643e99bba0fedfbf6ed"

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `ZMod 6` localized at `{2, 4}` is equal to `ZMod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `IsLocalization.uniqueOfZeroMem`).

## Main statements

* `IsLocalization.card_le`: A localization has cardinality no larger than the base ring.
* `IsLocalization.card`: If you don't localize at zero-divisors, the localization of a ring has
  cardinality equal to its base ring,

-/


open Cardinal nonZeroDivisors

universe u v

namespace IsLocalization

variable {R : Type u} [CommRing R] (S : Submonoid R) {L : Type u} [CommRing L] [Algebra R L]
  [IsLocalization S L]

/-- A localization always has cardinality less than or equal to the base ring. -/
theorem card_le : #L ≤ #R := by
  classical
    cases fintypeOrInfinite R
    · exact Cardinal.mk_le_of_surjective (IsArtinianRing.localization_surjective S _)
    erw [← Cardinal.mul_eq_self <| Cardinal.aleph0_le_mk R]
    set f : R × R → L := fun aa => IsLocalization.mk' _ aa.1 (if h : aa.2 ∈ S then ⟨aa.2, h⟩ else 1)
    refine @Cardinal.mk_le_of_surjective _ _ f fun a => ?_
    obtain ⟨x, y, h⟩ := IsLocalization.mk'_surjective S a
    use (x, y)
    dsimp [f]
    rwa [dif_pos <| show ↑y ∈ S from y.2, SetLike.eta]
#align is_localization.card_le IsLocalization.card_le

variable (L)

/-- If you do not localize at any zero-divisors, localization preserves cardinality. -/
theorem card (hS : S ≤ R⁰) : #R = #L :=
  (Cardinal.mk_le_of_injective (IsLocalization.injective L hS)).antisymm (card_le S)
#align is_localization.card IsLocalization.card

end IsLocalization
