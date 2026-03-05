/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Saturation
public import Mathlib.RingTheory.Localization.Basic

/-! # Localization and submonoid saturation

In this file we show that `A` is a localization of `R` on the submonoid `S` iff it is so on the
saturation of `S`.

Crucially, the saturation of `S` is precisely the elements that become a unit in `A`.

-/

@[expose] public section

namespace IsLocalization
variable {R : Type*} [CommRing R] {S T : Submonoid R} {A : Type*} [CommRing A] [Algebra R A]

open Submonoid

variable (S A) in
theorem mem_saturation_iff_isUnit_algebraMap [IsLocalization S A] {x : R} :
    x ∈ S.saturation ↔ IsUnit (algebraMap R A x) := by
  rw [IsLocalization.algebraMap_isUnit_iff S, Submonoid.mem_saturation_iff_exists_dvd]

theorem saturation_iff : IsLocalization S.saturation.toSubmonoid A ↔ IsLocalization S A :=
  .symm <| iff_of_le_of_exists_dvd _ _ le_toSubmonoid_saturation <| by
    simp [mem_saturation_iff_exists_dvd]

variable (S T) in
theorem of_saturation_eq [IsLocalization S A] (ih : S.saturation = T.saturation) :
    IsLocalization T A := by
  rwa [← saturation_iff, ← ih, saturation_iff]

end IsLocalization
