/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Submonoid.Saturation
import Mathlib.RingTheory.Localization.Defs

/-! # Localization and submonoid saturation

In this file we show that `A` is a localization of `R` on the submonoid `S` iff it is so on the
saturation of `S`.

Crucially, the saturation of `S` is precisely the elements that become a unit in `A`.

-/

namespace IsLocalization
variable {R : Type*} [CommRing R] {S : Submonoid R} {A : Type*} [CommRing A] [Algebra R A]

open Submonoid

variable (S A) in
theorem mem_saturation_iff_isUnit_algebraMap [IsLocalization S A] {x : R} :
    x ∈ S.saturation ↔ IsUnit (algebraMap R A x) := by
  rw [IsLocalization.algebraMap_isUnit_iff S, Submonoid.mem_saturation_iff_exists_dvd]

variable (S) in
theorem of_saturation_eq [IsLocalization S A] (T : Submonoid R) (ih : S.saturation = T.saturation) :
    IsLocalization T A := by
  refine ⟨fun x ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} eq ↦ ?_⟩
  · rw [← mem_saturation_iff_isUnit_algebraMap S A, ih]
    exact le_toSubmonoid_saturation x.2
  · obtain ⟨⟨x₁, ⟨x₂, hx₂⟩⟩, h⟩ := IsLocalization.surj S y
    obtain ⟨x₃, hx₃⟩ : x₂ ∈ T.saturation := ih ▸ le_toSubmonoid_saturation hx₂
    exact ⟨(x₁ * x₃, ⟨_, hx₃⟩), by simpa [mul_assoc] using congr($h * algebraMap R A x₃)⟩
  · obtain ⟨⟨x₃, hx₃⟩, eq⟩ := IsLocalization.exists_of_eq (M := S) eq
    obtain ⟨x₄, hx₄⟩ : x₃ ∈ T.saturation := ih ▸ le_toSubmonoid_saturation hx₃
    exact ⟨⟨_, hx₄⟩, by simpa [mul_right_comm] using congr($eq * x₄)⟩

theorem saturation_iff : IsLocalization S.saturation.toSubmonoid A ↔ IsLocalization S A :=
  ⟨fun h ↦ .of_saturation_eq S.saturation.toSubmonoid _ <| by simp,
  fun h ↦ .of_saturation_eq S _ <| by simp⟩

end IsLocalization
