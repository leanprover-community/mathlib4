/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!

# Localizations of domains as subalgebras of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/


namespace Localization

open nonZeroDivisors

variable {A : Type*} (K : Type*) [CommRing A] (S : Submonoid A) (hS : S ≤ A⁰)

section CommRing

variable [CommRing K] [Algebra A K] [IsFractionRing A K]

theorem map_isUnit_of_le (hS : S ≤ A⁰) (s : S) : IsUnit (algebraMap A K s) := by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

/-- The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`. -/
noncomputable def mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : B →ₐ[A] K :=
  { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }

@[simp]
theorem mapToFractionRing_apply {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (b : B) :
    mapToFractionRing K S B hS b = IsLocalization.lift (map_isUnit_of_le K S hS) b :=
  rfl

theorem mem_range_mapToFractionRing_iff (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔
      ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ :=
  ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩

instance isLocalization_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsLocalization S (mapToFractionRing K S B hS).range :=
  IsLocalization.isLocalization_of_algEquiv S <|
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine ⟨fun a b h => ?_, Set.surjective_onto_range⟩
      refine (IsLocalization.lift_injective_iff _).2 (fun a b => ?_) (Subtype.ext_iff.1 h)
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)

instance isFractionRing_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsFractionRing (mapToFractionRing K S B hS).range K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

/-- Given a commutative ring `A` with fraction ring `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`IsLocalization.mk' K a ⟨s, _⟩`, where `s ∈ S`.
-/
noncomputable def subalgebra (hS : S ≤ A⁰) : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff

namespace subalgebra

instance isLocalization_subalgebra : IsLocalization S (subalgebra K S hS) := by
  dsimp only [Localization.subalgebra]
  rw [Subalgebra.copy_eq]
  infer_instance

instance isFractionRing : IsFractionRing (subalgebra K S hS) K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

end subalgebra

end CommRing

section Field

variable [Field K] [Algebra A K] [IsFractionRing A K]

namespace subalgebra

theorem mem_range_mapToFractionRing_iff_ofField (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔
      ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  rw [mem_range_mapToFractionRing_iff]
  convert Iff.rfl
  congr
  rw [Units.val_inv_eq_inv_val]
  rfl

/-- Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`algebraMap A K a * (algebraMap A K s)⁻¹` where `a s : A` and `s ∈ S`.
-/
noncomputable def ofField : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField

theorem ofField_eq : ofField K S hS = subalgebra K S hS := by
  simp_rw [ofField, subalgebra, Subalgebra.copy_eq]

instance isLocalization_ofField : IsLocalization S (ofField K S hS) := by
  rw [ofField_eq]
  exact isLocalization_subalgebra K S hS

instance (S : Subalgebra A K) : IsFractionRing S K := by
  refine IsFractionRing.of_field S K fun z ↦ ?_
  rcases IsFractionRing.div_surjective (A := A) z with ⟨x, y, _, eq⟩
  exact ⟨algebraMap A S x, algebraMap A S y, eq.symm⟩

instance isFractionRing_ofField : IsFractionRing (ofField K S hS) K :=
  inferInstance

end subalgebra

end Field

end Localization
