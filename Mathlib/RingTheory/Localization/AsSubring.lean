/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
import Mathlib.RingTheory.Localization.LocalizationLocalization

#align_import ring_theory.localization.as_subring from "leanprover-community/mathlib"@"649ca66bf4d62796b5eefef966e622d91aa471f3"

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
  -- 🎉 no goals
#align localization.map_is_unit_of_le Localization.map_isUnit_of_le

/-- The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`. -/
noncomputable def mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : B →ₐ[A] K :=
  { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }
                                                                                -- 🎉 no goals
#align localization.map_to_fraction_ring Localization.mapToFractionRing

@[simp]
theorem mapToFractionRing_apply {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (b : B) :
    mapToFractionRing K S B hS b = IsLocalization.lift (map_isUnit_of_le K S hS) b :=
  rfl
#align localization.map_to_fraction_ring_apply Localization.mapToFractionRing_apply

theorem mem_range_mapToFractionRing_iff (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔
      ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ :=
  ⟨by
    rintro ⟨x, rfl⟩
    -- ⊢ ∃ a s hs, ↑↑(mapToFractionRing K S B hS) x = IsLocalization.mk' K a { val := …
    obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective S x
    -- ⊢ ∃ a_1 s_1 hs, ↑↑(mapToFractionRing K S B hS) (IsLocalization.mk' B a s) = Is …
    use a, s, s.2
    -- ⊢ ↑↑(mapToFractionRing K S B hS) (IsLocalization.mk' B a s) = IsLocalization.m …
    apply IsLocalization.lift_mk', by
    -- 🎉 no goals
    rintro ⟨a, s, hs, rfl⟩
    -- ⊢ IsLocalization.mk' K a { val := s, property := (_ : s ∈ A⁰) } ∈ AlgHom.range …
    use IsLocalization.mk' _ a ⟨s, hs⟩
    -- ⊢ ↑↑(mapToFractionRing K S B hS) (IsLocalization.mk' B a { val := s, property  …
    apply IsLocalization.lift_mk'⟩
    -- 🎉 no goals
#align localization.mem_range_map_to_fraction_ring_iff Localization.mem_range_mapToFractionRing_iff

instance isLocalization_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsLocalization S (mapToFractionRing K S B hS).range :=
  IsLocalization.isLocalization_of_algEquiv S <|
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine' ⟨fun a b h => _, Set.surjective_onto_range⟩
      -- ⊢ a = b
      refine' (IsLocalization.lift_injective_iff _).2 (fun a b => _) (Subtype.ext_iff.1 h)
      -- ⊢ ↑(algebraMap A B) a = ↑(algebraMap A B) b ↔ ↑(algebraMap A K) a = ↑(algebraM …
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)
#align localization.is_localization_range_map_to_fraction_ring Localization.isLocalization_range_mapToFractionRing

instance isFractionRing_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsFractionRing (mapToFractionRing K S B hS).range K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS
#align localization.is_fraction_ring_range_map_to_fraction_ring Localization.isFractionRing_range_mapToFractionRing

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
    -- ⊢ x✝ ∈ {x | ∃ a s hs, x = IsLocalization.mk' K a { val := s, property := (_ :  …
    symm
    -- ⊢ x✝ ∈ ↑(AlgHom.range (mapToFractionRing K S (Localization S) hS)) ↔ x✝ ∈ {x | …
    apply mem_range_mapToFractionRing_iff
    -- 🎉 no goals
#align localization.subalgebra Localization.subalgebra

namespace subalgebra

instance isLocalization_subalgebra : IsLocalization S (subalgebra K S hS) := by
  dsimp only [Localization.subalgebra]
  -- ⊢ IsLocalization S { x // x ∈ Subalgebra.copy (AlgHom.range (mapToFractionRing …
  rw [Subalgebra.copy_eq]
  -- ⊢ IsLocalization S { x // x ∈ AlgHom.range (mapToFractionRing K S (Localizatio …
  infer_instance
  -- 🎉 no goals
#align localization.subalgebra.is_localization_subalgebra Localization.subalgebra.isLocalization_subalgebra

instance isFractionRing : IsFractionRing (subalgebra K S hS) K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS
#align localization.subalgebra.is_fraction_ring Localization.subalgebra.isFractionRing

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
  -- ⊢ (∃ a s hs, x = IsLocalization.mk' K a { val := s, property := (_ : s ∈ A⁰) } …
  convert Iff.rfl
  -- ⊢ ↑(algebraMap A K) x✝² * (↑(algebraMap A K) x✝¹)⁻¹ = IsLocalization.mk' K x✝² …
  congr
  -- ⊢ (↑(algebraMap A K) x✝¹)⁻¹ = ↑(↑(IsUnit.liftRight (MonoidHom.restrict (Submon …
  rw [Units.val_inv_eq_inv_val]
  -- ⊢ (↑(algebraMap A K) x✝¹)⁻¹ = (↑(↑(IsUnit.liftRight (MonoidHom.restrict (Submo …
  rfl
  -- 🎉 no goals
#align localization.subalgebra.mem_range_map_to_fraction_ring_iff_of_field Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField

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
    -- ⊢ x✝ ∈ {x | ∃ a s x_1, x = ↑(algebraMap A K) a * (↑(algebraMap A K) s)⁻¹} ↔ x✝ …
    symm
    -- ⊢ x✝ ∈ ↑(AlgHom.range (mapToFractionRing K S (Localization S) hS)) ↔ x✝ ∈ {x | …
    apply mem_range_mapToFractionRing_iff_ofField
    -- 🎉 no goals
#align localization.subalgebra.of_field Localization.subalgebra.ofField

instance isLocalization_ofField : IsLocalization S (subalgebra.ofField K S hS) := by
  dsimp only [Localization.subalgebra.ofField]
  -- ⊢ IsLocalization S { x // x ∈ Subalgebra.copy (AlgHom.range (mapToFractionRing …
  rw [Subalgebra.copy_eq]
  -- ⊢ IsLocalization S { x // x ∈ AlgHom.range (mapToFractionRing K S (Localizatio …
  infer_instance
  -- 🎉 no goals
#align localization.subalgebra.is_localization_of_field Localization.subalgebra.isLocalization_ofField

instance isFractionRing_ofField : IsFractionRing (subalgebra.ofField K S hS) K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS
#align localization.subalgebra.is_fraction_ring_of_field Localization.subalgebra.isFractionRing_ofField

end subalgebra

end Field

end Localization
