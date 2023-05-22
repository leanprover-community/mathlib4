/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebra.category.Ring.instances
! leanprover-community/mathlib commit a7c017d750512a352b623b1824d75da5998457d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.RingTheory.Localization.Away.Basic
import Mathbin.RingTheory.Ideal.LocalRing

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_isIso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  IsIso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso
#align localization_unit_is_iso localization_unit_isIso

instance localization_unit_is_iso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  by
  cases R
  exact localization_unit_isIso _
#align localization_unit_is_iso' localization_unit_is_iso'

theorem IsLocalization.epi {R : Type _} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun T f₁ f₂ => @IsLocalization.ringHom_ext R _ M S _ _ T _ _ _ _⟩
#align is_localization.epi IsLocalization.epi

instance Localization.epi {R : Type _} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _
#align localization.epi Localization.epi

instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M : _) :=
  by
  cases R
  exact IsLocalization.epi M _
#align localization.epi' Localization.epi'

instance CommRingCat.isLocalRingHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalRingHom g] [IsLocalRingHom f] : IsLocalRingHom (f ≫ g) :=
  isLocalRingHom_comp _ _
#align CommRing.is_local_ring_hom_comp CommRingCat.isLocalRingHom_comp

theorem isLocalRingHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalRingHom f.Hom :=
  {
    map_nonunit := fun a ha => by
      convert f.inv.is_unit_map ha
      rw [CategoryTheory.Iso.hom_inv_id_apply] }
#align is_local_ring_hom_of_iso isLocalRingHom_of_iso

-- see Note [lower instance priority]
instance (priority := 100) isLocalRingHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalRingHom f :=
  isLocalRingHom_of_iso (asIso f)
#align is_local_ring_hom_of_is_iso isLocalRingHom_of_isIso

