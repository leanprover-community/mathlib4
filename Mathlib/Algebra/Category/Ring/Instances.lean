/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.LocalRing

#align_import algebra.category.Ring.instances from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_isIso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso
#align localization_unit_is_iso localization_unit_isIso

instance localization_unit_isIso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_isIso _
#align localization_unit_is_iso' localization_unit_isIso'

theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun {T} _ _ => @IsLocalization.ringHom_ext R _ M S _ _ T _ _ _ _⟩
#align is_localization.epi IsLocalization.epi

instance Localization.epi {R : Type*} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _
#align localization.epi Localization.epi

instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M : _) := by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _
#align localization.epi' Localization.epi'

instance CommRingCat.isLocalRingHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalRingHom g] [IsLocalRingHom f] : IsLocalRingHom (f ≫ g) :=
  _root_.isLocalRingHom_comp _ _
set_option linter.uppercaseLean3 false in
#align CommRing.is_local_ring_hom_comp CommRingCat.isLocalRingHom_comp

theorem isLocalRingHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalRingHom f.hom :=
  { map_nonunit := fun a ha => by
      convert f.inv.isUnit_map ha
      exact (RingHom.congr_fun f.hom_inv_id _).symm }
#align is_local_ring_hom_of_iso isLocalRingHom_of_iso

-- see Note [lower instance priority]
instance (priority := 100) isLocalRingHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalRingHom f :=
  isLocalRingHom_of_iso (asIso f)
#align is_local_ring_hom_of_is_iso isLocalRingHom_of_isIso
