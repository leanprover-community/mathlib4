/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_isIso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso

instance localization_unit_isIso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_isIso _

theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun {T} _ _ => @IsLocalization.ringHom_ext R _ M S _ _ T _ _ _ _⟩

instance Localization.epi {R : Type*} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _

instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M : _) := by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _

/-
TODO: This abbrev is added in #17403, together with the following instance
`CommRingCat.isLocalHom_ofIsLocalRingHom`.
This is a local revert to the state before #6045 in the algebraic geomertry part of Mathlib.

Although this instance itself can be find only using
`inferInstance`, the instance `IsLocalHom (f ≫ g)` cannnot be inferred from `IsLocalRingHom (f ≫ g)`
without this instance.
-/
abbrev IsLocalRingHom {R S} [Semiring R] [Semiring S] (f : R →+* S) := IsLocalHom (F := R →+* S) f

instance CommRingCat.isLocalHom_ofIsLocalRingHom {R S : CommRingCat} (f : R ⟶ S)
    [IsLocalRingHom f] : IsLocalHom f :=
  inferInstance

@[instance]
theorem CommRingCat.isLocalRingHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalRingHom g] [IsLocalRingHom f] : IsLocalRingHom (f ≫ g) :=
  RingHom.isLocalHom_comp _ _

theorem isLocalRingHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalRingHom f.hom :=
  { map_nonunit := fun a ha => by
      convert f.inv.isUnit_map ha
      exact (RingHom.congr_fun f.hom_inv_id _).symm }

-- see Note [lower instance priority]
@[instance 100]
theorem isLocalRingHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalRingHom f :=
  isLocalRingHom_of_iso (asIso f)
