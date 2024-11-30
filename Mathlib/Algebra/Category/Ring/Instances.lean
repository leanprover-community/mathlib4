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

universe u

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
These three instances solve the issue where the `FunLike` instances provided by
`CommRingCat.instFunLike'`, `CommRingCat.instFunLike''`, and `CommRingCat.instFunLike'''`
are not syntactically equal to `CommRingCat.instFunLike` when applied to
objects of the form `CommRingCat.of R`.
To prevent infinite loops, the priority of these three instances must be set lower
than that of other instances.
-/
instance (priority := 50) {R : Type*} [CommRing R] {S : CommRingCat} (f : CommRingCat.of R ⟶ S)
    [IsLocalHom (R := CommRingCat.of R) f] : IsLocalHom f :=
  inferInstance

instance (priority := 50) {R : CommRingCat} {S : Type*} [CommRing S] (f : R ⟶ CommRingCat.of S)
    [IsLocalHom (S := CommRingCat.of S) f] : IsLocalHom f :=
  inferInstance

instance (priority := 50) {R S : Type u} [CommRing R] [CommRing S]
    (f : CommRingCat.of R ⟶ CommRingCat.of S)
    [IsLocalHom (R := CommRingCat.of R) (S := CommRingCat.of S) f] : IsLocalHom f :=
  inferInstance

-- This instance handles the coercion of a morphism into a real `RingHom`.
instance {R S : CommRingCat} (f : R ⟶ S) [IsLocalHom f] :
    IsLocalHom (F := R →+* S) f :=
  inferInstance

@[instance]
theorem CommRingCat.isLocalHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalHom g] [IsLocalHom f] : IsLocalHom (f ≫ g) :=
  RingHom.isLocalHom_comp _ _

@[deprecated (since := "2024-10-10")]
alias CommRingCat.isLocalRingHom_comp := CommRingCat.isLocalHom_comp

theorem isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom :=
  { map_nonunit := fun a ha => by
      convert f.inv.isUnit_map ha
      exact (RingHom.congr_fun f.hom_inv_id _).symm }

@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_of_iso := isLocalHom_of_iso

-- see Note [lower instance priority]
@[instance 100]
theorem isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalHom f :=
  isLocalHom_of_iso (asIso f)

@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_of_isIso := isLocalHom_of_isIso
