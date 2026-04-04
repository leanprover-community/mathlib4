/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib

@[expose] public section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

variable (X) in
abbrev Modules.isQuasicoherent : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)

theorem isQuasicoherent_iff_isIso_fromSpecΓ :
    (tilde.functor R).essImage = isQuasicoherent (Spec R) := by
  ext
  rw [← isIso_fromTildeΓ_iff]
  exact isIso_fromTildeΓ_iff_isQuasiCoherent _

variable {J : Type u} [Category.{v} J] (F : J ⥤ (Spec R).Modules)

instance : (isQuasicoherent (Spec R)).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_iff_isIso_fromSpecΓ]
  exact instIsClosedUnderColimitsOfShapeEssImageOfHasColimitsOfShapeOfPreservesColimitsOfShapeOfFullOfFaithful (tilde.functor R)

set_option backward.isDefEq.respectTransparency false in
instance epi_of_epi {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Epi f] : Epi (moduleSpecΓFunctor.map f) := by
  apply (tilde.functor R).epi_of_epi_map
  haveI : IsIso (tilde.adjunction.counit.app N) := isQuasicoherent_IsIso_fromTildeΓ N
  rw [← epi_comp_iff_of_isIso _ (tilde.adjunction.counit.app N),
    tilde.adjunction.counit_naturality f]
  haveI : Epi (tilde.adjunction.counit.app M) := (isQuasicoherent_IsIso_fromTildeΓ M).epi_of_iso
  infer_instance

theorem surjective_of_epi {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Epi f] : Function.Surjective (f.val.app (Opposite.op ⊤)).hom :=
  ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f) |>.mp (epi_of_epi f)

abbrev QuasicoherentSheaves :=
  (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory

namespace QuasicoherentSheaves

variable (X) in
def toModules : X.QuasicoherentSheaves ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).ι

abbrev module (F : X.QuasicoherentSheaves) : X.Modules := (toModules X).obj F

instance : (toModules X).Full :=
  inferInstanceAs (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).ι.Full

instance : (toModules X).Faithful :=
  inferInstanceAs (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).ι.Faithful

section IsAffine

variable {R : CommRingCat.{u}}

#check Equivalence.fullyFaithfulToEssImage
#check AffineScheme.instIsEquivalenceOppositeCommRingCatOpRightOpΓ
#check tilde.adjunction

section

@[simps]
noncomputable def equivEssImageOfCoreflective {C : Type*} [Category* C]
    {D : Type*} [Category* D] {L : C ⥤ D} [Coreflective L] : C ≌ L.EssImageSubcategory where
  functor := L.toEssImage
  inverse := L.essImage.ι ⋙ coreflector L
  unitIso := sorry
  counitIso := sorry

end

noncomputable instance : Coreflective (tilde.functor R) where
  R := moduleSpecΓFunctor
  adj := tilde.adjunction

theorem isQuasicoherent_eq_essImage_tilde_functor :
    (tilde.functor R).essImage = (SheafOfModules.isQuasicoherent (R := (Spec R).ringCatSheaf)) := by
  ext
  rw [← isIso_fromTildeΓ_iff]
  exact isIso_fromTildeΓ_iff_isQuasiCoherent _

variable (R) in
noncomputable def tildeEquiv_aux : ModuleCat R ≌ (tilde.functor R).essImage.FullSubcategory :=
  equivEssImageOfCoreflective

noncomputable def tildeEquiv : ModuleCat R ≌ (Spec R).QuasicoherentSheaves :=
  (tildeEquiv_aux R).trans
    (ObjectProperty.fullSubcategoryCongr isQuasicoherent_eq_essImage_tilde_functor)

#check Adjunction.has_colimits_of_equivalence

instance hasColimitsOfSize : HasColimitsOfSize.{v, u} (Spec R).QuasicoherentSheaves :=
  Adjunction.has_colimits_of_equivalence tildeEquiv.inverse

instance hasLimitsOfSize : HasLimitsOfSize.{u, u} (Spec R).QuasicoherentSheaves :=
  Adjunction.has_limits_of_equivalence tildeEquiv.inverse

open Modules

example : tildeEquiv.inverse = (toModules (Spec R)) ⋙ moduleSpecΓFunctor := rfl

example : (tildeEquiv (R := R)).functor ⋙ (toModules (Spec R)) = tilde.functor R := rfl

end IsAffine

end AlgebraicGeometry.Scheme.QuasicoherentSheaves
