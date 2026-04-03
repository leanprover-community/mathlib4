/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

abbrev QuasicoherentSheaves :=
  (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory

namespace QuasicoherentSheaves

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

open Modules

variable {Y : Scheme.{u}} (φ : X ≅ Y)

#check SheafOfModules.pushforwardPushforwardEquivalence

set_option backward.isDefEq.respectTransparency false in
noncomputable def Modules.equivOfIso : X.Modules ≌ Y.Modules where
  functor := Modules.pushforward φ.hom
  inverse := Modules.pushforward φ.inv
  unitIso := (pushforwardId X).symm ≪≫ pushforwardCongr φ.hom_inv_id.symm ≪≫
    (pushforwardComp φ.hom φ.inv).symm
  counitIso := pushforwardComp φ.inv φ.hom ≪≫ pushforwardCongr φ.inv_hom_id ≪≫ pushforwardId Y
  functor_unitIso_comp :=
    sorry

example : tildeEquiv.inverse = (toModules (Spec R)) ⋙ moduleSpecΓFunctor := rfl

example : (tildeEquiv (R := R)).functor ⋙ (toModules (Spec R)) = tilde.functor R := rfl

end IsAffine

end AlgebraicGeometry.Scheme.QuasicoherentSheaves
