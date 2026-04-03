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

variable {X : Scheme.{u}}

section

variable {Y : Scheme.{u}} (φ : X ≅ Y)

#check SheafOfModules.unit

noncomputable def modulesEquiv : X.Modules ≌ Y.Modules :=
  haveI : (Opens.mapMapIso (forgetToTop.mapIso φ)).functor.IsContinuous (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) := inferInstanceAs ((Opens.map φ.hom.base).IsContinuous _ _)
  haveI : (Opens.mapMapIso (forgetToTop.mapIso φ)).inverse.IsContinuous (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) := inferInstanceAs ((Opens.map φ.inv.base).IsContinuous _ _)
  SheafOfModules.pushforwardPushforwardEquivalence (Opens.mapMapIso (forgetToTop.mapIso φ))
    φ.hom.toRingCatSheafHom φ.inv.toRingCatSheafHom sorry sorry

@[simp]
lemma modulesEquiv_functor : (modulesEquiv φ).functor = pushforward φ.hom := rfl

@[simp]
lemma modulesEquiv_inverse : (modulesEquiv φ).inverse = pushforward φ.inv := rfl

lemma modulesEquiv_inv : (modulesEquiv φ).symm = modulesEquiv φ.symm := rfl

end

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
