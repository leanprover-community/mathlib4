/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib

@[expose] public section

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

abbrev Modules.IsQuasicoherent (M : X.Modules) :=
  SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M

variable (X) in
abbrev Modules.isQuasicoherent : ObjectProperty X.Modules :=
  Modules.IsQuasicoherent

section

instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] :
    (M.restrict f).IsQuasicoherent := sorry

theorem isIso_fromTildeΓ_iff_isQuasiCoherent (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ M.IsQuasicoherent := sorry

instance isQuasicoherent_IsIso_fromTildeΓ (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso M.fromTildeΓ := (isIso_fromTildeΓ_iff_isQuasiCoherent M).mpr inferInstance

end

@[simp]
lemma isQuasicoherent_def {M : X.Modules} : isQuasicoherent X M ↔ M.IsQuasicoherent := by rfl

theorem isQuasicoherent_of_iso {M N : X.Modules} (φ : M ≅ N) [M.IsQuasicoherent] :
    N.IsQuasicoherent := SheafOfModules.IsQuasicoherent.of_iso M N φ

instance : (isQuasicoherent X).IsClosedUnderIsomorphisms :=
  ObjectProperty.IsClosedUnderIsomorphisms.mk
    (fun e _ => isQuasicoherent_of_iso e)

theorem isQuasicoherent_iff_isIso_fromSpecΓ :
    (tilde.functor R).essImage = isQuasicoherent (Spec R) := by
  ext
  rw [← isIso_fromTildeΓ_iff]
  exact isIso_fromTildeΓ_iff_isQuasiCoherent _

variable {J : Type w} [Category.{v} J] (F : J ⥤ (Spec R).Modules)
  [HasColimitsOfShape J AddCommGrpCat]

instance : (isQuasicoherent (Spec R)).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_iff_isIso_fromSpecΓ]
  exact instIsClosedUnderColimitsOfShapeEssImageOfHasColimitsOfShapeOfPreservesColimitsOfShapeOfFullOfFaithful (tilde.functor R)

instance [Finite J] : (isQuasicoherent (Spec R)).IsClosedUnderLimitsOfShape (Discrete J) := by
  rw [← isQuasicoherent_iff_isIso_fromSpecΓ]
  exact instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful (tilde.functor R)

set_option backward.isDefEq.respectTransparency false in
instance epi_of_epi {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Epi f] : Epi (moduleSpecΓFunctor.map f) := by
  apply (tilde.functor R).epi_of_epi_map
  haveI : IsIso (tilde.adjunction.counit.app N) := isQuasicoherent_IsIso_fromTildeΓ N
  rw [← epi_comp_iff_of_isIso _ (tilde.adjunction.counit.app N),
    tilde.adjunction.counit_naturality f]
  haveI : Epi (tilde.adjunction.counit.app M) := (isQuasicoherent_IsIso_fromTildeΓ M).epi_of_iso
  infer_instance

theorem isQuasicoherent_spec_surjective_of_epi {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (Opposite.op ⊤)).hom :=
  ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f) |>.mp (epi_of_epi f)

noncomputable section restrictEquivalence

variable {Y : Scheme.{u}} (φ : X ≅ Y)

namespace Modules

def restrictFunctor_inv_restrictFunctor_hom_id :
    restrictFunctor φ.inv ⋙ restrictFunctor φ.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp φ.hom φ.inv).symm ≪≫
  restrictFunctorCongr φ.hom_inv_id ≪≫
  restrictFunctorId

instance : (restrictFunctor φ.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' _
    (restrictFunctor_inv_restrictFunctor_hom_id φ.symm).symm
    (restrictFunctor_inv_restrictFunctor_hom_id φ)

theorem isQuasicoherent_restrictFunctor_iff {M : Y.Modules} :
    (M.restrict φ.hom).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  apply ObjectProperty.prop_of_iso _ ((restrictFunctor_inv_restrictFunctor_hom_id φ.symm).app M)
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.comp_obj]
  infer_instance

theorem isQuasicoherent_inverseImage_iso :
    (isQuasicoherent X).inverseImage (restrictFunctor φ.hom) = isQuasicoherent Y := by
  ext
  simp [isQuasicoherent_restrictFunctor_iff]

instance isQuasicoherent_pushforward_of_iso {φ : X ⟶ Y} [IsIso φ] {M : X.Modules}
    [M.IsQuasicoherent] :
    ((pushforward φ).obj M).IsQuasicoherent :=
  (isQuasicoherent_restrictFunctor_iff (asIso φ)).mp
    ((isQuasicoherent X).prop_of_iso ((restrictFunctorAdjCounitIso φ).app M).symm ‹_›)

end Modules

end restrictEquivalence

noncomputable section IsAffine

namespace Modules

theorem isQuasicoherent_surjective_of_epi {M N : X.Modules} [IsAffine X] (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (Opposite.op ⊤)).hom := by
  rw [← (isoSpec X).inv.opensRange_of_isIso, ← (isoSpec X).inv.image_top_eq_opensRange]
  change Function.Surjective (((restrictFunctor (isoSpec X).inv).map f).val.app (op ⊤))
  exact isQuasicoherent_spec_surjective_of_epi ((restrictFunctor (isoSpec X).inv).map f)

instance {R S : CommRingCat.{u}} (φ : R ⟶ S) {M : (Spec S).Modules} [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  rw [← isIso_fromTildeΓ_iff_isQuasiCoherent] at ⊢ hM
  exact pushforward_isIso_fromTildeΓ φ M

instance isQuasicoherent_of_pushforward {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  rw [show f = (X.isoSpec.hom ≫ Spec.map (Hom.appTop f)) ≫ Y.isoSpec.inv by
    simp [isoSpec_hom_naturality f]]
  let φ := (pushforward X.isoSpec.hom).isoWhiskerLeft
      (pushforwardComp (Spec.map (Hom.appTop f)) Y.isoSpec.inv) ≪≫
      pushforwardComp X.isoSpec.hom (Spec.map (Hom.appTop f) ≫ Y.isoSpec.inv)
  haveI : ((pushforward X.isoSpec.hom ⋙ pushforward (Spec.map (Hom.appTop f)) ⋙
      pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    infer_instance
  exact isQuasicoherent_of_iso (φ.app M)

variable {X : Scheme.{u}} [IsAffine X] {J : Type w} [Category.{v} J] (F : J ⥤ X.Modules)
  [HasColimitsOfShape J AddCommGrpCat]

instance : (isQuasicoherent X).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage ..

instance [Finite J] : (isQuasicoherent X).IsClosedUnderLimitsOfShape (Discrete J) := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage ..

end Modules

end IsAffine

end AlgebraicGeometry.Scheme
