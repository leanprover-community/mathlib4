/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib

/-!

# QC

-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} (M : X.Modules)

namespace AlgebraicGeometry.Scheme.Modules

instance (priority := 100) [M.IsFree] : M.IsLocallyFree := SheafOfModules.IsFree.isLocallyFree M

lemma isQuasicoherent_restrict_iff {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsQuasicoherent ↔ (M.over f.opensRange).IsQuasicoherent := sorry

variable (𝓤 : OpenCover.{u} X)

lemma _root_.AlgebraicGeometry.Scheme.OpenCover.coversTop : (Opens.grothendieckTopology X).CoversTop
    (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) := by
  intro W x hx
  have hx' : x ∈ (⊤ : X.Opens) := trivial
  rw [← 𝓤.iSup_opensRange, TopologicalSpace.Opens.mem_iSup] at hx'
  obtain ⟨i, hi⟩ := hx'
  refine ⟨(𝓤.f i).opensRange ⊓ W, homOfLE inf_le_right, ?_, ⟨hi, hx⟩⟩
  rw [Sieve.mem_ofObjects_iff]
  exact ⟨i, ⟨homOfLE inf_le_left⟩⟩

theorem isQuasiCoherent_of_open_cover
    (h : ∀ i, (M.restrict (𝓤.f i)).IsQuasicoherent) : M.IsQuasicoherent :=
  have _ i : (M.over (𝓤.f i).opensRange).IsQuasicoherent := by
    rw [← isQuasicoherent_restrict_iff]
    exact h i
  SheafOfModules.IsQuasicoherent.of_coversTop M (fun i : 𝓤.I₀ => (𝓤.f i).opensRange) 𝓤.coversTop

def LocallyFreeLocusSet : Set X := {x | ∃ (U : Scheme.{u}) (f : U ⟶ X)
    (_ : IsOpenImmersion f), x ∈ f.opensRange ∧ (M.restrict f).IsLocallyFree}

lemma locallyFreeLocusSet_isOpen : IsOpen (LocallyFreeLocusSet M) := by
  rw [LocallyFreeLocusSet, isOpen_iff_forall_mem_open]
  intro x ⟨U, f, hf, hxU, hfree⟩
  exact ⟨f.opensRange, fun y hy => ⟨U, f, hf, hy, hfree⟩, f.opensRange.2, hxU⟩

@[simps]
def LocallyFreeLocus : X.Opens := ⟨LocallyFreeLocusSet M, locallyFreeLocusSet_isOpen M⟩

lemma locallyFreeLocus_restrict {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    f ⁻¹ᵁ (LocallyFreeLocus M) = LocallyFreeLocus (M.restrict f) := sorry

lemma locallyFreeLocus_eq_top_iff_isLocallyFree :
    LocallyFreeLocus M = ⊤ ↔ M.IsLocallyFree := sorry

lemma isLocallyFree_restrict_iff {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsLocallyFree ↔ f.opensRange ≤ LocallyFreeLocus M := by
  rw [← locallyFreeLocus_eq_top_iff_isLocallyFree, ← locallyFreeLocus_restrict]
  sorry

section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

-- REMOVE
-- REMOVE
set_option backward.isDefEq.respectTransparency false

lemma free_iff_isFree : Module.Free R M ↔ (tilde M).IsFree := by
  constructor
  · intro
    rw [SheafOfModules.IsFree.iso_free.{u}]
    exact ⟨_, ⟨(tilde.functor R).mapIso (Module.Free.chooseBasis R M).repr.toModuleIso ≪≫
      tildeFinsupp _⟩⟩
  intro h
  rw [SheafOfModules.IsFree.iso_free.{u}] at h
  obtain ⟨I, ⟨φ⟩⟩ := h
  let ψ := φ ≪≫ (tildeFinsupp (R := R) I).symm
  exact Module.Free.of_equiv (((tilde.functor R).preimageIso ψ).toLinearEquiv.symm)

instance [Module.Free R M] : (tilde M).IsFree := (free_iff_isFree M).mp inferInstance
variable (r : R)

set_option maxHeartbeats 800000 in
def NatIsoTildeFunctorRestrictFunctor : (tilde.functor R) ⋙
    (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) ≅
    ModuleCat.localizedModuleFunctor (.powers r) ⋙
    (tilde.functor (CommRingCat.of (Localization (.powers r)))) := by
  let S : CommRingCat.{u} := CommRingCat.of (Localization (.powers r))
  let f : Spec S ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let L : ModuleCat.{u} R ⥤ (Spec S).Modules := (tilde.functor R) ⋙ restrictFunctor f
  let Γ : (Spec S).Modules ⥤ ModuleCat.{u} S := moduleSpecΓFunctor (R := S)
  let T : ModuleCat.{u} S ⥤ (Spec S).Modules := tilde.functor S
  let loc : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.localizedModuleFunctor (.powers r)
  let β : L ⋙ Γ ≅ loc := by
    change ((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)) ≅
      ModuleCat.localizedModuleFunctor (.powers r)
    let app : (M : ModuleCat.{u} R) →
        (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj M) ≅
          (ModuleCat.localizedModuleFunctor (.powers r)).obj M := fun M => by
      let LM : (Spec S).Modules := (restrictFunctor f).obj (tilde M)
      have hf_top : f ''ᵁ (⊤ : (Spec S).Opens) = PrimeSpectrum.basicOpen r := by
        rw [Scheme.Hom.image_top_eq_opensRange]
        exact TopologicalSpace.Opens.ext
          (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)
      letI : Module R ((modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤)) :=
        Module.compHom _ (algebraMap R S)
      letI : IsScalarTower R S ((modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤)) :=
        .of_algebraMap_smul fun _ _ => rfl
      let e : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[R]
          (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
            (.op (f ''ᵁ (⊤ : (Spec S).Opens))) :=
        { __ := ((tilde M).restrictAppIso f (⊤ : (Spec S).Opens)).addCommGroupIsoToAddEquiv
          map_smul' := by
            intro a x
            exact AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec (M := tilde M)
              (f := CommRingCat.ofHom (algebraMap (↑R) (Localization.Away r))) (U := ⊤) a x }
      let toΓ : M →ₗ[R] (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) :=
        e.symm.toLinearMap.comp (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom
      have hloc_toOpen : IsLocalizedModule (.powers r)
          (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom := by
        rw [hf_top]
        infer_instance
      haveI : IsLocalizedModule (.powers r) toΓ := by
        dsimp [toΓ]
        exact IsLocalizedModule.of_linearEquiv (.powers r)
          (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom e.symm
      let eΓR : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[R]
          M.localizedModule (.powers r) :=
        IsLocalizedModule.linearEquiv (.powers r) toΓ (M.localizedModuleMkLinearMap (.powers r))
      let eΓ : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[S]
          M.localizedModule (.powers r) :=
        eΓR.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
      exact LinearEquiv.toModuleIso eΓ
    refine NatIso.ofComponents app ?_
    intro M N g
    apply ModuleCat.hom_ext
    let LM : (Spec S).Modules := (restrictFunctor f).obj (tilde M)
    let LN : (Spec S).Modules := (restrictFunctor f).obj (tilde N)
    letI : Module R ((modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤)) :=
      Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S ((modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤)) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI : Module R ((modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤)) :=
      Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S ((modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤)) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI : Module R (((tilde.functor R) ⋙ restrictFunctor f ⋙
        moduleSpecΓFunctor (R := S)).obj M) :=
      Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S (((tilde.functor R) ⋙ restrictFunctor f ⋙
        moduleSpecΓFunctor (R := S)).obj M) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI : Module R (((tilde.functor R) ⋙ restrictFunctor f ⋙
        moduleSpecΓFunctor (R := S)).obj N) :=
      Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S (((tilde.functor R) ⋙ restrictFunctor f ⋙
        moduleSpecΓFunctor (R := S)).obj N) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI : Module R (((ModuleCat.localizedModuleFunctor (.powers r)).obj N) : Type u) :=
      inferInstanceAs (Module R (N.localizedModule (.powers r)))
    letI : IsScalarTower R S (((ModuleCat.localizedModuleFunctor (.powers r)).obj N) : Type u) :=
      inferInstanceAs (IsScalarTower R S (N.localizedModule (.powers r)))
    letI : LinearMap.CompatibleSMul
        (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj M)
        (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj N)
        R S := by
      constructor
      intro f' c x
      rw [← IsScalarTower.algebraMap_smul S c x,
        ← IsScalarTower.algebraMap_smul S c (f' x)]
      exact f'.map_smul (algebraMap R S c) x
    letI : LinearMap.CompatibleSMul
        (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj M)
        (((ModuleCat.localizedModuleFunctor (.powers r)).obj N) : Type u) R S := by
      constructor
      intro f' c x
      rw [← IsScalarTower.algebraMap_smul S c x,
        ← IsScalarTower.algebraMap_smul S c (f' x)]
      exact f'.map_smul (algebraMap R S c) x
    let eM : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[R]
        (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
          (.op (f ''ᵁ (⊤ : (Spec S).Opens))) :=
      { __ := ((tilde M).restrictAppIso f (⊤ : (Spec S).Opens)).addCommGroupIsoToAddEquiv
        map_smul' := by
          intro a x
          exact AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec (M := tilde M)
            (f := CommRingCat.ofHom (algebraMap (↑R) (Localization.Away r))) (U := ⊤) a x }
    let eN : (modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤) ≃ₗ[R]
        (modulesSpecToSheaf.obj (tilde N)).presheaf.obj
          (.op (f ''ᵁ (⊤ : (Spec S).Opens))) :=
      { __ := ((tilde N).restrictAppIso f (⊤ : (Spec S).Opens)).addCommGroupIsoToAddEquiv
        map_smul' := by
          intro a x
          exact AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec (M := tilde N)
            (f := CommRingCat.ofHom (algebraMap (↑R) (Localization.Away r))) (U := ⊤) a x }
    let toΓM : M →ₗ[R] (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) :=
      eM.symm.toLinearMap.comp (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom
    let toΓN : N →ₗ[R] (modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤) :=
      eN.symm.toLinearMap.comp (tilde.toOpen N (f ''ᵁ (⊤ : (Spec S).Opens))).hom
    have hf_top : f ''ᵁ (⊤ : (Spec S).Opens) = PrimeSpectrum.basicOpen r := by
      rw [Scheme.Hom.image_top_eq_opensRange]
      exact TopologicalSpace.Opens.ext
        (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)
    have hlocM_toOpen : IsLocalizedModule (.powers r)
        (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom := by
      rw [hf_top]
      infer_instance
    have hlocN_toOpen : IsLocalizedModule (.powers r)
        (tilde.toOpen N (f ''ᵁ (⊤ : (Spec S).Opens))).hom := by
      rw [hf_top]
      infer_instance
    haveI : IsLocalizedModule (.powers r) toΓM := by
      dsimp [toΓM]
      exact IsLocalizedModule.of_linearEquiv (.powers r)
        (tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom eM.symm
    haveI : IsLocalizedModule (.powers r) toΓN := by
      dsimp [toΓN]
      exact IsLocalizedModule.of_linearEquiv (.powers r)
        (tilde.toOpen N (f ''ᵁ (⊤ : (Spec S).Opens))).hom eN.symm
    let eΓRM : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[R]
        M.localizedModule (.powers r) :=
      IsLocalizedModule.linearEquiv (.powers r) toΓM (M.localizedModuleMkLinearMap (.powers r))
    let eΓRN : (modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤) ≃ₗ[R]
        N.localizedModule (.powers r) :=
      IsLocalizedModule.linearEquiv (.powers r) toΓN (N.localizedModuleMkLinearMap (.powers r))
    let eΓM : (modulesSpecToSheaf.obj LM).presheaf.obj (.op ⊤) ≃ₗ[S]
        M.localizedModule (.powers r) :=
      eΓRM.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
    let eΓN : (modulesSpecToSheaf.obj LN).presheaf.obj (.op ⊤) ≃ₗ[S]
        N.localizedModule (.powers r) :=
      eΓRN.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
    have hmap (m : M) :
        ((moduleSpecΓFunctor (R := S)).map ((restrictFunctor f).map (tilde.map g))).hom
          (toΓM m) = toΓN (g m) := by
      dsimp [toΓM, toΓN]
      apply eN.injective
      change ((modulesSpecToSheaf.map (tilde.map g)).hom.app
          (.op (f ''ᵁ (⊤ : (Spec S).Opens)))).hom
          ((tilde.toOpen M (f ''ᵁ (⊤ : (Spec S).Opens))).hom m) =
        (tilde.toOpen N (f ''ᵁ (⊤ : (Spec S).Opens))).hom (g.hom m)
      have h := congrArg ModuleCat.Hom.hom
        (tilde.toOpen_map_app (M := M) (N := N) g (f ''ᵁ (⊤ : (Spec S).Opens)))
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
      exact LinearMap.congr_fun h m
    let j : (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj M) →ₗ[R]
        ((ModuleCat.localizedModuleFunctor (.powers r)).obj N) :=
      (ModuleCat.Hom.hom ((((tilde.functor R) ⋙ restrictFunctor f ⋙
        moduleSpecΓFunctor (R := S)).map g) ≫ (app N).hom)).restrictScalars R
    let k : (((tilde.functor R) ⋙ restrictFunctor f ⋙ moduleSpecΓFunctor (R := S)).obj M) →ₗ[R]
        ((ModuleCat.localizedModuleFunctor (.powers r)).obj N) :=
      (ModuleCat.Hom.hom
        ((app M).hom ≫ (ModuleCat.localizedModuleFunctor (.powers r)).map g)).restrictScalars R
    have hjk : j = k := by
      apply IsLocalizedModule.ext (.powers r) toΓM
      · intro x
        exact IsLocalizedModule.map_units (N.localizedModuleMkLinearMap (.powers r)) x
      · ext m
        dsimp [j, k]
        change (app N).hom.hom (((moduleSpecΓFunctor (R := S)).map
          ((restrictFunctor f).map (tilde.map g))).hom (toΓM m)) =
          ((ModuleCat.localizedModuleFunctor (.powers r)).map g).hom
            ((app M).hom.hom (toΓM m))
        rw [hmap m]
        change eΓN (toΓN (g.hom m)) =
          ((ModuleCat.localizedModuleFunctor (.powers r)).map g).hom (eΓM (toΓM m))
        change eΓRN (toΓN (g.hom m)) =
          ((ModuleCat.localizedModuleFunctor (.powers r)).map g).hom (eΓRM (toΓM m))
        rw [IsLocalizedModule.linearEquiv_apply]
        rw [IsLocalizedModule.linearEquiv_apply]
        dsimp [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
        change N.localizedModuleMkLinearMap (.powers r) (g.hom m) =
          (IsLocalizedModule.map (.powers r) (M.localizedModuleMkLinearMap (.powers r))
            (N.localizedModuleMkLinearMap (.powers r)) g.hom)
            (M.localizedModuleMkLinearMap (.powers r) m)
        rw [IsLocalizedModule.map_apply]
    ext x
    exact LinearMap.congr_fun hjk x
  let εHom : L ⋙ (Γ ⋙ T) ⟶ L := Functor.whiskerLeft L (fromTildeΓNatTrans (R := S))
  have hε : IsIso εHom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso (Scheme.Modules.fromTildeΓ (R := S) (L.obj M))
    apply isIso_fromTildeΓ_of_presentation
    let F : SheafOfModules (Spec R).ringCatSheaf ⥤
        SheafOfModules (Spec S).ringCatSheaf := restrictFunctor f
    let α : (Spec S).ringCatSheaf ⟶
        ((Scheme.Hom.opensFunctor f).sheafPushforwardContinuous _ _ _).obj
          (Spec R).ringCatSheaf :=
      ⟨Functor.whiskerRight
        ({ app := fun U => (f.appIso U.unop).inv
           naturality := by
            intro U V i
            exact f.appIso_inv_naturality i } :
          (Spec S).presheaf ⟶ (Scheme.Hom.opensFunctor f).op ⋙ (Spec R).presheaf)
        (forget₂ CommRingCat RingCat)⟩
    have hα : IsIso (SheafOfModules.unitToPushforwardObjUnit α) := by
      change IsIso (C := (Spec S).Modules) (SheafOfModules.unitToPushforwardObjUnit α)
      rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
      intro U
      change IsIso ((forget₂ RingCat AddCommGrpCat).map
        ((forget₂ CommRingCat RingCat).map (f.appIso U).inv))
      infer_instance
    let η : SheafOfModules.unit (Spec S).ringCatSheaf ≅
        F.obj (SheafOfModules.unit (Spec R).ringCatSheaf) :=
      @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit α) hα
    let P : (tilde M).Presentation :=
      presentationTilde.{u} (R := R) M .univ (by simp) _ (Submodule.span_eq _)
    have hF : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u+1, u+1} F := by
      change CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u+1, u+1}
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f)
      exact (Adjunction.ofIsLeftAdjoint
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f)).leftAdjoint_preservesColimits
    letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u+1, u+1} F := hF
    exact P.map F η
  let ε : L ⋙ (Γ ⋙ T) ≅ L := @asIso _ _ _ _ εHom hε
  exact ε.symm ≪≫ (Functor.associator L Γ T).symm ≪≫ Functor.isoWhiskerRight β T

abbrev fromLocalizationAway : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))

@[simp]
theorem fromLocalizationAway_opensRange :
    (fromLocalizationAway r).opensRange = PrimeSpectrum.basicOpen r :=
  TopologicalSpace.Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)

lemma freeLocus_le_locallyFreeLocusSet [Module.FinitePresentation R M] :
    Module.freeLocus R M ≤ LocallyFreeLocusSet (tilde M) := by
  intro p h
  rw [Module.mem_freeLocus] at h
  obtain ⟨r, ⟨hr₁, ⟨hr₂, _⟩⟩⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (p.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap (p.asIdeal.primeCompl) M) (Localization.AtPrime p.asIdeal)
  let Rᵣ : CommRingCat.{u} := CommRingCat.of (Localization.Away r)
  let Mᵣ : ModuleCat.{u} Rᵣ := ModuleCat.of Rᵣ (M.localizedModule (.powers r))
  use Spec Rᵣ, fromLocalizationAway r, inferInstance
  refine ⟨by rw [fromLocalizationAway_opensRange, PrimeSpectrum.mem_basicOpen]; exact hr₁, ?_⟩
  let φ : (tilde M).restrict _ ≅ tilde Mᵣ := (NatIsoTildeFunctorRestrictFunctor r).app M
  let ψ : Mᵣ ≃ₗ[Rᵣ] (LocalizedModule (.powers r) M) :=
    Shrink.linearEquiv (Localization.Away r) (LocalizedModule (.powers r) M)
  have := Module.Free.of_equiv ψ.symm
  refine ObjectProperty.prop_of_iso SheafOfModules.IsLocallyFree.{u} φ.symm ?_
  infer_instance

lemma locallyFreeLocusSet_le_freeLocus : LocallyFreeLocusSet (tilde M) ≤ Module.freeLocus R M := by
  intro p h
  sorry

theorem locallyFreeLocusSet_eq_freeLocus [Module.FinitePresentation R M] :
    LocallyFreeLocusSet (tilde M) = Module.freeLocus R M :=
  le_antisymm (locallyFreeLocusSet_le_freeLocus M) (freeLocus_le_locallyFreeLocusSet M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [Module.Flat R M] [Module.FinitePresentation R M] : (tilde M).IsLocallyFree := by
  rw [← locallyFreeLocus_eq_top_iff_isLocallyFree]
  ext1
  dsimp
  rw [locallyFreeLocusSet_eq_freeLocus, Module.freeLocus_eq_univ]

end

end AlgebraicGeometry.Scheme.Modules
