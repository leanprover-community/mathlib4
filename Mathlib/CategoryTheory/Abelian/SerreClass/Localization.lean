/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Localization with respect to a Serre class

The main definition in this file is `ObjectProperty.SerreClassLocalization.abelian`
which shows that if `L : C ⥤ D` is a localization functor with respect to
the class of morphisms `P.isoModSerre` for a Serre class `P : ObjectProperty C`
in the abelian category `C`, then `D` is an abelian category.

We also show that a functor `G : D ⥤ E` to an abelian category is exact iff
the composition `L ⋙ G` is.

-/

@[expose] public section

universe v'' v' v u'' u' u

namespace CategoryTheory

open Limits ZeroObject

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]
  {E : Type u''} [Category.{v''} E] [Abelian E]

lemma exists_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · exact ⟨_, kernel.ι f, P.prop_of_iso (Abelian.coimageIsoImage f).symm hf, by simp⟩

lemma exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_epiModSerre_comp_eq_zero_iff P]
    exact ⟨Y', s, hs.2, eq⟩
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    simpa only [isoModSerre_iff_of_mono] using
      P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

lemma exists_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, hf, by simp⟩

lemma exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_comp_monoModSerre_eq_zero_iff P]
    exact ⟨Y', s, hs.1, eq⟩
  · refine ⟨_, cokernel.π f, by rwa [isoModSerre_iff_of_epi], by simp⟩

variable {P} in
lemma monoModSerre.isoModSerre_factorThruImage
    {X Y : C} {f : X ⟶ Y} (hf : P.monoModSerre f) :
    P.isoModSerre (Abelian.factorThruImage f) := by
  rw [isoModSerre_iff_of_epi]
  exact P.prop_of_iso
    (asIso (kernel.map _ f (𝟙 _) (Abelian.image.ι f) (by simp))).symm hf

variable {P} in
lemma epiModSerre.isoModSerre_image_ι
    {X Y : C} {f : X ⟶ Y} (hf : P.epiModSerre f) :
    P.isoModSerre (Abelian.image.ι f) := by
  rw [isoModSerre_iff_of_mono]
  dsimp [epiModSerre] at hf ⊢
  exact P.prop_of_iso
    (asIso (cokernel.map f _ (Abelian.factorThruImage f) (𝟙 Y) (by simp))) hf

namespace SerreClassLocalization

instance : P.isoModSerre.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ :=
    ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)

instance : P.isoModSerre.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ :=
    ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)

noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance

variable [L.IsLocalization P.isoModSerre] [Preadditive D] [L.Additive]

include L P

lemma isZero_obj_iff (X : C) :
    IsZero (L.obj X) ↔ P X := by
  simp only [IsZero.iff_id_eq_zero, ← L.map_id, ← L.map_zero,
    MorphismProperty.map_eq_iff_precomp L P.isoModSerre,
    Category.comp_id, comp_zero, exists_prop, exists_eq_right]
  refine ⟨?_, fun _ ↦ ⟨X, by simpa⟩⟩
  rintro ⟨Y, h⟩
  simpa using h.2

lemma hasZeroObject : HasZeroObject D :=
  ⟨L.obj 0, by simpa [isZero_obj_iff L P] using P.prop_zero⟩

lemma map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    L.map f = 0 ↔ P (Abelian.image f) := by
  rw [← L.map_zero, MorphismProperty.map_eq_iff_precomp L P.isoModSerre]
  simp [← exists_isoModSerre_comp_eq_zero_iff P]

lemma map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
    [Epi f] [Mono g] :
    L.map f ≫ L.map g = 0 ↔ P Z := by
  rw [← L.map_comp, map_eq_zero_iff L P]
  have := strongEpi_of_epi f
  exact P.prop_iff_of_iso (Abelian.imageIsoImage _ ≪≫ (image.isoStrongEpiMono f g rfl).symm)

lemma mono_map_iff {X Y : C} (f : X ⟶ Y) :
    Mono (L.map f) ↔ P.monoModSerre f := by
  have := Localization.essSurj L P.isoModSerre
  refine ⟨fun _ ↦ ?_, fun hf ↦ ?_⟩
  · have hf : L.map (kernel.ι f) = 0 := by
      rw [← cancel_mono (L.map f), zero_comp, ← L.map_comp,
        kernel.condition, L.map_zero]
    simpa [hf] using map_comp_eq_zero_iff_of_epi_mono L P (𝟙 _) (kernel.ι f)
  · suffices ∀ ⦃Z : C⦄ (z : Z ⟶ X) (hz : L.map z ≫ L.map f = 0), L.map z = 0 by
      rw [Preadditive.mono_iff_cancel_zero]
      intro W z hz
      obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
        ((L.objObjPreimageIso W).hom ≫ z)
      have hs := Localization.inverts L P.isoModSerre φ.s φ.hs
      rw [← cancel_epi (L.objObjPreimageIso W).hom, comp_zero, hφ,
        ← cancel_epi (L.map φ.s), comp_zero,
        MorphismProperty.RightFraction.map_s_comp_map]
      apply this φ.f
      have : L.map φ.s ≫ (L.objObjPreimageIso W).hom ≫ z = L.map φ.f := by cat_disch
      rw [← this, Category.assoc, Category.assoc, hz, comp_zero, comp_zero]
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P, ← exists_comp_monoModSerre_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    exact ⟨W, f ≫ s, MorphismProperty.comp_mem _ _ _ hf hs, by simpa using eq⟩

lemma epi_map_iff {X Y : C} (f : X ⟶ Y) :
    Epi (L.map f) ↔ P.epiModSerre f := by
  have := Localization.essSurj L P.isoModSerre
  refine ⟨fun _ ↦ ?_, fun hf ↦ ?_⟩
  · have hf : L.map (cokernel.π f) = 0 := by
      rw [← cancel_epi (L.map f), comp_zero, ← L.map_comp,
        cokernel.condition, L.map_zero]
    simpa [hf] using map_comp_eq_zero_iff_of_epi_mono L P (cokernel.π f) (𝟙 _)
  · suffices ∀ ⦃Z : C⦄ (z : Y ⟶ Z) (hz : L.map f ≫ L.map z = 0), L.map z = 0 by
      rw [Preadditive.epi_iff_cancel_zero]
      intro W z hz
      obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
        (z ≫ (L.objObjPreimageIso W).inv)
      have hs := Localization.inverts L P.isoModSerre φ.s φ.hs
      rw [← cancel_mono (L.objObjPreimageIso W).inv, zero_comp, hφ,
        ← cancel_mono (L.map φ.s), zero_comp,
        MorphismProperty.LeftFraction.map_comp_map_s]
      apply this φ.f
      have : L.map φ.f = z ≫ (L.objObjPreimageIso W).inv ≫ L.map φ.s := by
        simp [reassoc_of% hφ]
      rw [this, reassoc_of% hz, zero_comp]
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P, ← exists_epiModSerre_comp_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    refine ⟨_, s ≫ f, MorphismProperty.comp_mem _ _ _ hs hf, by simpa⟩

lemma inverseImage_monomorphisms :
    (MorphismProperty.monomorphisms _).inverseImage L = P.monoModSerre := by
  ext
  simp [mono_map_iff L P]

lemma inverseImage_epimorphisms :
    (MorphismProperty.epimorphisms _).inverseImage L = P.epiModSerre := by
  ext
  simp [epi_map_iff L P]

lemma preservesMonomorphisms : L.PreservesMonomorphisms where
  preserves f _ := by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f

lemma preservesEpimorphisms : L.PreservesEpimorphisms where
  preserves f _ := by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

lemma mono_iff {X Y : D} (f : X ⟶ Y) :
    Mono f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ ↦ ?_, ?_⟩
  · suffices ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Mono (L.map f)),
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.monomorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [mono_map_iff L P] at hf
    refine ⟨_, _, Abelian.image.ι f, inferInstance, ⟨Iso.symm ?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_factorThruImage
    exact Arrow.isoMk (asIso (L.map (Abelian.factorThruImage f))) (Iso.refl _)
      (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Mono (L.map f')))

lemma epi_iff {X Y : D} (f : X ⟶ Y) :
    Epi f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ ↦ ?_, ?_⟩
  · suffices ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Epi (L.map f)),
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.epimorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [epi_map_iff L P] at hf
    refine ⟨_, _, Abelian.factorThruImage f, inferInstance, ⟨?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_image_ι
    refine Arrow.isoMk (Iso.refl _) (asIso (L.map (Abelian.image.ι f))) (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Epi (L.map f')))

lemma preservesKernel {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) L := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices ∀ (W : D) (z : W ⟶ L.obj X) (hz : z ≫ L.map f = 0),
      ∃ (l : W ⟶ L.obj (kernel f)), l ≫ L.map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ L).2
        (Fork.IsLimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : ∃ (Z : C) (hZ : W = L.obj Z) (z : Z ⟶ X), w = eqToHom hZ ≫ L.map z
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ w)
    have _ := Localization.inverts L P.isoModSerre φ.s φ.hs
    rw [← cancel_epi (L.map φ.s),
      MorphismProperty.RightFraction.map_s_comp_map] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by
      rw [← hφ, Category.assoc, Category.assoc, hw, comp_zero, comp_zero]) ⟨_, rfl, by simp⟩
    exact ⟨(L.objObjPreimageIso W).inv ≫ inv (L.map φ.s) ≫ l, by simp [hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.id_comp, ← L.map_comp] at hw
  rw [map_eq_zero_iff L P, ← exists_isoModSerre_comp_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  have := Localization.inverts L P.isoModSerre t ht
  rw [← Category.assoc] at fac
  refine ⟨inv (L.map t) ≫ L.map (kernel.lift _ _ fac), ?_⟩
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, IsIso.inv_comp_eq,
    ← L.map_comp, kernel.lift_ι]

lemma preservesCokernel {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices ∀ (W : D) (z : L.obj Y ⟶ W) (hz : L.map f ≫ z = 0),
      ∃ (l : L.obj (cokernel f) ⟶ W), L.map (cokernel.π  f) ≫ l = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : ∃ (Z : C) (hZ : L.obj Z = W) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (w ≫ (L.objObjPreimageIso W).inv)
    have _ := Localization.inverts L P.isoModSerre φ.s φ.hs
    rw [← cancel_mono (L.map φ.s), Category.assoc,
      MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso W).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp] at hw
  rw [map_eq_zero_iff L P, ← exists_comp_isoModSerre_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  rw [Category.assoc] at fac
  have := Localization.inverts L P.isoModSerre t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

lemma hasKernels : HasKernels D where
  has_limit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e))

lemma hasCokernels : HasCokernels D where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm))

lemma hasEqualizers : HasEqualizers D :=
  have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _

lemma hasCoequalizers : HasCoequalizers D :=
  have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g := by
    exact Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _

lemma hasBinaryProducts : HasBinaryProducts D := by
  have := Localization.essSurj L P.isoModSerre
  have (X Y : D) : HasBinaryProduct X Y :=
    hasLimit_of_iso (show Limits.pair _ _ ≅ _ from
      mapPairIso (L.objObjPreimageIso X) (L.objObjPreimageIso Y))
  exact hasBinaryProducts_of_hasLimit_pair D

lemma hasFiniteProducts : HasFiniteProducts D :=
  have := hasZeroObject L P
  have := hasBinaryProducts L P
  hasFiniteProducts_of_has_binary_and_terminal

lemma isNormalMonoCategory : IsNormalMonoCategory D where
  normalMonoOfMono f hf := by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    have := preservesKernel L P hf'.g
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }

lemma isNormalEpiCategory : IsNormalEpiCategory D where
  normalEpiOfEpi f hf := by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    have := preservesCokernel L P hf'.g
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

/-- If `L : C ⥤ D` is a localization functor with respect to a Serre class `P` in
the abelian category `C`, then `D` is an abelian category.
(Note that we assume that `D` has already been equipped with a preadditive structure,
and that `L` is additive. Otherwise, see the results in the file
`Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`
which applies because `P.isoModSerre` has a calculus of left and right fractions.) -/
@[stacks 02MS]
def abelian : Abelian D := by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor

lemma preservesFiniteLimits : PreservesFiniteLimits L := by
  letI := abelian L P
  have := (Functor.preservesFiniteLimits_tfae L).out 3 2
  rw [this]
  intro _ _ f
  exact preservesKernel L P f

lemma preservesFiniteColimits : PreservesFiniteColimits L := by
  letI := abelian L P
  have := (Functor.preservesFiniteColimits_tfae L).out 3 2
  rw [this]
  intro _ _ f
  exact preservesCokernel L P f

lemma isIso_map_iff {X Y : C} (f : X ⟶ Y) :
    IsIso (L.map f) ↔ P.isoModSerre f := by
  letI := abelian L P
  rw [isIso_iff_mono_and_epi, mono_map_iff L P, epi_map_iff L P, isoModSerre_iff]

lemma inverseImage_isomorphisms :
    (MorphismProperty.isomorphisms _).inverseImage L = P.isoModSerre := by
  ext
  simp [isIso_map_iff L P]

variable (G : D ⥤ E)

lemma preservesFiniteLimits_comp_iff :
    PreservesFiniteLimits (L ⋙ G) ↔ PreservesFiniteLimits G := by
  letI := abelian L P
  have := preservesFiniteLimits L P
  refine ⟨fun _ ↦ ?_, fun _ ↦ comp_preservesFiniteLimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).2
    ((L ⋙ G).additive_of_preserves_binary_products)
  refine ((Functor.preservesFiniteLimits_tfae G).out 2 3).1 (fun _ _ f ↦ ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesLimit (parallelPair (L.map f'.hom) 0) G :=
    preservesLimit_of_preserves_limit_cone
      ((KernelFork.isLimitMapConeEquiv _ _).1
        (isLimitOfPreserves L (kernelIsKernel f'.hom)))
          ((KernelFork.isLimitMapConeEquiv _ G).2
            ((KernelFork.isLimitMapConeEquiv _ (L ⋙ G)).1
              (isLimitOfPreserves (L ⋙ G) (kernelIsKernel f'.hom))))
  exact preservesLimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

lemma preservesFiniteColimits_comp_iff :
    PreservesFiniteColimits (L ⋙ G) ↔ PreservesFiniteColimits G := by
  letI := abelian L P
  have := preservesFiniteColimits L P
  refine ⟨fun _ ↦ ?_, fun _ ↦ comp_preservesFiniteColimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).2 (by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (L ⋙ G)
    exact Functor.additive_of_preservesBinaryBiproducts _)
  refine ((Functor.preservesFiniteColimits_tfae G).out 2 3).1 (fun _ _ f ↦ ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesColimit (parallelPair (L.map f'.hom) 0) G :=
    preservesColimit_of_preserves_colimit_cocone
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
        (isColimitOfPreserves L (cokernelIsCokernel f'.hom)))
          ((CokernelCofork.isColimitMapCoconeEquiv _ G).2
            ((CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ G)).1
              (isColimitOfPreserves (L ⋙ G) (cokernelIsCokernel f'.hom))))
  exact preservesColimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

lemma exactFunctor_comp_iff :
    exactFunctor _ _ (L ⋙ G) ↔ exactFunctor _ _ G := by
  simp [preservesFiniteLimits_comp_iff L P, preservesFiniteColimits_comp_iff L P]

variable (E)

/-- When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, this is the functor `(D ⥤ₑ E) ⥤ C ⥤ₑ E`
obtained by precomposition with `L`. -/
def whiskeringLeft : (D ⥤ₑ E) ⥤ C ⥤ₑ E :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj L) (fun G ↦ by
      dsimp
      simpa only [exactFunctor_comp_iff L P] using G.property)

@[simp]
lemma whiskeringLeft_obj_obj (G : D ⥤ₑ E) :
    ((whiskeringLeft L P E).obj G).obj = L ⋙ G.obj := rfl

/-- When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, the functor `whiskeringLeft L P E: (D ⥤ₑ E) ⥤ C ⥤ₑ E`
is fully faithful. -/
noncomputable def fullyFaithfulWhiskeringLeft :
    (whiskeringLeft L P E).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
   ((exactFunctor D E).fullyFaithfulι.comp
    (Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre E))

instance : (whiskeringLeft L P E).Faithful :=
  (fullyFaithfulWhiskeringLeft L P E).faithful

instance : (whiskeringLeft L P E).Full :=
  (fullyFaithfulWhiskeringLeft L P E).full

lemma essImage_whiskeringLeft :
    (whiskeringLeft L P E).essImage =
      fun G ↦ P.isoModSerre.IsInvertedBy G.obj := by
  ext F
  refine ⟨?_, fun hF ↦ ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _
      (show  L ⋙ G.obj ≅ F.obj from (ObjectProperty.ι _).mapIso e)]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  · refine ⟨⟨Localization.lift F.obj hF L, ?_⟩,
      ⟨ObjectProperty.isoMk _ (Localization.fac F.obj hF L)⟩⟩
    rw [← exactFunctor_comp_iff L P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac F.obj hF L).symm F.property

end SerreClassLocalization

end ObjectProperty

end CategoryTheory
