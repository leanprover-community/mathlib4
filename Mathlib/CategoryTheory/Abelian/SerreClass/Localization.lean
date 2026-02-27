/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# Localization with respect to a Serre class

In this file, we shall study the localization of an abelian
category `C` with respect to the class of morphisms
`P.isoModSerre` where `P : ObjectProperty C` is a Serre class.
We shall show that the localized category is an abelian
category (TODO @joelriou).

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

open Limits ZeroObject

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]

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
noncomputable example : P.isoModSerre.Q.Additive := inferInstance

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

end SerreClassLocalization

end ObjectProperty

end CategoryTheory
