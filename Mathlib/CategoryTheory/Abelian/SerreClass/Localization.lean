/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Composition

/-!
# Localization with respect to a Serre class

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

variable [Abelian C]

namespace ObjectProperty

variable (P : ObjectProperty C) [P.IsSerreClass]

lemma exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs.2
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    rw [isoModSerre_iff_of_mono]
    exact P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

lemma exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs.1
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, by simpa [isoModSerre_iff_of_epi], by simp⟩

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

end ObjectProperty

end CategoryTheory
