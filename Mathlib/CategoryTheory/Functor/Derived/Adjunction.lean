/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Derived adjunction

Assume that functors `G : C₁ ⥤ C₂` and `F : C₂ ⥤ C₁` are part of an
adjunction `adj : G ⊣ F`, that we have localization
functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with respect to
classes of morphisms `W₁` and `W₂`, and that `G` admits
a left derived functor `G' : D₁ ⥤ D₂` and `F` a right derived
functor `F' : D₂ ⥤ D₁`. We show that there is an adjunction
`G' ⊣ F'` under the additional assumption that `F'` and `G'`
are *absolute* derived functors, i.e. they remain derived
functors after the post-composition with any functor
(we actually only need to know that `G' ⋙ F'` is the
left derived functor of `G ⋙ L₂ ⋙ F'` and
that `F' ⋙ G'` is the right derived functor of `F ⋙ L₁ ⋙ G'`).

## References

* [Georges Maltsiniotis, *Le théorème de Quillen, d'adjonction des
foncteurs dérivés, revisité*][Maltsiniotis2007]

-/

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {G' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁}
  (α : L₁ ⋙ G' ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ F')

namespace Adjunction

open Functor

/-- Auxiliary definition for `Adjunction.derived`. -/
@[simps]
def derived' [G'.IsLeftDerivedFunctor α W₁] [F'.IsRightDerivedFunctor β W₂]
    (η : 𝟭 D₁ ⟶ G' ⋙ F') (ε : F' ⋙ G' ⟶ 𝟭 D₂)
    (hη : ∀ (X₁ : C₁), η.app (L₁.obj X₁) ≫ F'.map (α.app X₁) =
      L₁.map (adj.unit.app X₁) ≫ β.app (G.obj X₁) := by cat_disch)
    (hε : ∀ (X₂ : C₂), G'.map (β.app X₂) ≫ ε.app (L₂.obj X₂) =
      α.app (F.obj X₂) ≫ L₂.map (adj.counit.app X₂) := by cat_disch) : G' ⊣ F' where
  unit := η
  counit := ε
  left_triangle_components := by
    suffices G'.leftUnitor.inv ≫ whiskerRight η G' ≫ (Functor.associator _ _ _ ).hom ≫
        whiskerLeft G' ε ≫ G'.rightUnitor.hom = 𝟙 _ from
      fun Y₁ ↦ by simpa using congr_app this Y₁
    apply G'.leftDerived_ext α W₁
    ext X₁
    have eq₁ := ε.naturality (α.app X₁)
    have eq₂ := G'.congr_map (hη X₁)
    have eq₃ := α.naturality (adj.unit.app X₁)
    dsimp at eq₁ eq₂ eq₃ ⊢
    simp only [Functor.map_comp] at eq₂
    rw [Category.assoc, Category.assoc, Category.assoc, Category.comp_id,
      Category.id_comp, Category.id_comp, Category.id_comp, ← eq₁, reassoc_of% eq₂,
      hε (G.obj X₁), reassoc_of% eq₃, ← L₂.map_comp, adj.left_triangle_components,
      Functor.map_id, Category.comp_id]
  right_triangle_components := by
    suffices F'.leftUnitor.inv ≫ whiskerLeft F' η ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ε F' ≫ F'.rightUnitor.hom = 𝟙 _ from
        fun Y₂ ↦ by simpa using congr_app this Y₂
    apply F'.rightDerived_ext β W₂
    ext X₂
    have eq₁ := η.naturality (β.app X₂)
    have eq₂ := F'.congr_map (hε X₂)
    have eq₃ := β.naturality (adj.counit.app X₂)
    dsimp at eq₁ eq₂ eq₃ ⊢
    simp only [Functor.map_comp] at eq₂
    rw [Category.comp_id, Category.comp_id, Category.id_comp, Category.id_comp,
      reassoc_of% eq₁, eq₂, reassoc_of% (hη (F.obj X₂)), ← eq₃, ← L₁.map_comp_assoc,
      adj.right_triangle_components, Functor.map_id, Category.id_comp]

section

variable [(G' ⋙ F').IsLeftDerivedFunctor
  ((Functor.associator _ _ _).inv ≫ whiskerRight α F') W₁]

/-- The unit of the derived adjunction, see `Adjunction.derived`. -/
noncomputable def derivedη : 𝟭 D₁ ⟶ G' ⋙ F' :=
  (G' ⋙ F').leftDerivedLift ((Functor.associator _ _ _).inv ≫ whiskerRight α F') W₁ _
    (L₁.rightUnitor.hom ≫ L₁.leftUnitor.inv ≫ whiskerRight adj.unit L₁ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G β ≫ (Functor.associator _ _ _).inv)

@[reassoc (attr := simp)]
lemma derivedη_fac_app (X₁ : C₁) :
    (adj.derivedη W₁ α β).app (L₁.obj X₁) ≫ F'.map (α.app X₁) =
      L₁.map (adj.unit.app X₁) ≫ β.app (G.obj X₁) := by
  simpa using ((G' ⋙ F').leftDerived_fac_app ((Functor.associator _ _ _).inv ≫
    whiskerRight α F') W₁ _ (L₁.rightUnitor.hom ≫ L₁.leftUnitor.inv ≫ whiskerRight adj.unit L₁ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G β ≫ (Functor.associator _ _ _).inv)) X₁

end

section

variable [(F' ⋙ G').IsRightDerivedFunctor
  (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂]

/-- The counit of the derived adjunction, see `Adjunction.derived`. -/
noncomputable def derivedε : F' ⋙ G' ⟶ 𝟭 D₂ :=
  (F' ⋙ G').rightDerivedDesc (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂ _
    ((Functor.associator _ _ _).hom ≫ whiskerLeft F α ≫ (Functor.associator _ _ _).inv ≫
        whiskerRight adj.counit _ ≫ L₂.leftUnitor.hom ≫ L₂.rightUnitor.inv)

@[reassoc (attr := simp)]
lemma derivedε_fac_app (X₂ : C₂) :
    G'.map (β.app X₂) ≫ (adj.derivedε W₂ α β).app (L₂.obj X₂) =
      α.app (F.obj X₂) ≫ L₂.map (adj.counit.app X₂) := by
  simpa using ((F' ⋙ G').rightDerived_fac_app
    (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂ _
    ((Functor.associator _ _ _).hom ≫ whiskerLeft F α ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight adj.counit _ ≫ L₂.leftUnitor.hom ≫ L₂.rightUnitor.inv)) X₂

end

/-- An adjunction between functors induces an adjunction between the
corresponding left/right derived functors, when these derived
functors are *absolute*, i.e. they remain derived functors
after the post-composition with any functor.

(One actually only needs that `G' ⋙ F'` is the left derived functor of
`G ⋙ L₂ ⋙ F'` and that `F' ⋙ G'` is the right derived functor of
`F ⋙ L₁ ⋙ G'`). -/
@[simps!]
noncomputable def derived [G'.IsLeftDerivedFunctor α W₁] [F'.IsRightDerivedFunctor β W₂]
    [(G' ⋙ F').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α F') W₁]
    [(F' ⋙ G').IsRightDerivedFunctor
      (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂] : G' ⊣ F' :=
  adj.derived' W₁ W₂ α β (adj.derivedη W₁ α β) (adj.derivedε W₂ α β)

end Adjunction

end CategoryTheory
