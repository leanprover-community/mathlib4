/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.CatCommSq

/-!

# Localization functors are preserved through equivalences

-/

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D D₁ D₂ : Type _} [Category C₁] [Category C₂] [Category D]
  [Category D₁] [Category D₂]

namespace Localization

variable
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G : C₁ ⥤ D₂) (G' : D₁ ⥤ D₂) [Lifting L₁ W₁ G G']
  (F : C₂ ⥤ D₁) (F' : D₂ ⥤ D₁) [Lifting L₂ W₂ F F']
  (α : G ⋙ F' ≅ L₁) (β : F ⋙ G' ≅ L₂)

/-- basic constructor of an equivalence between localized categories -/
noncomputable def equivalence : D₁ ≌ D₂ :=
  Equivalence.mk G' F' (liftNatIso L₁ W₁ L₁ (G ⋙ F') (𝟭 D₁) (G' ⋙ F') α.symm)
    (liftNatIso L₂ W₂ (F ⋙ G') L₂ (F' ⋙ G') (𝟭 D₂) β)

@[simp]
lemma equivalence_counit_app (X : C₂) :
    (equivalence L₁ W₁ L₂ W₂ G G' F F' α β).counitIso.app (L₂.obj X) =
      (Lifting.iso L₂ W₂ (F ⋙ G') (F' ⋙ G')).app X ≪≫ β.app X := by
  ext
  dsimp [equivalence, Equivalence.mk]
  rw [liftNatTrans_app]
  dsimp [Lifting.iso]
  rw [comp_id]

/-- basic construction of an equivalence between localized categories -/
noncomputable def isEquivalence : IsEquivalence G' :=
  IsEquivalence.ofEquivalence (equivalence L₁ W₁ L₂ W₂ G G' F F' α β)

end Localization

namespace Functor

namespace IsLocalization

lemma of_equivalence_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁) (L₂ : C₂ ⥤ D) (W₂ : MorphismProperty C₂)
  (E : C₁ ≌ C₂) (hW₁ : W₁ ⊆ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂)
  [L₁.IsLocalization W₁] (iso : E.functor ⋙ L₂ ≅ L₁) : L₂.IsLocalization W₂ := by
  have h : W₁.IsInvertedBy (E.functor ⋙ W₂.Q) := fun _ _ f hf => by
    obtain ⟨_, _, f', hf', ⟨e⟩⟩ := hW₁ f hf
    exact ((MorphismProperty.RespectsIso.isomorphisms _).arrow_mk_iso_iff
      (W₂.Q.mapArrow.mapIso e)).1 (Localization.inverts W₂.Q W₂ _ hf')
  exact
  { inverts := hW₂
    nonempty_isEquivalence :=
      ⟨Localization.isEquivalence W₂.Q W₂ L₁ W₁ L₂ (Construction.lift L₂ hW₂)
        (E.functor ⋙ W₂.Q) (Localization.lift (E.functor ⋙ W₂.Q) h L₁)
        ((leftUnitor _).symm ≪≫ isoWhiskerRight E.counitIso.symm _ ≪≫
          Functor.associator _ _ _ ≪≫
          isoWhiskerLeft E.inverse ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight iso _) ≪≫
          isoWhiskerLeft _ (Localization.fac (E.functor ⋙ W₂.Q) h L₁) ≪≫
          (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight E.counitIso _ ≪≫ leftUnitor _ )
        (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Lifting.iso W₂.Q W₂ _ _)  ≪≫ iso) ⟩ }

lemma of_equivalences (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂)
  (E : C₁ ≌ C₂) (E' : D₁ ≌ D₂) [CatCommSq E.functor L₁ L₂ E'.functor]
  (hW₁ : W₁ ⊆ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂): L₂.IsLocalization W₂ := by
  haveI : (E.functor ⋙ L₂).IsLocalization W₁ :=
    of_equivalence_target L₁ W₁ _ E' ((CatCommSq.iso _ _ _ _).symm)
  exact of_equivalence_source (E.functor ⋙ L₂) W₁ L₂ W₂ E hW₁ hW₂ (Iso.refl _)

end IsLocalization

end Functor

end CategoryTheory
