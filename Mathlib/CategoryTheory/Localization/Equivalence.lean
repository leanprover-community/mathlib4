/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Localization functors are preserved through equivalences

In `Mathlib/CategoryTheory/Localization/Predicate.lean`, the lemma
`Localization.of_equivalence_target` already showed that the predicate of localized categories is
unchanged when we replace the target category (i.e. the candidate localized category) by an
equivalent category.
In this file, we show the same for the source category (`Localization.of_equivalence_source`).
More generally, `Localization.of_equivalences` shows that we may replace both the
source and target categories by equivalent categories. This is obtained using
`Localization.isEquivalence` which provide a sufficient condition in order to show
that a functor between localized categories is an equivalence.

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* D₁] [Category* D₂]

namespace Localization

variable
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G : C₁ ⥤ D₂) (G' : D₁ ⥤ D₂) [Lifting L₁ W₁ G G']
  (F : C₂ ⥤ D₁) (F' : D₂ ⥤ D₁) [Lifting L₂ W₂ F F']
  (α : G ⋙ F' ≅ L₁) (β : F ⋙ G' ≅ L₂)

/-- Basic constructor of an equivalence between localized categories -/
noncomputable def equivalence : D₁ ≌ D₂ :=
  Equivalence.mk G' F' (liftNatIso L₁ W₁ L₁ (G ⋙ F') (𝟭 D₁) (G' ⋙ F') α.symm)
    (liftNatIso L₂ W₂ (F ⋙ G') L₂ (F' ⋙ G') (𝟭 D₂) β)

@[simp]
lemma equivalence_counitIso_app (X : C₂) :
    (equivalence L₁ W₁ L₂ W₂ G G' F F' α β).counitIso.app (L₂.obj X) =
      (Lifting.iso L₂ W₂ (F ⋙ G') (F' ⋙ G')).app X ≪≫ β.app X := by
  ext
  dsimp [equivalence, Equivalence.mk]
  rw [liftNatTrans_app]
  dsimp [Lifting.iso]
  rw [comp_id]

include L₁ W₁ L₂ W₂ G F F' α β in
/-- Basic constructor of an equivalence between localized categories -/
lemma isEquivalence : G'.IsEquivalence :=
  (equivalence L₁ W₁ L₂ W₂ G G' F F' α β).isEquivalence_functor

end Localization

namespace Functor

namespace IsLocalization

/-- If `L₁ : C₁ ⥤ D` is a localization functor for `W₁ : MorphismProperty C₁`, then it is also
the case of a functor `L₂ : C₂ ⥤ D` for a suitable `W₂ : MorphismProperty C₂` when
we have an equivalence of category `E : C₁ ≌ C₂` and an isomorphism `E.functor ⋙ L₂ ≅ L₁`. -/
lemma of_equivalence_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁)
    (L₂ : C₂ ⥤ D) (W₂ : MorphismProperty C₂)
    (E : C₁ ≌ C₂) (hW₁ : W₁ ≤ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂)
    [L₁.IsLocalization W₁] (iso : E.functor ⋙ L₂ ≅ L₁) : L₂.IsLocalization W₂ := by
  have h : W₁.IsInvertedBy (E.functor ⋙ W₂.Q) := fun _ _ f hf => by
    obtain ⟨_, _, f', hf', ⟨e⟩⟩ := hW₁ f hf
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (W₂.Q.mapArrow.mapIso e)).1 (Localization.inverts W₂.Q W₂ _ hf')
  exact
    { inverts := hW₂
      isEquivalence :=
        Localization.isEquivalence W₂.Q W₂ L₁ W₁ L₂ (Construction.lift L₂ hW₂)
          (E.functor ⋙ W₂.Q) (Localization.lift (E.functor ⋙ W₂.Q) h L₁) (by
            calc
              L₂ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ ≅ _ := (leftUnitor _).symm
              _ ≅ _ := isoWhiskerRight E.counitIso.symm _
              _ ≅ E.inverse ⋙ E.functor ⋙ L₂ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ :=
                    Functor.associator _ _ _
              _ ≅ E.inverse ⋙ L₁ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ :=
                    isoWhiskerLeft E.inverse ((Functor.associator _ _ _).symm ≪≫
                      isoWhiskerRight iso _)
              _ ≅ E.inverse ⋙ E.functor ⋙ W₂.Q :=
                    isoWhiskerLeft _ (Localization.fac (E.functor ⋙ W₂.Q) h L₁)
              _ ≅ (E.inverse ⋙ E.functor) ⋙ W₂.Q := (Functor.associator _ _ _).symm
              _ ≅ 𝟭 C₂ ⋙ W₂.Q := isoWhiskerRight E.counitIso _
              _ ≅ W₂.Q := leftUnitor _)
          (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Lifting.iso W₂.Q W₂ _ _) ≪≫ iso) }

/-- If `L₁ : C₁ ⥤ D₁` is a localization functor for `W₁ : MorphismProperty C₁`, then if we
transport this functor `L₁` via equivalences `C₁ ≌ C₂` and `D₁ ≌ D₂` to get a functor
`L₂ : C₂ ⥤ D₂`, then `L₂` is also a localization functor for
a suitable `W₂ : MorphismProperty C₂`. -/
lemma of_equivalences (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂)
    (E : C₁ ≌ C₂) (E' : D₁ ≌ D₂) [CatCommSq E.functor L₁ L₂ E'.functor]
    (hW₁ : W₁ ≤ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂) :
    L₂.IsLocalization W₂ := by
  haveI : (E.functor ⋙ L₂).IsLocalization W₁ :=
    of_equivalence_target L₁ W₁ _ E' ((CatCommSq.iso _ _ _ _).symm)
  exact of_equivalence_source (E.functor ⋙ L₂) W₁ L₂ W₂ E hW₁ hW₂ (Iso.refl _)

end IsLocalization

end Functor

end CategoryTheory
