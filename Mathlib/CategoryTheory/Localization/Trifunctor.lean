/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.CategoryTheory.Products.Associator

/-!
# Lifting of trifunctors

In this file, in the context of the localization of categories, we extend the notion
of lifting of functors to the case of trifunctors
(see also the file `Localization.Bifunctor` for the case of bifunctors).
The main result in this file is that we can localize "associator" isomorphisms
(see the definition `Localization.associator`).

-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₁₂ C₂₃ D₁ D₂ D₃ D₁₂ D₂₃ C D E : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category D₁] [Category D₂] [Category D₃]
  [Category C₁₂] [Category C₂₃] [Category D₁₂] [Category D₂₃]
  [Category C] [Category D] [Category E]

namespace MorphismProperty

/-- Classes of morphisms `W₁ : MorphismProperty C₁`, `W₂ : MorphismProperty C₂` and
`W₃ : MorphismProperty C₃` are said to be inverted by `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E` if
`W₁.prod (W₂.prod W₃)` is inverted by the
functor `currying₃.functor.obj F : C₁ × C₂ × C₃ ⥤ E`. -/
def IsInvertedBy₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃) (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : Prop :=
  (W₁.prod (W₂.prod W₃)).IsInvertedBy (currying₃.functor.obj F)

end MorphismProperty

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)

/-- Given functors `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂`, `L₃ : C₃ ⥤ D₃`,
morphisms properties `W₁` on `C₁`, `W₂` on `C₂`, `W₃` on `C₃`, and
functors `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E` and `F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E`, we say
`Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F'` holds if `F` is induced by `F'`, up to an isomorphism. -/
class Lifting₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) where
  /-- the isomorphism `((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F` expressing
  that `F` is induced by `F'` up to an isomorphism -/
  iso' : ((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F']

/-- The isomorphism `((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F`
when `Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F'` holds. -/
noncomputable def Lifting₃.iso :
    ((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F :=
  Lifting₃.iso' W₁ W₂ W₃

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)

noncomputable instance Lifting₃.uncurry [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F'] :
    Lifting (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))
      (uncurry₃.obj F) (uncurry₃.obj F') where
  iso' := uncurry₃.mapIso (Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}
  (hF : MorphismProperty.IsInvertedBy₃ W₁ W₂ W₃ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

/-- Given localization functor `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂` and `L₃ : C₃ ⥤ D₃`
with respect to `W₁ : MorphismProperty C₁`, `W₂ : MorphismProperty C₂` and
`W₃ : MorphismProperty C₃` respectively, and a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E`
which inverts `W₁`, `W₂` and `W₃`, this is the induced localized
trifunctor `D₁ ⥤ D₂ ⥤ D₃ ⥤ E`. -/
noncomputable def lift₃ : D₁ ⥤ D₂ ⥤ D₃ ⥤ E :=
  curry₃.obj (lift (uncurry₃.obj F) hF (L₁.prod (L₂.prod L₃)))

noncomputable instance : Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F (lift₃ F hF L₁ L₂ L₃) where
  iso' :=
    (curry₃ObjProdComp L₁ L₂ L₃ _).symm ≪≫
      curry₃.mapIso (fac (uncurry₃.obj F) hF (L₁.prod (L₂.prod L₃))) ≪≫
        currying₃.unitIso.symm.app F

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)
  [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁'] [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂'] (τ : F₁ ⟶ F₂)
  (e : F₁ ≅ F₂)

/-- The natural transformation `F₁' ⟶ F₂'` of trifunctors induced by a
natural transformation `τ : F₁ ⟶ F₂` when `Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁'`
and `Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂'` hold. -/
noncomputable def lift₃NatTrans : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry₃.preimage
    (liftNatTrans (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃)) (uncurry₃.obj F₁)
      (uncurry₃.obj F₂) (uncurry₃.obj F₁') (uncurry₃.obj F₂') (uncurry₃.map τ))

@[simp]
theorem lift₃NatTrans_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₂ F₁' F₂' τ).app
        (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃) =
      (((Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁').hom.app X₁).app X₂).app X₃ ≫
        ((τ.app X₁).app X₂).app X₃ ≫
        (((Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂').inv.app X₁).app X₂).app X₃ := by
  dsimp [lift₃NatTrans, fullyFaithfulUncurry₃, Equivalence.fullyFaithfulFunctor]
  simp only [currying₃_unitIso_hom_app_app_app_app, Functor.id_obj,
    currying₃_unitIso_inv_app_app_app_app, Functor.comp_obj,
    Category.comp_id, Category.id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry₃.obj F₁') (uncurry₃.obj F₂') (uncurry₃.map τ) ⟨X₁, X₂, X₃⟩

variable {F₁' F₂'} in
include W₁ W₂ W₃ in
theorem natTrans₃_ext {τ τ' : F₁' ⟶ F₂'}
    (h : ∀ (X₁ : C₁) (X₂ : C₂) (X₃ : C₃), ((τ.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃) =
      ((τ'.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)) : τ = τ' :=
  uncurry₃.map_injective (natTrans_ext (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))
    (fun _ ↦ h _ _ _))

/-- The natural isomorphism `F₁' ≅ F₂'` of trifunctors induced by a
natural isomorphism `e : F₁ ≅ F₂` when `Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁'`
and `Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂'` hold. -/
@[simps]
noncomputable def lift₃NatIso : F₁' ≅ F₂' where
  hom := lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₂ F₁' F₂' e.hom
  inv := lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₃_ext L₁ L₂ L₃ W₁ W₂ W₃ (by aesop_cat)
  inv_hom_id := natTrans₃_ext L₁ L₂ L₃ W₁ W₂ W₃ (by aesop_cat)

end

section

variable
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₁₂ : C₁₂ ⥤ D₁₂) (L₂₃ : C₂₃ ⥤ D₂₃) (L : C ⥤ D)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (W₁₂ : MorphismProperty C₁₂) (W₂₃ : MorphismProperty C₂₃) (W : MorphismProperty C)
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] [L.IsLocalization W]
  (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C)
  (F : C₁ ⥤ C₂₃ ⥤ C) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  (iso : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  (F₁₂' : D₁ ⥤ D₂ ⥤ D₁₂) (G' : D₁₂ ⥤ D₃ ⥤ D)
  (F' : D₁ ⥤ D₂₃ ⥤ D) (G₂₃' : D₂ ⥤ D₃ ⥤ D₂₃)
  [Lifting₂ L₁ L₂ W₁ W₂ (F₁₂ ⋙ (whiskeringRight _ _ _).obj L₁₂) F₁₂']
  [Lifting₂ L₁₂ L₃ W₁₂ W₃ (G ⋙ (whiskeringRight _ _ _).obj L) G']
  [Lifting₂ L₁ L₂₃ W₁ W₂₃ (F ⋙ (whiskeringRight _ _ _).obj L) F']
  [Lifting₂ L₂ L₃ W₂ W₃ (G₂₃ ⋙ (whiskeringRight _ _ _).obj L₂₃) G₂₃']

/-- The construction `bifunctorComp₁₂` of a trifunctor by composition of bifunctors
is compatible with localization. -/
noncomputable def Lifting₃.bifunctorComp₁₂ :
    Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃
      ((Functor.postcompose₃.obj L).obj (bifunctorComp₁₂ F₁₂ G))
      (bifunctorComp₁₂ F₁₂' G') where
  iso' :=
    ((whiskeringRight C₁ _ _).obj
      ((whiskeringRight C₂ _ _).obj ((whiskeringLeft _ _ D).obj L₃))).mapIso
        ((bifunctorComp₁₂Functor.mapIso
          (Lifting₂.iso L₁ L₂ W₁ W₂ (F₁₂ ⋙ (whiskeringRight _ _ _).obj L₁₂) F₁₂')).app G') ≪≫
        (bifunctorComp₁₂Functor.obj F₁₂).mapIso
          (Lifting₂.iso L₁₂ L₃ W₁₂ W₃ (G ⋙ (whiskeringRight _ _ _).obj L) G')

/-- The construction `bifunctorComp₂₃` of a trifunctor by composition of bifunctors
is compatible with localization. -/
noncomputable def Lifting₃.bifunctorComp₂₃ :
    Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃
      ((Functor.postcompose₃.obj L).obj (bifunctorComp₂₃ F G₂₃))
      (bifunctorComp₂₃ F' G₂₃') where
  iso' :=
    ((whiskeringLeft _ _ _).obj L₁).mapIso ((bifunctorComp₂₃Functor.obj F').mapIso
      (Lifting₂.iso L₂ L₃ W₂ W₃ (G₂₃ ⋙ (whiskeringRight _ _ _).obj L₂₃) G₂₃')) ≪≫
        (bifunctorComp₂₃Functor.mapIso
          (Lifting₂.iso L₁ L₂₃ W₁ W₂₃ (F ⋙ (whiskeringRight _ _ _).obj L) F')).app G₂₃

variable {F₁₂ G F G₂₃}

/-- The associator isomorphism obtained by localization. -/
noncomputable def associator : bifunctorComp₁₂ F₁₂' G' ≅ bifunctorComp₂₃ F' G₂₃' :=
  letI := Lifting₃.bifunctorComp₁₂ L₁ L₂ L₃ L₁₂ L W₁ W₂ W₃ W₁₂ F₁₂ G F₁₂' G'
  letI := Lifting₃.bifunctorComp₂₃ L₁ L₂ L₃ L₂₃ L W₁ W₂ W₃ W₂₃ F G₂₃ F' G₂₃'
  lift₃NatIso L₁ L₂ L₃ W₁ W₂ W₃ _ _ _ _ ((Functor.postcompose₃.obj L).mapIso iso)

lemma associator_hom_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((associator L₁ L₂ L₃ L₁₂ L₂₃ L W₁ W₂ W₃ W₁₂ W₂₃ iso F₁₂' G' F' G₂₃').hom.app (L₁.obj X₁)).app
      (L₂.obj X₂)).app (L₃.obj X₃) =
        (G'.map (((Lifting₂.iso L₁ L₂ W₁ W₂
          (F₁₂ ⋙ (whiskeringRight C₂ C₁₂ D₁₂).obj L₁₂) F₁₂').hom.app X₁).app X₂)).app (L₃.obj X₃) ≫
          ((Lifting₂.iso L₁₂ L₃ W₁₂ W₃ (G ⋙ (whiskeringRight C₃ C D).obj L) G').hom.app
              ((F₁₂.obj X₁).obj X₂)).app X₃ ≫
            L.map (((iso.hom.app X₁).app X₂).app X₃) ≫
          ((Lifting₂.iso L₁ L₂₃ W₁ W₂₃
            (F ⋙ (whiskeringRight _ _ _).obj L) F').inv.app X₁).app ((G₂₃.obj X₂).obj X₃) ≫
        (F'.obj (L₁.obj X₁)).map
          (((Lifting₂.iso L₂ L₃ W₂ W₃
            (G₂₃ ⋙ (whiskeringRight _ _ _).obj L₂₃) G₂₃').inv.app X₂).app X₃) := by
  dsimp [associator]
  rw [lift₃NatTrans_app_app_app]
  dsimp [Lifting₃.iso, Lifting₃.bifunctorComp₁₂, Lifting₃.bifunctorComp₂₃]
  simp only [Category.assoc]

end

end Localization

end CategoryTheory
