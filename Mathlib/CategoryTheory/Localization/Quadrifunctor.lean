/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.CurryingFour
public import Mathlib.CategoryTheory.Localization.Trifunctor

/-!
# Lifting of quadrifunctors

In this file, in the context of the localization of categories, we extend the notion of lifting
of functors to the case of quadrifunctors. The definitions reduce to functors on the
right-associated product category by currying and uncurrying.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄] [Category* E]

namespace MorphismProperty

/-- Classes of morphisms `W₁ : MorphismProperty C₁`, `W₂ : MorphismProperty C₂`,
`W₃ : MorphismProperty C₃` and `W₄ : MorphismProperty C₄` are said to be inverted by
`F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E` if `W₁.prod (W₂.prod (W₃.prod W₄))` is inverted by the functor
`currying₄.functor.obj F : C₁ × C₂ × C₃ × C₄ ⥤ E`. -/
def IsInvertedBy₄ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃) (W₄ : MorphismProperty C₄)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) : Prop :=
  (W₁.prod (W₂.prod (W₃.prod W₄))).IsInvertedBy (currying₄.functor.obj F)

end MorphismProperty

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)

/-- Given functors `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂`, `L₃ : C₃ ⥤ D₃`, `L₄ : C₄ ⥤ D₄`,
morphism properties `W₁` on `C₁`, `W₂` on `C₂`, `W₃` on `C₃`, `W₄` on `C₄`, and functors
`F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E` and `F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E`, we say
`Lifting₄ L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F F'` holds if `F` is induced by `F'`, up to an
isomorphism. -/
class Lifting₄ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
    (W₄ : MorphismProperty C₄) (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) where
  /-- The isomorphism expressing that `F` is induced by `F'`, up to an isomorphism. -/
  iso (L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F F') :
    (((((whiskeringLeft₄ E).obj L₁).obj L₂).obj L₃).obj L₄).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (W₃ : MorphismProperty C₃) (W₄ : MorphismProperty C₄)
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E)

noncomputable instance Lifting₄.uncurry [Lifting₄ L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F F'] :
    Lifting (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
      (uncurry₄.obj F) (uncurry₄.obj F') where
  iso := uncurry₄.mapIso (Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃} {W₄ : MorphismProperty C₄}
  (hF : MorphismProperty.IsInvertedBy₄ W₁ W₂ W₃ W₄ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [L₄.IsLocalization W₄] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₃.ContainsIdentities] [W₄.ContainsIdentities]

/-- Given localization functors `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂`, `L₃ : C₃ ⥤ D₃` and
`L₄ : C₄ ⥤ D₄` with respect to `W₁ : MorphismProperty C₁`, `W₂ : MorphismProperty C₂`,
`W₃ : MorphismProperty C₃` and `W₄ : MorphismProperty C₄`, respectively, and a quadrifunctor
`F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E` which inverts `W₁`, `W₂`, `W₃` and `W₄`, this is the induced
localized quadrifunctor `D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E`. -/
noncomputable def lift₄ : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E :=
  curry₄.obj (lift (uncurry₄.obj F) hF (L₁.prod (L₂.prod (L₃.prod L₄))))

noncomputable instance : Lifting₄ L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F
    (lift₄ F hF L₁ L₂ L₃ L₄) where
  iso :=
    (curry₄ObjProdComp L₁ L₂ L₃ L₄ _).symm ≪≫
      curry₄.mapIso (fac (uncurry₄.obj F) hF (L₁.prod (L₂.prod (L₃.prod L₄)))) ≪≫
        currying₄.unitIso.symm.app F

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (W₃ : MorphismProperty C₃) (W₄ : MorphismProperty C₄)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [L₄.IsLocalization W₄] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₃.ContainsIdentities] [W₄.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
  (F₁' F₂' : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E)
  [Lifting₄ L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁']
  [Lifting₄ L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂'] (τ : F₁ ⟶ F₂) (e : F₁ ≅ F₂)

/-- The natural transformation `F₁' ⟶ F₂'` of quadrifunctors induced by a natural transformation
`τ : F₁ ⟶ F₂` when `F₁'` and `F₂'` lift `F₁` and `F₂`, respectively. -/
noncomputable def lift₄NatTrans : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry₄.preimage
    (liftNatTrans (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
      (uncurry₄.obj F₁) (uncurry₄.obj F₂) (uncurry₄.obj F₁') (uncurry₄.obj F₂')
      (uncurry₄.map τ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem lift₄NatTrans_app_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₂ F₁' F₂' τ).app
      (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)).app (L₄.obj X₄) =
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').hom.app X₁).app X₂).app X₃).app X₄ ≫
          (((τ.app X₁).app X₂).app X₃).app X₄ ≫
          ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').inv.app X₁).app X₂).app X₃).app X₄ := by
  dsimp [lift₄NatTrans, fullyFaithfulUncurry₄, Equivalence.fullyFaithfulFunctor]
  simp only [currying₄_unitIso_hom_app_app_app_app_app, Functor.id_obj,
    currying₄_unitIso_inv_app_app_app_app_app, Functor.comp_obj, Category.comp_id,
    Category.id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry₄.obj F₁') (uncurry₄.obj F₂') (uncurry₄.map τ)
    ⟨X₁, X₂, X₃, X₄⟩

variable {F₁' F₂'} in
include W₁ W₂ W₃ W₄ in
/-- Two natural transformations between quadrifunctors on localized categories are equal if
their components agree on objects in the images of the four localization functors. -/
theorem natTrans₄_ext {τ τ' : F₁' ⟶ F₂'}
    (h : ∀ (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄),
      ((((τ.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)).app (L₄.obj X₄)) =
        ((((τ'.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)).app (L₄.obj X₄))) :
    τ = τ' :=
  uncurry₄.map_injective
    (natTrans_ext (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
      (fun _ ↦ h _ _ _ _))

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `F₁' ≅ F₂'` of quadrifunctors induced by a natural isomorphism
`e : F₁ ≅ F₂` when `F₁'` and `F₂'` lift `F₁` and `F₂`, respectively. -/
@[simps]
noncomputable def lift₄NatIso : F₁' ≅ F₂' where
  hom := lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₂ F₁' F₂' e.hom
  inv := lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₄_ext L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄
    (fun X₁ X₂ X₃ X₄ ↦ by
      simp only [NatTrans.comp_app, lift₄NatTrans_app_app_app_app, NatTrans.id_app]
      let e₁ :=
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').app X₁).app X₂).app X₃).app X₄
      let e₂ := (((e.app X₁).app X₂).app X₃).app X₄
      let e₃ :=
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').app X₁).app X₂).app X₃).app X₄
      simpa [e₁, e₂, e₃, Category.assoc] using (e₁ ≪≫ e₂ ≪≫ e₃.symm).hom_inv_id)
  inv_hom_id := natTrans₄_ext L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄
    (fun X₁ X₂ X₃ X₄ ↦ by
      simp only [NatTrans.comp_app, lift₄NatTrans_app_app_app_app, NatTrans.id_app]
      let e₁ :=
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').app X₁).app X₂).app X₃).app X₄
      let e₂ := (((e.app X₁).app X₂).app X₃).app X₄
      let e₃ :=
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').app X₁).app X₂).app X₃).app X₄
      simpa [e₁, e₂, e₃, Category.assoc] using (e₃ ≪≫ e₂.symm ≪≫ e₁.symm).hom_inv_id)

end

end Localization

end CategoryTheory
