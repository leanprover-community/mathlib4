/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Lifting of bifunctors

In this file, in the context of the localization of categories, we extend the notion
of lifting of functors to the case of bifunctors. As the localization of categories
behaves well with respect to finite products of categories (when the classes of
morphisms contain identities), all the definitions for bifunctors `C₁ ⥤ C₂ ⥤ E`
are obtained by reducing to the case of functors `(C₁ × C₂) ⥤ E` by using
currying and uncurrying.

Given morphism properties `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`,
and a functor `F : C₁ ⥤ C₂ ⥤ E`, we define `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`
as the condition that the functor `uncurry.obj F : C₁ × C₂ ⥤ E` inverts `W₁.prod W₂`.

If `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are localization functors for `W₁` and `W₂`
respectively, and `F : C₁ ⥤ C₂ ⥤ E` satisfies `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`,
we introduce `Localization.lift₂ F hF L₁ L₂ : D₁ ⥤ D₂ ⥤ E` which is a bifunctor
which lifts `F`.

-/

@[expose] public section

namespace CategoryTheory

open Category Functor

variable {C₁ C₂ D₁ D₂ E E' : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* E] [Category* E']

namespace MorphismProperty

/-- Classes of morphisms `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂` are said
to be inverted by `F : C₁ ⥤ C₂ ⥤ E` if `W₁.prod W₂` is inverted by
the functor `uncurry.obj F : C₁ × C₂ ⥤ E`. -/
def IsInvertedBy₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

end MorphismProperty

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

/-- Given functors `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂`, morphisms properties `W₁` on `C₁`
and `W₂` on `C₂`, and functors `F : C₁ ⥤ C₂ ⥤ E` and `F' : D₁ ⥤ D₂ ⥤ E`, we say
`Lifting₂ L₁ L₂ W₁ W₂ F F'` holds if `F` is induced by `F'`, up to an isomorphism. -/
class Lifting₂ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) where
  /-- the isomorphism `(((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F` expressing
  that `F` is induced by `F'` up to an isomorphism -/
  iso (L₁ L₂ W₁ W₂ F F') : (((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']

/-- If `Lifting₂ L₁ L₂ W₁ W₂ F F'` holds, then `Lifting L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))`
holds for any `X₁ : C₁`. -/
@[implicit_reducible]
noncomputable def Lifting₂.fst (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁)) where
  iso := ((evaluation _ _).obj X₁).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

noncomputable instance Lifting₂.flip : Lifting₂ L₂ L₁ W₂ W₁ F.flip F'.flip where
  iso := (flipFunctor _ _ _).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

/-- If `Lifting₂ L₁ L₂ W₁ W₂ F F'` holds, then
`Lifting L₁ W₁ (F.flip.obj X₂) (F'.flip.obj (L₂.obj X₂))` holds for any `X₂ : C₂`. -/
@[implicit_reducible]
noncomputable def Lifting₂.snd (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) (F'.flip.obj (L₂.obj X₂)) :=
  Lifting₂.fst L₂ L₁ W₂ W₁ F.flip F'.flip X₂

noncomputable instance Lifting₂.uncurry :
    Lifting (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F) (uncurry.obj F') where
  iso := Functor.uncurry.mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (hF : MorphismProperty.IsInvertedBy₂ W₁ W₂ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- Given localization functor `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with respect
to `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂` respectively,
and a bifunctor `F : C₁ ⥤ C₂ ⥤ E` which inverts `W₁` and `W₂`, this is
the induced localized bifunctor `D₁ ⥤ D₂ ⥤ E`. -/
noncomputable def lift₂ : D₁ ⥤ D₂ ⥤ E :=
  curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

noncomputable instance : Lifting₂ L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂) where
  iso := (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

noncomputable instance Lifting₂.liftingLift₂ (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁)) :=
  Lifting₂.fst _ _ W₁ _ _ _ _

noncomputable instance Lifting₂.liftingLift₂Flip (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂)) :=
  Lifting₂.snd _ _ _ W₂ _ _ _

lemma lift₂_iso_hom_app_app₁ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁))).hom.app X₂ :=
  rfl

lemma lift₂_iso_hom_app_app₂ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂))).hom.app X₁ :=
  rfl

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F F']

noncomputable instance Lifting₂.compRight {E' : Type*} [Category* E'] (G : E ⥤ E') :
    Lifting₂ L₁ L₂ W₁ W₂
      (F ⋙ (whiskeringRight _ _ _).obj G)
      (F' ⋙ (whiskeringRight _ _ _).obj G) :=
  ⟨isoWhiskerRight (iso L₁ L₂ W₁ W₂ F F') ((whiskeringRight _ _ _).obj G)⟩

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂']

/-- The natural transformation `F₁' ⟶ F₂'` of bifunctors induced by a
natural transformation `τ : F₁ ⟶ F₂` when `Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'`
and `Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂'` hold. -/
noncomputable def lift₂NatTrans (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry.preimage
    (liftNatTrans (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F₁)
      (uncurry.obj F₂) (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ))

@[simp]
theorem lift₂NatTrans_app_app (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂) :
    ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).app (L₁.obj X₁)).app (L₂.obj X₂) =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F₁ F₁').hom.app X₁).app X₂ ≫ (τ.app X₁).app X₂ ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F₂ F₂').inv.app X₁).app X₂ := by
  dsimp [lift₂NatTrans, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
  simp only [comp_id, id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ) ⟨X₁, X₂⟩

variable {F₁' F₂'} in
include W₁ W₂ in
theorem natTrans₂_ext {τ τ' : F₁' ⟶ F₂'}
    (h : ∀ (X₁ : C₁) (X₂ : C₂), (τ.app (L₁.obj X₁)).app (L₂.obj X₂) =
      (τ'.app (L₁.obj X₁)).app (L₂.obj X₂)) : τ = τ' :=
  uncurry.map_injective (natTrans_ext (L₁.prod L₂) (W₁.prod W₂) (fun _ ↦ h _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F₁' ≅ F₂'` of bifunctors induced by a
natural isomorphism `e : F₁ ≅ F₂` when `Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'`
and `Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂'` hold. -/
@[simps]
noncomputable def lift₂NatIso (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e.hom
  inv := lift₂NatTrans L₁ L₂ W₁ W₂ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)
  inv_hom_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)

end

end Localization

end CategoryTheory
