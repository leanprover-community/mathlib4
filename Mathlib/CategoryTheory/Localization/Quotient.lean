/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Quotient

/-!
# Localization of quotient categories

Given a relation `homRel : HomRel C` on morphisms in a category `C`
and `W : MorphismProperty C`, we introduce a property
`homRel.FactorsThroughLocalization W` expressing that related
morphisms are mapped to the same morphism in the localized
category with respect to `W`. When `W` is compatible with `homRel`
(i.e. there is a class of morphisms `W'` such that
`hW : W = W'.inverseImage (Quotient.functor homRel)`),
we show that `LocalizerMorphism.ofEq hW : LocalizerMorphism W W'`
induces an equivalence on localized categories.

-/

namespace HomRel

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] (homRel : HomRel C)

/-- Given `homRel : HomRel C` and `W : MorphismProperty C`, this is the property
that whenever `homRel f g`, then the morphisms `f` and `g` are sent to the
same morphism in the localization category with respect to `W`. -/
def FactorsThroughLocalization (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g → AreEqualizedByLocalization W f g

variable {homRel} {W : MorphismProperty C}
  (h : homRel.FactorsThroughLocalization W)
  {W' : MorphismProperty (Quotient homRel)}
  (hW : W = W'.inverseImage (Quotient.functor homRel))

namespace FactorsThroughLocalization

open Localization

section

variable {E : Type*} [Category E]

/-- If `L' : Quotient homRel ⥤ D` satisfies the strict universal property of the
localization, then `Quotient.functor homRel ⋙ L'` also satisfies it. -/
def strictUniversalPropertyFixedTarget (L' : Quotient homRel ⥤ D)
    (univ : StrictUniversalPropertyFixedTarget L' W' E) :
      StrictUniversalPropertyFixedTarget
        (Quotient.functor homRel ⋙ L') W E where
  inverts _ _ _ hf := univ.inverts _ (by rwa [hW] at hf)
  lift F hF :=
    univ.lift (CategoryTheory.Quotient.lift _ F
        (fun _ _ f g hfg ↦ (h hfg).map_eq_of_isInvertedBy _ hF)) (by
      rintro K L ⟨f⟩ hf
      exact hF _ (by simpa [hW] using hf))
  fac F hF := by rw [Functor.assoc, univ.fac, Quotient.lift_spec]
  uniq F₁ F₂ h := univ.uniq _ _ (Quotient.lift_unique' _ _ _ h)

variable (E) in
/-- If `homRel : HomRel C` satisfies `homRel.FactorsThroughLocalization W` and
that the class of morphisms `W` induces a class of morphism `W'` on the quotient category,
then `Quotient.functor homRel ⋙ W'.Q` satisfies the universal property of the
localization. This is used in `HomRel.FactorsThroughLocalization.isLocalizedEquivalence`
in order to show that as a localizer morphism, the quotient functor induces an
equivalence on localized categories. -/
noncomputable def strictUniversalPropertyFixedTarget' :
    StrictUniversalPropertyFixedTarget
      (Quotient.functor homRel ⋙ W'.Q) W E :=
  strictUniversalPropertyFixedTarget h hW _ (strictUniversalPropertyFixedTargetQ W' E)

end

include h in
/-- If `homRel : HomRel C` satisfies `homRel.FactorsThroughLocalization W` and
that the class of morphisms `W` induces a class of morphism `W'` on the quotient category,
then the localizer morphism given by the functor `Quotient.functor HomRel : C ⥤ Quotient homRel`
induces equivalences on localized categories. -/
lemma isLocalizedEquivalence :
    (LocalizerMorphism.ofEq hW).IsLocalizedEquivalence :=
  have : ((LocalizerMorphism.ofEq hW).functor ⋙ W'.Q).IsLocalization W :=
    Functor.IsLocalization.mk' _ _
      (h.strictUniversalPropertyFixedTarget' hW _)
      (h.strictUniversalPropertyFixedTarget' hW _)
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ W'.Q

end FactorsThroughLocalization

end HomRel
