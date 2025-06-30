/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Quotient

/-!
# Localization of quotient categories

-/

open CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  (homRel : HomRel C)

namespace CategoryTheory

namespace HomRel

def FactorsThroughLocalization (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g → AreEqualizedByLocalization W f g

variable {homRel} {W : MorphismProperty C}
  (h : FactorsThroughLocalization homRel W)
  {W' : MorphismProperty (Quotient homRel)}
  (hW : W = W'.inverseImage (Quotient.functor homRel))

namespace FactorsThroughLocalization

open Localization

@[simps]
def localizerMorphism : LocalizerMorphism W W' where
  functor := Quotient.functor _
  map := by rw [hW]

section

variable {E : Type*} [Category E]

def strictUniversalPropertyFixedTarget (L' : Quotient homRel ⥤ D)
  (univ : StrictUniversalPropertyFixedTarget L' W' E):
    StrictUniversalPropertyFixedTarget
      (Quotient.functor homRel ⋙ L') W E where
  inverts _ _ _ hf := univ.inverts _ (by rwa [hW] at hf)
  lift F hF :=
    univ.lift (Quotient.lift _ F (fun _ _ f g hfg ↦ (h hfg).map_eq_of_inverts _ hF)) (by
      intro K L f hf
      induction f using Quotient.induction with
      | h f => exact hF _ (by simpa [hW] using hf))
  fac F hF := by
    rw [Functor.assoc, univ.fac]
    rfl
  uniq F₁ F₂ h := by
    apply univ.uniq
    exact Quotient.lift_unique' _ _ _ h

variable (E) in
noncomputable def strictUniversalPropertyFixedTarget' :
    StrictUniversalPropertyFixedTarget
      (Quotient.functor homRel ⋙ W'.Q) W E :=
  strictUniversalPropertyFixedTarget h hW _
    (strictUniversalPropertyFixedTargetQ W' E)

end

include h in
lemma isLocalizedEquivalence :
    (localizerMorphism hW).IsLocalizedEquivalence := by
  have : ((localizerMorphism hW).functor ⋙ W'.Q).IsLocalization W :=
    Functor.IsLocalization.mk' _ _
      (h.strictUniversalPropertyFixedTarget' hW _)
      (h.strictUniversalPropertyFixedTarget' hW _)
  apply LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    (localizerMorphism hW) (W'.Q)

end FactorsThroughLocalization

end HomRel

end CategoryTheory
