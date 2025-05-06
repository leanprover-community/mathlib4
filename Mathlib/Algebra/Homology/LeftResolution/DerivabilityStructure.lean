/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolution.Basic
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.Algebra.Homology.DerivedCategory.Minus

/-!
# Derivability structure from a left resolution

-/

-- part of this should be refactored and moved to `LeftResolutions.*`

/-universe v u
open CategoryTheory Category Limits

namespace CategoryTheory

/-- isIso_of_isIso_app' -/
lemma NatIso.isIso_of_isIso_app' {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) (hα : ∀ X, IsIso (α.app X)) : IsIso α := by
  apply NatIso.isIso_of_isIso_app

end CategoryTheory

namespace CochainComplex

variable {C A : Type*} [Category C] [Abelian C] [Category A] [Preadditive A]
  [HasZeroObject A] [HasFiniteCoproducts A]
  (ι : A ⥤ C) [ι.Full] [ι.Faithful] [ι.PreservesZeroMorphisms] [ι.Additive]

namespace LeftResolutions

abbrev quasiIso : MorphismProperty (CochainComplex.Minus A) :=
  CochainComplex.Minus.quasiIso.inverseImage ι.mapCochainComplexMinus

@[simps]
def localizerMorphism :
    LocalizerMorphism (quasiIso ι) (CochainComplex.Minus.quasiIso (C := C)) where
  functor := ι.mapCochainComplexMinus
  map _ _ _ hf := hf

variable {ι}
variable (Λ : LeftResolutions ι) [Λ.F.PreservesZeroMorphisms]

instance : ι.mapCochainComplexMinus.Full :=
  Functor.Full.of_comp_faithful_iso ι.mapCochainComplexMinusCompι

instance : ι.mapCochainComplexMinus.Faithful :=
  Functor.Faithful.of_comp_iso ι.mapCochainComplexMinusCompι

include Λ in
lemma localizerMorphism_isLocalizedEquivalence :
    (localizerMorphism ι).IsLocalizedEquivalence := by
  let W₁ := quasiIso ι
  let W₂ := CochainComplex.Minus.quasiIso (C := C)
  let L₁ := W₁.Q
  let L₂ := W₂.Q
  let G := (localizerMorphism ι).localizedFunctor L₁ L₂
  let eG := Localization.Lifting.iso L₁ W₁ ((localizerMorphism ι).functor ⋙ L₂) G
  let F : CochainComplex.Minus C ⥤ (quasiIso ι).Localization :=
    Λ.resolutionFunctor ⋙ (quasiIso ι).Q
  have hF : CochainComplex.Minus.quasiIso.IsInvertedBy F := fun K L f hf =>
    Localization.inverts L₁ W₁ _ (Λ.quasiIso_resolutionFunctor_map _ hf)
  let F' := Localization.lift F hF L₂
  let L₂F' : L₂ ⋙ F' ≅ F := Localization.fac _ _ _
  have : IsIso (whiskerRight Λ.resolutionNatTrans L₂) :=
    NatIso.isIso_of_isIso_app' _ (fun K =>
      Localization.inverts L₂ W₂ _ (Λ.quasiIso_resolutionNatTrans_app K))
  let η : F' ⋙ G ≅ 𝟭 _ := Localization.liftNatIso L₂ W₂ (L₂ ⋙ F' ⋙ G) L₂ _ _
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight L₂F' _ ≪≫
      (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ eG ≪≫
      (Functor.associator _ _ _).symm ≪≫ asIso (whiskerRight Λ.resolutionNatTrans L₂) ≪≫
      L₂.leftUnitor))
  let α : (localizerMorphism ι).functor ⋙ Λ.resolutionFunctor ⟶ 𝟭 _ :=
    ((Functor.FullyFaithful.ofFullyFaithful
      ι.mapCochainComplexMinus).whiskeringRight _).preimage
        ((Functor.associator _ _ _).hom ≫
      whiskerLeft _ Λ.resolutionNatTrans ≫ (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
  have : IsIso (whiskerRight α L₁) := NatIso.isIso_of_isIso_app' _ (fun K => by
    apply Localization.inverts L₁ W₁
    dsimp [W₁, quasiIso, MorphismProperty.inverseImage]
    dsimp [α]
    simp only [comp_id, id_comp]
    erw [Functor.map_preimage]
    apply quasiIso_resolutionNatTrans_app)
  let ε : 𝟭 _ ≅ G ⋙ F' := Localization.liftNatIso L₁ W₁ L₁ (L₁ ⋙ G ⋙ F') _ _
    (L₁.leftUnitor.symm ≪≫ (asIso (whiskerRight α L₁)).symm ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ L₂F'.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      Functor.associator _ _ _)
  let e : (quasiIso ι).Localization ≌ (CochainComplex.Minus.quasiIso (C := C)).Localization :=
    CategoryTheory.Equivalence.mk G F' ε η
  have : G.IsEquivalence := inferInstanceAs e.functor.IsEquivalence
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' _ L₁ L₂ G

end LeftResolutions

end CochainComplex-/
