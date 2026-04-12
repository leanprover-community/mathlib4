/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.CochainComplexMinus
public import Mathlib.Algebra.Homology.Embedding.CochainComplexTrunc
public import Mathlib.Algebra.Homology.PreservesQuasiIso
public import Mathlib.Algebra.Homology.ObjectProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Resolutions of unbounded complexes

-/

@[expose] public section

open CategoryTheory Limits Functor

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A]
  [HasColimitsOfShape ℤ A]
  (L : Minus A ⥤ CochainComplex A ℤ)

noncomputable def leftResolution : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  filtrationLEMinusFunctor A ⋙ (whiskeringRight _ _ _).obj L ⋙ colim

noncomputable def objectPropertyColimitOfShapeLeftResolutionObj
    (P : ObjectProperty (CochainComplex A ℤ)) (hP : L.essImage ≤ P)
    (K : CochainComplex A ℤ) :
    P.ColimitOfShape ℤ ((leftResolution L).obj K) where
  toColimitPresentation := .colimit _
  prop_diag_obj _ := hP _ (L.obj_mem_essImage _)

lemma objectPropertyColimitOfShape_leftResolution_obj
    (P : ObjectProperty (CochainComplex A ℤ)) (hP : L.essImage ≤ P)
    (K : CochainComplex A ℤ) :
    P.colimitsOfShape ℤ ((leftResolution L).obj K) :=
  ⟨objectPropertyColimitOfShapeLeftResolutionObj L P hP K⟩

variable {L} (α : L ⟶ Minus.ι _)

noncomputable def leftResolutionπ :
    leftResolution L ⟶ 𝟭 _ :=
  whiskerLeft _ (whiskerRight ((whiskeringRight _ _ _).map α) _) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (filtrationLEMinusFunctorCompWhiskeringRightObjιIso A).hom _ ≫
    (filtrationLEFunctorCompColimIso A).hom

set_option backward.isDefEq.respectTransparency false in
instance quasiIso_leftResolutionπ_app [HasExactColimitsOfShape ℤ A]
    [∀ K, QuasiIso (α.app K)] (K : CochainComplex A ℤ) :
    QuasiIso ((leftResolutionπ α).app K) := by
  let φ := colimMap (((whiskeringRight _ _ _).map α).app K.filtrationLEMinus)
  have : QuasiIso φ := (HomologicalComplex.quasiIso A (.up ℤ)).colimMap _ (fun n ↦ by
    dsimp
    simp only [HomologicalComplex.mem_quasiIso_iff]
    infer_instance)
  dsimp only [leftResolutionπ]
  change QuasiIso (φ ≫ _)
  infer_instance

end CochainComplex

namespace CategoryTheory

open CochainComplex

namespace Abelian

namespace LeftResolution

variable {A C : Type*} [Category C] [Category A]
  [Preadditive C] [HasZeroObject C] [Abelian A] {ι : C ⥤ A}
  [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
  [HasFiniteCoproducts C] [HasColimitsOfShape ℤ A]

noncomputable def resolutionFunctor : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  CochainComplex.leftResolution (Λ.minusResolutionFunctor ⋙
    ι.mapCochainComplexMinus ⋙ Minus.ι A)

noncomputable def resolutionNatTrans : Λ.resolutionFunctor ⟶ 𝟭 _ :=
  CochainComplex.leftResolutionπ
    (whiskerRight Λ.minusResolutionNatTrans (Minus.ι A))

set_option backward.isDefEq.respectTransparency false in
instance quasiIso_resolutionNatTrans_app
    [HasExactColimitsOfShape ℤ A] (K : CochainComplex A ℤ) :
    QuasiIso (Λ.resolutionNatTrans.app K) := by
  dsimp [resolutionNatTrans]
  infer_instance

noncomputable def colimitOfShapeResolutionFunctorObj (K : CochainComplex A ℤ) :
    ι.essImage.cochainComplexMinus.ColimitOfShape ℤ (Λ.resolutionFunctor.obj K) :=
  objectPropertyColimitOfShapeLeftResolutionObj _ _ (by
    rintro M ⟨X, ⟨e⟩⟩
    rw [← ι.essImage.cochainComplexMinus.prop_iff_of_iso e]
    exact ⟨fun _ ↦ Functor.obj_mem_essImage _ _, ObjectProperty.prop_ι_obj _ _⟩) K

end LeftResolution

end Abelian

end CategoryTheory
