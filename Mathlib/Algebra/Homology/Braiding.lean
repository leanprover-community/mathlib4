import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.CategoryTheory.Monoidal.Braided

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory

namespace MonoidalCategory

variable (C : Type*) [Category C] [MonoidalCategory C] [BraidedCategory C]

@[simps!]
def curriedBraidingNatIso :
    (curryObj (MonoidalCategory.tensor C)) ≅
      (curryObj (MonoidalCategory.tensor C)).flip :=
  NatIso.ofComponents (fun K => NatIso.ofComponents (fun L => β_ K L) (by aesop_cat)) (by aesop_cat)

end MonoidalCategory

end CategoryTheory

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

instance [∀ (X₁ : C₁), (F.obj X₁).Additive] : F.flip.Additive where
instance [F.Additive] (X₂ : C₂) : ((F.flip).obj X₂).Additive where

end CategoryTheory.Functor

namespace HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] {c : ComplexShape I} [DecidableEq I]
  (s : c.TensorSigns)

variable [(curryObj (MonoidalCategory.tensor C)).Additive]
  (K L : HomologicalComplex C c)

def tensorBicomplex :
      HomologicalComplex₂ C c c :=
    (((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).obj K).obj L)

instance [h : HasTensor K L] :
    GradedObject.HasMap (tensorBicomplex K L).toGradedObject s.totalComplexShape.π := h

noncomputable def tensorBiComplexTotalIso [HasTensor K L] [HasTensor L K] :
    Monoidal.tensorObj s K L ≅ (tensorBicomplex K L).total s.totalComplexShape := Iso.refl _

variable [BraidedCategory C]

@[simps!]
def tensorBicomplexFlipIso : tensorBicomplex K L ≅ (tensorBicomplex L K).flip :=
  ((Functor.mapHomologicalComplex₂FlipIso (curryObj (MonoidalCategory.tensor C)) c c).app K).app L ≪≫
    (HomologicalComplex₂.flipFunctor C c c).mapIso (((NatIso.mapHomologicalComplex₂ (curriedBraidingNatIso C).symm c c).app L).app K)

@[simps!]
def tensorBicomplexFlipNatIso :
    (Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c) ≅
      (Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).flip ⋙
        (whiskeringRight _ _ _).obj (HomologicalComplex₂.flipFunctor C c c) :=
  NatIso.ofComponents (fun K => NatIso.ofComponents (fun L => tensorBicomplexFlipIso K L) (by
    intro L L' φ
    dsimp [tensorBicomplexFlipIso]
    simp only [NatTrans.naturality_assoc, Functor.comp_map, Functor.flip_obj_map, assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, NatTrans.naturality])) (by
    intro K K' φ
    ext L : 2
    dsimp [tensorBicomplexFlipIso]
    rw [assoc, ← NatTrans.comp_app_assoc, NatTrans.naturality]
    dsimp
    rw [assoc, ← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality])

structure _root_.ComplexShape.TensorSigns.Braiding where
  σ : TotalComplexShapeSymmetry s.totalComplexShape s.totalComplexShape
  symm (i₁ i₂ : I) : σ.ε i₁ i₂ = σ.ε i₂ i₁ -- this should be necessary for the hexagon relation?

variable {s} (β : s.Braiding) [h₁ : HasTensor K L] [h₂ : HasTensor L K]

instance : (tensorBicomplex K L).flip.toGradedObject.HasMap s.totalComplexShape.π := by
  refine' @GradedObject.hasMap_of_iso (I × I) I C _ _ _ _ _ h₂
  exact GradedObject.isoMk _ _ (fun ⟨i₁, i₂⟩ => β_ (K.X i₂) (L.X i₁))

namespace Monoidal

noncomputable def braiding : Monoidal.tensorObj s K L ≅ Monoidal.tensorObj s L K :=
  HomologicalComplex₂.totalSymmIso β.σ (tensorBicomplex K L) ≪≫
    HomologicalComplex₂.totalMapIso (tensorBicomplexFlipIso L K).symm s.totalComplexShape

/-lemma ιTensorObj_braiding_hom (i₁ i₂ i₃ : I) (h : i₁ + i₂ = i₃) :
  ιTensorObj s K L i₁ i₂ i₃ h ≫ (braiding K L β).hom.f i₃ =
    (β_ (K.X i₁) (L.X i₂)).hom ≫ ιTensorObj s L K i₂ i₁ i₃ (by rw [add_comm, h]) :=
  -- with this definition of braiding, we may get `(β_ (L.X i₂) (K.X i₁)).inv` instead
  -- of `(β_ (K.X i₁) (L.X i₂)).hom` in which case the definition should be fixed...
  sorry-/

variable (X Y Z : HomologicalComplex C c)
  [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
  [HasTensor Y X] [HasTensor Z Y] [HasTensor X Z]
  [HasTensor (tensorObj s X Y) Z] [HasTensor X (tensorObj s Y Z)]
  [HasTensor (tensorObj s Y Z) X] [HasTensor Y (tensorObj s Z X)]
  [HasTensor (tensorObj s Y X) Z] [HasTensor Y (tensorObj s X Z)]
  [HasTensor (tensorObj s Z X) Y] [HasTensor Z (tensorObj s X Y)]
  [HasTensor (tensorObj s X Z) Y] [HasTensor X (tensorObj s Z Y)]
  [GradedObject.HasGoodTensor₁₂Tensor X.X Y.X Z.X]
  [GradedObject.HasGoodTensorTensor₂₃ X.X Y.X Z.X]
  [GradedObject.HasGoodTensor₁₂Tensor Y.X Z.X X.X]
  [GradedObject.HasGoodTensorTensor₂₃ Y.X Z.X X.X]
  [GradedObject.HasGoodTensor₁₂Tensor Y.X X.X Z.X]
  [GradedObject.HasGoodTensorTensor₂₃ Y.X X.X Z.X]
  [GradedObject.HasGoodTensor₁₂Tensor Z.X X.X Y.X]
  [GradedObject.HasGoodTensorTensor₂₃ Z.X X.X Y.X]
  [GradedObject.HasGoodTensor₁₂Tensor X.X Z.X Y.X]
  [GradedObject.HasGoodTensorTensor₂₃ X.X Z.X Y.X]

/-lemma hexagon_forward :
  (associator s X Y Z).hom ≫ (braiding X (tensorObj s Y Z) β).hom ≫ (associator s Y Z X).hom =
    tensorHom s (braiding X Y β).hom (𝟙 Z) ≫ (associator s Y X Z).hom ≫ tensorHom s (𝟙 Y) (braiding X Z β).hom := by
  ext n x y z h
  dsimp
  sorry

lemma hexagon_reverse : (associator s X Y Z).inv ≫ (braiding (tensorObj s X Y) Z β).hom ≫ (associator s Z X Y).inv =
    tensorHom s (𝟙 X) (braiding Y Z β).hom ≫ (associator s X Z Y).inv ≫ tensorHom s (braiding X Z β).hom (𝟙 Y) := by
  sorry-/

end Monoidal

end HomologicalComplex
