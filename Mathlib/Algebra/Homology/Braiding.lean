import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.CategoryTheory.Monoidal.Braided

open CategoryTheory Category Limits MonoidalCategory Preadditive MonoidalPreadditive

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

variable [(curryObj (MonoidalCategory.tensor C)).Additive]
  (K L : HomologicalComplex C c)

def tensorBicomplex :
      HomologicalComplex₂ C c c :=
    (((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).obj K).obj L)

section

variable [ComplexShape.TensorSigns c]

instance [h : HasTensor K L] :
    GradedObject.HasMap (tensorBicomplex K L).toGradedObject (ComplexShape.π c c c) := h

noncomputable def tensorBiComplexTotalIso [HasTensor K L] [HasTensor L K] :
    Monoidal.tensorObj K L ≅ (tensorBicomplex K L).total c := Iso.refl _

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

end

variable (c)

class _root_.ComplexShape.Braiding  extends c.TensorSigns,
    TotalComplexShapeSymmetry c c c where
  σ_add₁ (i₁ i₁' i₂ : I) : ComplexShape.σ c c c (i₁ + i₁') i₂ = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁' i₂
  σ_add₂ (i₁ i₂ i₂' : I) : ComplexShape.σ c c c i₁ (i₂ + i₂') = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁ i₂'

lemma _root_.ComplexShape.σ_add₁ (i₁ i₁' i₂ : I) [c.Braiding] :
  ComplexShape.σ c c c (i₁ + i₁') i₂ = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁' i₂ := by
  apply ComplexShape.Braiding.σ_add₁

lemma _root_.ComplexShape.σ_add₂ (i₁ i₂ i₂' : I) [c.Braiding] :
  ComplexShape.σ c c c i₁ (i₂ + i₂') = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁ i₂' := by
  apply ComplexShape.Braiding.σ_add₂

@[simps]
instance : TotalComplexShapeSymmetry (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  symm := fun p q => add_comm q p
  σ := fun p q => (p * q).negOnePow
  σ_mul_self := by aesop
  compatibility₁ := by
    rintro p _ rfl q
    dsimp
    rw [one_mul, ← Int.negOnePow_add, add_mul, one_mul]
  compatibility₂ := by
    rintro p q _ rfl
    dsimp
    rw [mul_one, add_comm q 1, mul_add, mul_one, Int.negOnePow_add, ← mul_assoc, Int.negOnePow_mul_self, one_mul]

instance : (ComplexShape.up ℤ).Braiding where
  σ_add₁ p p' q := by
    dsimp
    rw [← Int.negOnePow_add, add_mul]
  σ_add₂ p q q' := by
    dsimp
    rw [← Int.negOnePow_add, mul_add]

variable [c.Braiding] [BraidedCategory C]

variable {c}
variable [HasTensor K L] [HasTensor L K]

instance : (tensorBicomplex K L).flip.toGradedObject.HasMap (ComplexShape.π c c c) := by
  refine' @GradedObject.hasMap_of_iso (I × I) I C _ _ _ _ _ (inferInstance : HasTensor L K)
  exact GradedObject.isoMk _ _ (fun ⟨i₁, i₂⟩ => β_ (K.X i₂) (L.X i₁))

namespace Monoidal

open BraidedCategory


noncomputable def braiding : Monoidal.tensorObj K L ≅ Monoidal.tensorObj L K :=
  HomologicalComplex₂.totalSymmIso c (tensorBicomplex K L) ≪≫
    HomologicalComplex₂.totalMapIso (tensorBicomplexFlipIso L K).symm c

@[reassoc (attr := simp)]
lemma ιTensorObj_braiding_hom (i₁ i₂ i₃ : I) (h : i₁ + i₂ = i₃) :
  ιTensorObj K L i₁ i₂ i₃ h ≫ (braiding K L).hom.f i₃ =
    ComplexShape.σ c c c i₁ i₂ • (β_ (K.X i₁) (L.X i₂)).hom ≫ ιTensorObj L K i₂ i₁ i₃ (by rw [add_comm, h]) := by
  -- with this definition of braiding, we may get `(β_ (L.X i₂) (K.X i₁)).inv` instead
  -- of `(β_ (K.X i₁) (L.X i₂)).hom` in which case the definition should be fixed...
  sorry

variable (X Y Z : HomologicalComplex C c)
  [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
  [HasTensor Y X] [HasTensor Z Y] [HasTensor X Z]
  [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
  [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)]
  [HasTensor (tensorObj Y X) Z] [HasTensor Y (tensorObj X Z)]
  [HasTensor (tensorObj Z X) Y] [HasTensor Z (tensorObj X Y)]
  [HasTensor (tensorObj X Z) Y] [HasTensor X (tensorObj Z Y)]
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

lemma hexagon_forward :
  (associator X Y Z).hom ≫ (braiding X (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
    tensorHom (braiding X Y).hom (𝟙 Z) ≫ (associator Y X Z).hom ≫
      tensorHom (𝟙 Y) (braiding X Z).hom := by
  ext n x y z h
  dsimp
  rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq _ _ _ _ _ _ _ _ _ rfl, assoc,
    ιTensorObj_braiding_hom_assoc, zsmul_comp, comp_zsmul, comp_zsmul, assoc, braiding_naturality_assoc,
    ← ιTensorObj₃'_eq_assoc _ _ _ _ _ _ _ (by rw [← h]; abel), ιTensorObj₃'_associator_hom,
    hexagon_forward_assoc]
  rw [ιTensorObj₃'_eq _ _ _ _ _ _ _ _ _ rfl, assoc, ι_tensorHom_assoc, id_f,
    ← comp_tensor_id_assoc, ιTensorObj_braiding_hom, zsmul_tensor, zsmul_comp,
    comp_tensor_id, assoc,
    ← ιTensorObj₃'_eq_assoc _ _ _ _ _ _ _ (by rw [← h]; abel),
    ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq Y X Z _ _ _ _ _ _ rfl, assoc,
    ι_tensorHom, id_f, ← id_tensor_comp_assoc, ιTensorObj_braiding_hom, tensor_zsmul,
    zsmul_comp, comp_zsmul, comp_zsmul, id_tensor_comp, assoc,
    ← ιTensorObj₃_eq _ _ _ _ _ _ _ _ _ (add_comm z x), smul_smul, c.σ_add₂]

lemma hexagon_reverse :
    (associator X Y Z).inv ≫ (braiding (tensorObj X Y) Z).hom ≫ (associator Z X Y).inv =
      tensorHom (𝟙 X) (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
        tensorHom (braiding X Z).hom (𝟙 Y) := by
  ext n x y z h
  dsimp
  rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq _ _ _ _ _ _ _ _ _ rfl, assoc,
    ιTensorObj_braiding_hom_assoc, zsmul_comp, comp_zsmul, comp_zsmul, assoc, braiding_naturality_assoc,
    ← ιTensorObj₃_eq_assoc _ _ _ _ _ _ _ (by rw [← h]; abel), ιTensorObj₃_associator_inv,
    hexagon_reverse_assoc]
  rw [ιTensorObj₃_eq _ _ _ _ _ _ _ _ _ rfl, assoc, ι_tensorHom_assoc, id_f,
    ← id_tensor_comp_assoc, ιTensorObj_braiding_hom, tensor_zsmul, zsmul_comp,
    id_tensor_comp, assoc,
    ← ιTensorObj₃_eq_assoc _ _ _ _ _ _ _ (by rw [← h]; abel),
    ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Z Y _ _ _ _ _ _ rfl, assoc,
    ι_tensorHom, id_f, ← comp_tensor_id_assoc, ιTensorObj_braiding_hom, zsmul_tensor,
    zsmul_comp, comp_zsmul, comp_zsmul, comp_tensor_id, assoc,
    ← ιTensorObj₃'_eq _ _ _ _ _ _ _ (by rw [← h]; abel) _ (add_comm z x), smul_smul, c.σ_add₁,
    mul_comm]

end Monoidal

end HomologicalComplex
