import Mathlib.Algebra.Homology.BifunctorAssociator
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.Monoidal.Transport

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]

abbrev HasTensor (K₁ K₂ : HomologicalComplex C c) := HasMapBifunctor K₁ K₂ (curriedTensor C) c

noncomputable abbrev tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] :
    HomologicalComplex C c :=
  mapBifunctor K₁ K₂ (curriedTensor C) c

noncomputable abbrev ιTensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j :=
  ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

noncomputable abbrev tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂ :=
  mapBifunctorMap f g _ _

abbrev HasGoodTensor₁₂ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

abbrev HasGoodTensor₂₃ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

noncomputable abbrev associator (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] :
    tensorObj (tensorObj K₁ K₂) K₃ ≅ tensorObj K₁ (tensorObj K₂ K₃) :=
  mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

variable (C c) in
noncomputable def tensorUnitIso :
    (GradedObject.single₀ I).obj (𝟙_ C) ≅ (forget C c).obj ((single C c 0).obj (𝟙_ C)) :=
  GradedObject.isoMk _ _ (fun i ↦
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

variable
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

instance (K₁ K₂ : HomologicalComplex C c) : HasTensor K₁ K₂ :=
  inferInstanceAs (GradedObject.HasTensor K₁.X K₂.X)

instance (K₁ K₂ K₃ : HomologicalComplex C c) : HasGoodTensor₁₂ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X)

instance (K₁ K₂ K₃ : HomologicalComplex C c) : HasGoodTensor₂₃ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X)

section Unitor

variable (K : HomologicalComplex C c)

noncomputable def leftUnitor' :
    (forget C c).obj (tensorObj ((single C c 0).obj (𝟙_ C)) K) ≅ K.X :=
  ((curriedTensor _).mapIso (tensorUnitIso C c).symm).app K.X ≪≫
    MonoidalCategoryStruct.leftUnitor (C := GradedObject I C) K.X

lemma leftUnitor'_inv (i : I) :
    (leftUnitor' K).inv i = (λ_ (K.X i)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ (K.X i)) ≫
      ιTensorObj ((single C c 0).obj (𝟙_ C)) K 0 i i (zero_add i) := by
  sorry

@[simp]
lemma unit_tensor_d₁ (i₁ i₂ j : I) :
    mapBifunctor.d₁ ((single C c 0).obj (𝟙_ C)) K (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

@[simp]
lemma tensor_unit_d₂ (i₁ i₂ j : I) :
    mapBifunctor.d₂ K ((single C c 0).obj (𝟙_ C)) (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

@[reassoc]
lemma leftUnitor'_inv_comm (i j : I) :
    (leftUnitor' K).inv i ≫ (tensorObj ((single C c 0).obj (𝟙_ C)) K).d i j =
      K.d i j ≫ (leftUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

noncomputable def leftUnitor :
    tensorObj ((single C c 0).obj (𝟙_ C)) K ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ ↦ leftUnitor'_inv_comm _ _ _))

noncomputable def rightUnitor' :
    (forget C c).obj (tensorObj K ((single C c 0).obj (𝟙_ C))) ≅ K.X :=
  ((curriedTensor (GradedObject I C)).obj K.X).mapIso (tensorUnitIso C c).symm ≪≫
    MonoidalCategoryStruct.rightUnitor (C := GradedObject I C) K.X

lemma rightUnitor'_inv_comm (i j : I) :
    (rightUnitor' K).inv i ≫ (tensorObj K ((single C c 0).obj (𝟙_ C))).d i j =
      K.d i j ≫ (rightUnitor' K).inv j :=
  sorry

noncomputable def rightUnitor :
    tensorObj K ((single C c 0).obj (𝟙_ C)) ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ ↦ rightUnitor'_inv_comm _ _ _))

end Unitor

variable (C c)

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (HomologicalComplex C c) where
  tensorObj K₁ K₂ := tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := (single C c 0).obj (𝟙_ C)
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

noncomputable def Monoidal.inducingFunctorData :
    Monoidal.InducingFunctorData (forget C c) where
  μIso _ _ := Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    erw [comp_id, id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    erw [comp_id, id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    erw [comp_id, id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight, id_comp, Iso.inv_hom_id, comp_id,
      assoc]
    erw [id_whiskerRight, id_comp, id_comp]
    rfl
  leftUnitor_eq K := by
    dsimp
    erw [id_comp]
    rfl
  rightUnitor_eq K := by
    dsimp
    rw [assoc]
    erw [id_comp]
    rfl

noncomputable instance : MonoidalCategory (HomologicalComplex C c) :=
  Monoidal.induced _ (Monoidal.inducingFunctorData C c)

end HomologicalComplex
