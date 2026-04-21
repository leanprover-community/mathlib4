/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category structure on homological complexes

Let `c : ComplexShape I` with `I` an additive monoid. If `c` is equipped
with the data and axioms `c.TensorSigns`, then the category
`HomologicalComplex C c` can be equipped with a monoidal category
structure if `C` is a monoidal category such that `C` has certain
coproducts and both left/right tensoring commute with these.

In particular, we obtain a monoidal category structure on
`ChainComplex C ℕ` when `C` is an additive monoidal category.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

/-- If `K₁` and `K₂` are two homological complexes, this is the property that
for all `j`, the coproduct of `K₁ i₁ ⊗ K₂ i₂` for `i₁ + i₂ = j` exists. -/
abbrev HasTensor (K₁ K₂ : HomologicalComplex C c) := HasMapBifunctor K₁ K₂ (curriedTensor C) c

section

variable [DecidableEq I]

/-- The tensor product of two homological complexes. -/
noncomputable abbrev tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] :
    HomologicalComplex C c :=
  mapBifunctor K₁ K₂ (curriedTensor C) c

/-- The inclusion `K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j` of a summand in
the tensor product of the homological complexes. -/
noncomputable abbrev ιTensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j :=
  ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

/-- The tensor product of two morphisms of homological complexes. -/
noncomputable abbrev tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂ :=
  mapBifunctorMap f g _ _

/-- Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `- ⊗ K₃.X i₃` commutes with the coproduct of
the `K₁.X i₁ ⊗ K₂.X i₂` such that `i₁ + i₂ = j`. -/
abbrev HasGoodTensor₁₂ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

/-- Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `K₁.X i₁` commutes with the coproduct of
the `K₂.X i₂ ⊗ K₃.X i₃` such that `i₂ + i₃ = j`. -/
abbrev HasGoodTensor₂₃ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

/-- The associator isomorphism for the tensor product of homological complexes. -/
noncomputable abbrev associator (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] :
    tensorObj (tensorObj K₁ K₂) K₃ ≅ tensorObj K₁ (tensorObj K₂ K₃) :=
  mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

variable (C c) in
/-- The unit of the tensor product of homological complexes. -/
noncomputable abbrev tensorUnit : HomologicalComplex C c := (single C c 0).obj (𝟙_ C)

variable (C c) in
/-- As a graded object, the single complex `(single C c 0).obj (𝟙_ C)` identifies
to the unit `(GradedObject.single₀ I).obj (𝟙_ C)` of the tensor product of graded objects. -/
noncomputable def tensorUnitIso :
    (GradedObject.single₀ I).obj (𝟙_ C) ≅ (tensorUnit C c).X :=
  GradedObject.isoMk _ _ (fun i ↦
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

end

instance (K₁ K₂ : HomologicalComplex C c) [GradedObject.HasTensor K₁.X K₂.X] :
    HasTensor K₁ K₂ := by
  assumption

instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X] :
    HasGoodTensor₁₂ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X)

instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X] :
    HasGoodTensor₂₃ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X)

section

variable (K : HomologicalComplex C c) [DecidableEq I]

section

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

instance : GradedObject.HasTensor (tensorUnit C c).X K.X :=
  GradedObject.hasTensor_of_iso (tensorUnitIso C c) (Iso.refl _)

instance : HasTensor (tensorUnit C c) K :=
  inferInstanceAs (GradedObject.HasTensor (tensorUnit C c).X K.X)

@[simp]
lemma unit_tensor_d₁ (i₁ i₂ j : I) :
    mapBifunctor.d₁ (tensorUnit C c) K (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

end

section

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

instance : GradedObject.HasTensor K.X (tensorUnit C c).X :=
  GradedObject.hasTensor_of_iso (Iso.refl _) (tensorUnitIso C c)

instance : HasTensor K (tensorUnit C c) :=
  inferInstanceAs (GradedObject.HasTensor K.X (tensorUnit C c).X)

@[simp]
lemma tensor_unit_d₂ (i₁ i₂ j : I) :
    mapBifunctor.d₂ K (tensorUnit C c) (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

end

end

section Unitor

variable (K : HomologicalComplex C c) [DecidableEq I]

section LeftUnitor

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- Auxiliary definition for `leftUnitor`. -/
noncomputable def leftUnitor' :
    (tensorObj (tensorUnit C c) K).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso ((tensorUnitIso C c).symm) (Iso.refl _) ≪≫
    GradedObject.Monoidal.leftUnitor K.X

set_option backward.isDefEq.respectTransparency false in
lemma leftUnitor'_inv (i : I) :
    (leftUnitor' K).inv i = (λ_ (K.X i)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ (K.X i)) ≫
      ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) := by
  dsimp [leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id, ← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma leftUnitor'_inv_comm (i j : I) :
    (leftUnitor' K).inv i ≫ (tensorObj (tensorUnit C c) K).d i j =
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

/-- The left unitor for the tensor product of homological complexes. -/
noncomputable def leftUnitor :
    tensorObj (tensorUnit C c) K ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ ↦ leftUnitor'_inv_comm _ _ _))

end LeftUnitor

section RightUnitor

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

/-- Auxiliary definition for `rightUnitor`. -/
noncomputable def rightUnitor' :
    (tensorObj K (tensorUnit C c)).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso (Iso.refl _) ((tensorUnitIso C c).symm) ≪≫
    GradedObject.Monoidal.rightUnitor K.X

set_option backward.isDefEq.respectTransparency false in
lemma rightUnitor'_inv (i : I) :
    (rightUnitor' K).inv i = (ρ_ (K.X i)).inv ≫ ((K.X i) ◁ (singleObjXSelf c 0 (𝟙_ C)).inv) ≫
      ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) := by
  dsimp [rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom, ← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma rightUnitor'_inv_comm (i j : I) :
    (rightUnitor' K).inv i ≫ (tensorObj K (tensorUnit C c)).d i j =
      K.d i j ≫ (rightUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

/-- The right unitor for the tensor product of homological complexes. -/
noncomputable def rightUnitor :
    tensorObj K (tensorUnit C c) ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ ↦ rightUnitor'_inv_comm _ _ _))

end RightUnitor

end Unitor

variable (C c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I]

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (HomologicalComplex C c) where
  tensorObj K₁ K₂ := tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := tensorUnit C c
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

set_option backward.isDefEq.respectTransparency false in
/-- The structure which allows to construct the monoidal category structure
on `HomologicalComplex C c` from the monoidal category structure on
graded objects. -/
noncomputable def Monoidal.inducingFunctorData :
    Monoidal.InducingFunctorData (forget C c) where
  μIso _ _ := Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight,
      id_comp, Iso.inv_hom_id, comp_id, assoc]
    erw [id_whiskerRight]
    rw [id_comp]
    erw [id_comp]
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

noncomputable instance monoidalCategory : MonoidalCategory (HomologicalComplex C c) :=
  Monoidal.induced _ (Monoidal.inducingFunctorData C c)

noncomputable example {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D]
    [HasZeroObject D] [HasFiniteCoproducts D] [((curriedTensor D).Additive)]
    [∀ (X : D), (((curriedTensor D).obj X).Additive)]
    [∀ (X : D), PreservesFiniteCoproducts ((curriedTensor D).obj X)]
    [∀ (X : D), PreservesFiniteCoproducts ((curriedTensor D).flip.obj X)] :
    MonoidalCategory (ChainComplex D ℕ) := inferInstance

end HomologicalComplex
