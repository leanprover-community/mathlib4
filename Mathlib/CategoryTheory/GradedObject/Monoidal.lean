import Mathlib.CategoryTheory.GradedObject.Trifunctor

namespace CategoryTheory

variable {I : Type*} [AddMonoid I] {C : Type*} [Category C] [MonoidalCategory C]

namespace MonoidalCategory

variable (C)

@[simps!]
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curryObj (MonoidalCategory.tensor C)) (curryObj (MonoidalCategory.tensor C)) ≅
      bifunctorComp₂₃ (curryObj (MonoidalCategory.tensor C)) (curryObj (MonoidalCategory.tensor C)) :=
  NatIso.ofComponents
    (fun X₁ => NatIso.ofComponents
      (fun X₂ => NatIso.ofComponents
        (fun X₃ => associator X₁ X₂ X₃)
          (fun {X₃ Y₃} φ => by simpa using associator_naturality (𝟙 X₁) (𝟙 X₂) φ))
        (fun {X₂ Y₂} φ => by
          ext X₃
          dsimp [curryObj] -- missing @simps
          simp))
        (fun {X₁ Y₁} φ => by
          ext X₂ X₃
          dsimp [curryObj] -- missing @simps
          simp)

end MonoidalCategory
namespace GradedObject

abbrev HasTensor (X Y : GradedObject I C) : Prop :=
  HasMap (((mapBifunctorFunctor (curryObj (MonoidalCategory.tensor C)) I I).obj X).obj Y)
    (fun x => x.1 + x.2)

noncomputable abbrev tensorObj (X Y : GradedObject I C) [HasTensor X Y] :
    GradedObject I C :=
  mapBifunctorMapObj (curryObj (MonoidalCategory.tensor C)) (fun x => x.1 + x.2) X Y

noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[simp]
noncomputable def whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
    [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
      tensorHom (𝟙 X) φ

@[simp]
noncomputable def whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
    [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
      tensorHom φ (𝟙 Y)

@[simp]
lemma tensor_id (X Y : GradedObject I C) [HasTensor X Y] :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  dsimp [tensorHom]
  simp
  rfl

lemma tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] [HasTensor X₂ Y₁]:
    tensorHom f g = whiskerRight f Y₁ ≫ whiskerLeft X₂ g := by
  dsimp only [tensorHom, mapBifunctorMapMap, whiskerLeft, whiskerRight]
  rw [← mapMap_comp]
  apply congr_mapMap
  simp

lemma tensor_comp {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₃ Y₃] :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  dsimp only [tensorHom, mapBifunctorMapMap]
  rw [← mapMap_comp]
  apply congr_mapMap
  simp

abbrev HasAssociator (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor X₂ X₃]
   [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)] :=
  HasGoodAssociator (MonoidalCategory.curriedAssociatorNatIso C)
    (fun ⟨i, j⟩ => i + j) (fun ⟨i, j⟩ => i + j) (fun ⟨i, j⟩ => i + j) (fun ⟨i, j⟩ => i + j)
    (fun ⟨i, j, k⟩ => i + j + k) (fun ⟨_, _, _⟩ => rfl) (fun ⟨i, j, k⟩ => add_assoc i j k)
    X₁ X₂ X₃

noncomputable def associator (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor X₂ X₃]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)] [H : HasAssociator X₁ X₂ X₃] :
  tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
    mapBifunctorBifunctorAssociator (H := H)

variable [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasAssociator X₁ X₂ X₃]

/-noncomputable instance : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := mapBifunctorMapMap _ _ f g
  tensorHom_def f g := tensorHom_def f g
  whiskerLeft X _ _ φ := whiskerLeft X φ
  whiskerRight {_ _ φ Y} := whiskerRight φ Y
  tensorUnit' := sorry
  associator X₁ X₂ X₃ := associator X₁ X₂ X₃
  associator_naturality := sorry
  leftUnitor := sorry
  leftUnitor_naturality := sorry
  rightUnitor := sorry
  rightUnitor_naturality := sorry
  tensor_comp f₁ f₂ g₁ g₂ := tensor_comp f₁ g₁ f₂ g₂
  pentagon := sorry
  triangle := sorry-/

end GradedObject

end CategoryTheory
