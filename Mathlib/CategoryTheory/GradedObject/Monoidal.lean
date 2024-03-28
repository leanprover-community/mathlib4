/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Scott Morrison
-/
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.GradedObject.Unitor
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Prod

/-!
# The monoidal category structures on graded objects

-/

universe u v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)

noncomputable instance (J : Type*) [hJ : Finite J] [PreservesFiniteCoproducts F] :
    PreservesColimitsOfShape (Discrete J) F := by
  apply Nonempty.some
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : PreservesColimitsOfShape (Discrete (Fin n)) F := PreservesFiniteCoproducts.preserves _
  exact ⟨preservesColimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F⟩

end Limits

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category C] [MonoidalCategory C]

namespace GradedObject

abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂)
    (fun ⟨i, j⟩  => i + j)

namespace Monoidal

noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

section

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
  X₁ i₁ ⊗ X₂ i₂ ⟶ tensorObj X₁ X₂ i₁₂ :=
    ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

variable {X₁ X₂}

@[ext]
lemma tensorObj_ext {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g) : f = g := by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

noncomputable def tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) :
    tensorObj X₁ X₂ k ⟶ A :=
  mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]
lemma ι_tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) (i₁ i₂ : I) (hi : i₁ + i₂ = k) :
    ιTensorObj X₁ X₂ i₁ i₂ k hi ≫ tensorObjDesc f = f i₁ i₂ hi := by
  apply ι_mapBifunctorMapObjDesc

end

noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]
lemma ι_tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ ⊗ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  refine' (ι_mapBifunctorMapMap (curriedTensor C) (fun ⟨i, j⟩ => i + j : I × I → I) f g
    i₁ i₂ i₁₂ h).trans _
  rw [← assoc]
  congr 1
  simp [curryObj, MonoidalCategory.tensorHom_def]

noncomputable abbrev whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
    [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
      tensorHom (𝟙 X) φ

noncomputable abbrev whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
    [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
      tensorHom φ (𝟙 Y)

@[simp]
lemma tensor_id (X Y : GradedObject I C) [HasTensor X Y] :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

lemma tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] [HasTensor X₂ Y₁]:
    tensorHom f g = whiskerRight f Y₁ ≫ whiskerLeft X₂ g := by
  dsimp only [tensorHom, mapBifunctorMapMap, whiskerLeft, whiskerRight]
  rw [← mapMap_comp]
  apply congr_mapMap
  simp

@[reassoc]
lemma tensor_comp {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₃ Y₃] :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  dsimp only [tensorHom, mapBifunctorMapMap]
  rw [← mapMap_comp]
  apply congr_mapMap
  simp

def r₁₂₃ : I × I × I → I := fun ⟨i, j, k⟩ => i + j + k

@[reducible] def ρ₁₂ : BifunctorComp₁₂IndexData (r₁₂₃ : _ → I) where
  I₁₂ := I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

@[reducible] def ρ₂₃ : BifunctorComp₂₃IndexData (r₁₂₃ : _ → I) where
  I₂₃ := I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm

variable (I) in
@[reducible]
def triangleIndexData : TriangleIndexData (r₁₂₃ : _ → I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  p₁₂ := fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add

abbrev _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

abbrev _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

section

variable (Z : C) (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor X₂ X₃]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  {Y₁ Y₂ Y₃ : GradedObject I C} [HasTensor Y₁ Y₂] [HasTensor Y₂ Y₃]
  [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₁ (tensorObj Y₂ Y₃)]

noncomputable def associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
  tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
    mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j :=
  X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ _ rfl ≫ ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j
    (by rw [← add_assoc, h])

@[reassoc]
lemma ιTensorObj₃_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ i₂₃ h') ≫
        ιTensorObj X₁ (tensorObj X₂ X₃) i₁ i₂₃ j (by rw [← h', ← add_assoc, h]) := by
  subst h'
  rfl

noncomputable def ιTensorObj₃' (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j :=
  (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ▷ X₃ i₃) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]
lemma ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
    (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h' ▷ X₃ i₃) ≫
        ιTensorObj (tensorObj X₁ X₂) X₃ i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
lemma ιTensorObj₃_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom f₁ (tensorHom f₂ f₃) j =
      (f₁ i₁ ⊗ f₂ i₂ ⊗ f₃ i₃) ≫ ιTensorObj₃ Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _  rfl,
    ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _  rfl, assoc, ι_tensorHom,
    ← id_tensorHom, ← id_tensorHom, ← MonoidalCategory.tensor_comp_assoc, ι_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, comp_id]

@[reassoc (attr := simp)]
lemma ιTensorObj₃'_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom (tensorHom f₁ f₂) f₃ j =
      ((f₁ i₁ ⊗ f₂ i₂) ⊗ f₃ i₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl,
    ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl, assoc, ι_tensorHom,
    ← tensorHom_id, ← tensorHom_id, ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ι_tensorHom, ← MonoidalCategory.tensor_comp_assoc, comp_id]

section

@[ext]
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ g) :
      f = g := by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

@[ext]
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    [H : HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) :
      f = g := by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

variable (X₁ X₂ X₃)

abbrev HasLeftTensor₃ObjExt (j : I) := PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) ↦
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
   ((curriedTensor C).obj Z)

variable {X₁ X₂ X₃}

@[ext]
lemma left_tensor_tensorObj₃_ext {j : I} {A : C} (Z : C)
    (f g : Z ⊗ tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [hZ : HasLeftTensor₃ObjExt Z X₁ X₂ X₃ j]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ f =
        (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ g) : f = g := by
    refine' (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) j) hZ).hom_ext _
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

end

variable (X₁ X₂ X₃)

@[reassoc (attr := simp)]
lemma ιTensorObj₃'_associator_hom
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).hom j =
      (α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
lemma ιTensorObj₃_associator_inv
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).inv j =
      (α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

variable {X₁ X₂ X₃}

lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by aesop_cat

end

section

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₃ X₄]
  [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]

noncomputable def ιTensorObj₄ (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j :=
  (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j
      (by rw [← h, ← add_assoc, ← add_assoc])

lemma ιTensorObj₄_eq (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I)
    (hi : i₂ + i₃ + i₄ = i₂₃₄) :
    ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h =
      (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ hi) ≫
        ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ i₂₃₄ j
          (by rw [← hi, ← add_assoc, ← add_assoc, h]) := by
  subst hi
  rfl

abbrev _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt :=
  ∀ (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

variable {X₁ X₂ X₃ X₄}

@[ext]
lemma tensorObj₄_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A)
    [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
    [H : HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (h : ∀ (i₁ i₂ i₃ i₄ : I) (h : i₁ + i₂ + i₃ + i₄ = j),
      ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ f =
        ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ g) : f = g := by
  apply tensorObj_ext
  intro i₁ i₂₃₄ h'
  apply left_tensor_tensorObj₃_ext
  intro i₂ i₃ i₄ h''
  have hj : i₁ + i₂ + i₃ + i₄ = j := by simp only [← h', ← h'', add_assoc]
  simpa only [assoc, ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j hj i₂₃₄ h''] using h i₁ i₂ i₃ i₄ hj

end

section Pentagon

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor X₂ X₃] [HasTensor X₃ X₄]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasTensor (tensorObj X₂ X₃) X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor (tensorObj (tensorObj X₁ X₂) X₃) X₄]
  [HasTensor (tensorObj X₁ (tensorObj X₂ X₃)) X₄]
  [HasTensor X₁ (tensorObj (tensorObj X₂ X₃) X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]
  [HasTensor (tensorObj X₁ X₂) (tensorObj X₃ X₄)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄]
  [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
  [HasGoodTensor₁₂Tensor (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensorTensor₂₃ (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensor₁₂Tensor X₁ X₂ (tensorObj X₃ X₄)]
  [HasGoodTensorTensor₂₃ X₁ X₂ (tensorObj X₃ X₄)]
  [HasTensor₄ObjExt X₁ X₂ X₃ X₄]

@[reassoc]
lemma pentagon_inv :
    tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).inv ≫ (associator X₁ (tensorObj X₂ X₃) X₄).inv ≫
        tensorHom (associator X₁ X₂ X₃).inv (𝟙 X₄) =
    (associator X₁ X₂ (tensorObj X₃ X₄)).inv ≫ (associator (tensorObj X₁ X₂) X₃ X₄).inv := by
  ext j i₁ i₂ i₃ i₄ h
  dsimp
  -- this proof needs some cleaning up because it uses
  -- lemmas id_tensorHom/tensorHom_id back and forth...
  -- working on the LHS
  conv_lhs => rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, ι_tensorHom_assoc,
    categoryOfGradedObjects_id, ← id_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ιTensorObj₃_associator_inv, ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl,
    id_tensor_comp, id_tensor_comp, assoc, assoc,
    id_tensorHom, id_tensorHom, id_tensorHom,
    ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
      (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
      (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]),
    assoc, ι_tensorHom, categoryOfGradedObjects_id,
    ← id_tensorHom, ← id_tensorHom, ← tensorHom_id, associator_inv_naturality_assoc,
    ← tensorHom_id, ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, assoc, id_tensorHom, id_tensorHom,
    ← ιTensorObj₃_eq_assoc X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl,
    ιTensorObj₃_associator_inv, comp_tensor_id, assoc, tensorHom_id, pentagon_inv_assoc,
    tensorHom_id]
  -- working on the RHS
  have H := (ιTensorObj X₁ X₂ i₁ i₂ _ rfl ⊗ 𝟙 _) ≫=
    ιTensorObj₃_associator_inv (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h
  rw [ιTensorObj₃_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl, assoc,
    ← id_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, comp_id, id_comp] at H
  conv_rhs => rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl,
    ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, ← id_tensorHom, id_tensor_comp, assoc,
    id_tensorHom, id_tensorHom, assoc,
    ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
      (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
    ιTensorObj₃_associator_inv_assoc, ← id_tensorHom, ← id_tensorHom,
    associator_inv_naturality_assoc,
    ιTensorObj₃'_eq X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j (by rw [← add_assoc, h]) _ rfl,
    assoc,
    ← tensorHom_id, ← MonoidalCategory.tensor_comp_assoc, comp_id, tensorHom_id,
    id_whiskerRight, id_comp, H,
    ← MonoidalCategory.tensor_id, MonoidalCategory.associator_inv_naturality_assoc,
    ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
    tensorHom_id, tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

lemma pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
    (associator X₁ (tensorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom =
    (associator (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← pentagon_inv_assoc, ← tensor_comp_assoc, id_comp, Iso.inv_hom_id,
    tensor_id, id_comp, Iso.inv_hom_id_assoc, ← tensor_comp, id_comp, Iso.inv_hom_id,
    tensor_id]

end Pentagon

section TensorUnit

variable [DecidableEq I] [HasInitial C]

noncomputable def tensorUnit : GradedObject I C := (single₀ I).obj (𝟙_ C)

noncomputable def tensorUnit₀ : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C :=
  singleObjApplyIso (0 : I) (𝟙_ C)

noncomputable def isInitialTensorUnitApply (i : I) (hi : i ≠ 0) :
    IsInitial ((tensorUnit : GradedObject I C) i) :=
  isInitialSingleObjApply _ _ _ hi

end TensorUnit

section LeftUnitor

variable [DecidableEq I] [HasInitial C]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curriedTensor C).flip.obj X₂)]
  (X X' : GradedObject I C)

instance : HasTensor tensorUnit X :=
  mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _

instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj
    ((single₀ I).obj (𝟙_ C))).obj X) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
  (inferInstance : HasTensor tensorUnit X)

noncomputable def leftUnitor : tensorObj tensorUnit X ≅ X :=
    mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X

lemma leftUnitor_inv_apply (i : I) :
    (leftUnitor X).inv i = (λ_ (X i)).inv ≫ tensorUnit₀.inv ▷ (X i) ≫
      ιTensorObj tensorUnit X 0 i i (zero_add i) := by
  dsimp [leftUnitor, tensorUnit₀]
  simp only [mapBifunctorLeftUnitor_inv_apply, Functor.id_obj, curryObj_obj_obj, tensor_obj,
    leftUnitorNatIso_inv_app, curryObj_map_app, tensor_map, Iso.cancel_iso_inv_left,
    curriedTensor_obj_obj, curriedTensor_map_app]
  rfl

variable {X X'}

@[reassoc (attr := simp)]
lemma leftUnitor_naturality (φ : X ⟶ X') :
    tensorHom (𝟙 (tensorUnit)) φ ≫ (leftUnitor X').hom =
      (leftUnitor X).hom ≫ φ := by
  apply mapBifunctorLeftUnitor_naturality

end LeftUnitor

section RightUnitor

variable [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  (X X' : GradedObject I C)

instance : HasTensor X tensorUnit :=
  mapBifunctorRightUnitor_hasMap (curriedTensor C) _
    (rightUnitorNatIso C) _ add_zero _

instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj X).obj
    ((single₀ I).obj (𝟙_ C))) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
  (inferInstance : HasTensor X tensorUnit)

noncomputable def rightUnitor : tensorObj X tensorUnit ≅ X :=
    mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X

lemma rightUnitor_inv_apply (i : I) :
    (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (X i) ◁ tensorUnit₀.inv ≫
      ιTensorObj X tensorUnit i 0 i (add_zero i) := by
  dsimp [rightUnitor, tensorUnit₀]
  simp only [mapBifunctorRightUnitor_inv_apply, Functor.id_obj, Functor.flip_obj_obj,
    curryObj_obj_obj, tensor_obj, rightUnitorNatIso_inv_app, curryObj_obj_map, tensor_map,
    Iso.cancel_iso_inv_left, curriedTensor_obj_obj, curriedTensor_obj_map]
  rfl

variable {X X'}

@[reassoc (attr := simp)]
lemma rightUnitor_naturality (φ : X ⟶ X') :
    tensorHom φ (𝟙 (tensorUnit)) ≫ (rightUnitor X').hom =
      (rightUnitor X).hom ≫ φ := by
  apply mapBifunctorRightUnitor_naturality

end RightUnitor

section Triangle

variable [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curriedTensor C).flip.obj X₂)]
  (X₁ X₃ : GradedObject I C) [HasTensor X₁ X₃]
  [HasTensor (tensorObj X₁ tensorUnit) X₃] [HasTensor X₁ (tensorObj tensorUnit X₃)]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] [HasGoodTensorTensor₂₃ X₁ tensorUnit X₃]

lemma triangle :
    (associator X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₃).hom =
      tensorHom (rightUnitor X₁).hom (𝟙 X₃) := by
  convert mapBifunctor_triangle (curriedAssociatorNatIso C) (𝟙_ C)
    (rightUnitorNatIso C) (leftUnitorNatIso C) (triangleIndexData I) X₁ X₃ (by simp)
  all_goals assumption

end Triangle

end Monoidal

section

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

noncomputable instance monoidalCategory : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.associator X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.associator_naturality f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensor_comp f₁ f₂ g₁ g₂ := Monoidal.tensor_comp f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

variable {A : C} (X₁ X₂ X₃ X₄ Y₁ Y₂ : GradedObject I C)

noncomputable def tensorObjIso :
    X₁ ⊗ X₂ ≅ mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂ := Iso.refl _

noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
  X₁ i₁ ⊗ X₂ i₂ ⟶ (X₁ ⊗ X₂) i₁₂ :=
    Monoidal.ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h

variable {X₁ X₂ Y₁ Y₂}

@[reassoc (attr := simp)]
lemma ι_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ ⊗ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  apply Monoidal.ι_tensorHom

variable (X₁ X₂)

@[simp]
abbrev cofanTensorFun (j : I) : { i : I × I | i.1 + i.2 = j } → C :=
  fun ⟨⟨i₁, i₂⟩, _⟩ => X₁ i₁ ⊗ X₂ i₂

@[simp]
noncomputable def cofanTensor (j : I) : Cofan (cofanTensorFun X₁ X₂ j) :=
  Cofan.mk ((X₁ ⊗ X₂) j) (fun ⟨⟨i₁, i₂⟩, hi⟩ => ιTensorObj X₁ X₂ i₁ i₂ j hi)

noncomputable def isColimitCofanTensor (j : I) : IsColimit (cofanTensor X₁ X₂ j) := by
  apply isColimitCofanMapObj

variable {X₁ X₂}

noncomputable def descTensor {j : I} (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ A) :
    (X₁ ⊗ X₂) j ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofanTensor X₁ X₂ j) (fun ⟨⟨i₁, i₂⟩, hi⟩ => f i₁ i₂ hi)

@[reassoc (attr := simp)]
lemma ι_descTensor (j : I) (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ A)
    (i₁ i₂ : I) (hi : i₁ + i₂ = j) :
    ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ descTensor f = f i₁ i₂ hi := by
  apply Cofan.IsColimit.fac

@[ext]
lemma tensorObj_ext {j : I} (f g : (X₁ ⊗ X₂) j ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g) : f = g :=
  Monoidal.tensorObj_ext f g h

end

section

instance (n : ℕ) : Finite ((fun (i : ℕ × ℕ) => i.1 + i.2) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by linarith⟩, ⟨i₂, by linarith⟩) : Fin (n + 1) × Fin (n + 1) )) ?_
  rintro ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ ⟨⟨j₁, j₂⟩, (hj : j₁ + j₂ = n)⟩ h
  simpa using h

instance (n : ℕ) : Finite ({ i : (ℕ × ℕ × ℕ) | i.1 + i.2.1 + i.2.2 = n }) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂, i₃⟩, (hi : i₁ + i₂ + i₃ = n)⟩ =>
    (⟨⟨i₁, by linarith⟩, ⟨i₂, by linarith⟩, ⟨i₃, by linarith⟩⟩ :
      Fin (n + 1) × Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨i₁, i₂, i₃⟩, hi : i₁ + i₂ + i₃ = n⟩ ⟨⟨j₁, j₂, j₃⟩, hj : j₁ + j₂ + j₃ = n⟩ h
  simpa using h

noncomputable example [HasFiniteCoproducts C]
    [∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)] :
    MonoidalCategory (GradedObject ℕ C) := inferInstance

end

end GradedObject

end CategoryTheory
