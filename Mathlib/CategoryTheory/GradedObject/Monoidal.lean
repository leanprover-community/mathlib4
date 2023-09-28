import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Prod

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
      (by aesop_cat)) (by aesop_cat)

end MonoidalCategory

namespace GradedObject

abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curryObj (MonoidalCategory.tensor C)) I I).obj X₁).obj X₂)
    (fun ⟨i, j⟩  => i + j)

namespace Monoidal

abbrev TensorCofan (X₁ X₂ : GradedObject I C) (j : I) :=
  (((mapBifunctor (curryObj (MonoidalCategory.tensor C)) I I).obj X₁).obj X₂).CofanMapObjFun (fun ⟨i, j⟩ => i + j) j

@[simps! pt]
def TensorCofan.mk (X₁ X₂ : GradedObject I C) (j : I) (pt : C)
    (ι : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ pt) : TensorCofan X₁ X₂ j :=
  CofanMapObjFun.mk _ _ _ pt (fun ⟨i₁, i₂⟩ h => ι i₁ i₂ h)

@[simp]
lemma TensorCofan.mk_inj (X₁ X₂ : GradedObject I C) (j : I) (pt : C)
    (ι : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ pt) (i₁ i₂ : I) (h : i₁ + i₂ = j) :
    (TensorCofan.mk X₁ X₂ j pt ι).proj ⟨⟨i₁, i₂⟩, h⟩ = ι i₁ i₂ h := rfl

lemma TensorCofan.hasTensor (X₁ X₂ : GradedObject I C)
    (c : ∀ i, TensorCofan X₁ X₂ i) (hc : ∀ i, IsColimit (c i)) :
    HasTensor X₁ X₂ :=
  CofanMapObjFun.hasMap _ _ c hc

noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curryObj (MonoidalCategory.tensor C)) (fun ⟨i, j⟩ => i + j) X₁ X₂


section

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
  X₁ i₁ ⊗ X₂ i₂ ⟶ tensorObj X₁ X₂ i₁₂ :=
    ιMapBifunctorMapObj (curryObj (MonoidalCategory.tensor C)) _ _ _ _ _ _ h

variable {X₁ X₂}

@[ext]
lemma tensorObj_ext {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g) : f = g := by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

end

noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]
lemma ι_tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁]
    [HasTensor X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ ⊗ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  refine' (ι_mapBifunctorMapMap (curryObj (MonoidalCategory.tensor C)) (fun ⟨i, j⟩ => i + j : I × I → I) f g
    i₁ i₂ i₁₂ h).trans _
  rw [← assoc]
  congr 1
  simp [curryObj]

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

@[reducible] def ρ₁₂ : Bifunctor₁₂BifunctorIndexData (r₁₂₃ : _ → I) where
  I₁₂ := I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

@[reducible] def ρ₂₃ : BifunctorBifunctor₂₃IndexData (r₁₂₃ : _ → I) where
  I₂₃ := I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := add_assoc _ _ _

abbrev _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodBifunctor₁₂BifunctorObj (curryObj (MonoidalCategory.tensor C))
    (curryObj (MonoidalCategory.tensor C)) ρ₁₂ X₁ X₂ X₃

abbrev _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodBifunctorBifunctor₂₃Obj (curryObj (MonoidalCategory.tensor C)) (curryObj (MonoidalCategory.tensor C)) ρ₂₃ X₁ X₂ X₃

section

variable (Z : C) (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor X₂ X₃]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  {Y₁ Y₂ Y₃ : GradedObject I C} [HasTensor Y₁ Y₂] [HasTensor Y₂ Y₃]
  [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₁ (tensorObj Y₂ Y₃)]

noncomputable def associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
  tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
    mapBifunctorBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j :=
  (𝟙 _ ⊗ ιTensorObj X₂ X₃ i₂ i₃ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j (by rw [← add_assoc, h])

@[reassoc]
lemma ιTensorObj₃_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (𝟙 _ ⊗ ιTensorObj X₂ X₃ i₂ i₃ i₂₃ h') ≫
        ιTensorObj X₁ (tensorObj X₂ X₃) i₁ i₂₃ j (by rw [← h', ← add_assoc, h]) := by
  subst h'
  rfl

noncomputable def ιTensorObj₃' (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j :=
  (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ⊗ 𝟙 _) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]
lemma ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
    (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h' ⊗ 𝟙 _) ≫
        ιTensorObj (tensorObj X₁ X₂) X₃ i₁₂ i₃ j (by rw [←h', h]) := by
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
    ← MonoidalCategory.tensor_comp_assoc, id_comp, ι_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, comp_id]

@[reassoc (attr := simp)]
lemma ιTensorObj₃'_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom (tensorHom f₁ f₂) f₃ j =
      ((f₁ i₁ ⊗ f₂ i₂) ⊗ f₃ i₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl,
    ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl, assoc, ι_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, ι_tensorHom,
    ← MonoidalCategory.tensor_comp_assoc, comp_id]

section

@[ext]
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ g) : f = g := by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

@[ext]
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    [H : HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

variable (X₁ X₂ X₃)

abbrev HasLeftTensor₃ObjExt (j : I) := PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) ↦ (((mapTrifunctor (bifunctorComp₂₃ (curryObj (tensor C)) (curryObj (tensor C))) I I I).obj X₁).obj X₂).obj X₃ i)
   ((curryObj (tensor C)).obj Z)

variable {X₁ X₂ X₃}

@[ext]
lemma left_tensor_tensorObj₃_ext {j : I} {A : C} (Z : C) (f g : Z ⊗ tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [hZ : HasLeftTensor₃ObjExt Z X₁ X₂ X₃ j]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      (𝟙 Z ⊗ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ f =
        (𝟙 Z ⊗ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ g) : f = g := by
    refine' (@isColimitOfPreserves C _ C _ _ _ _ ((curryObj (MonoidalCategory.tensor C)).obj Z) _
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
  ι_mapBifunctorBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
lemma ιTensorObj₃_associator_inv
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).inv j =
      (α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

variable {X₁ X₂ X₃}

lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by aesop_cat

end

section

variable [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂)]

noncomputable def tensorUnit : GradedObject I C :=
  fun i => if (i = 0) then (𝟙_ C) else initial C

variable (C)

noncomputable def tensorUnit₀' (i : I) (hi : i = 0) : (tensorUnit : GradedObject I C) i ≅ 𝟙_ C :=
  eqToIso (by subst hi; simp [tensorUnit])

variable (I)

noncomputable def tensorUnit₀ : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C :=
  tensorUnit₀' _ _ rfl

@[simp]
lemma tensorUnit₀'_eq : tensorUnit₀' C 0 rfl = tensorUnit₀ I C := rfl

variable {I}

noncomputable def isInitialTensorUnitApply (i : I) (hi : i ≠ 0) :
    IsInitial ((tensorUnit : GradedObject I C) i) := by
  dsimp [tensorUnit]
  rw [if_neg hi]
  exact initialIsInitial

variable {C}

def isInitialTensor (X₁ X₂ : C) (hX₁ : IsInitial X₁) : IsInitial (X₁ ⊗ X₂) :=
  IsInitial.isInitialObj ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂) _ hX₁

def tensorIsInitial (X₁ X₂ : C) (hX₂ : IsInitial X₂) : IsInitial (X₁ ⊗ X₂) :=
  IsInitial.isInitialObj ((curryObj (MonoidalCategory.tensor C)).obj X₁) _ hX₂

variable (X : GradedObject I C)

@[simps! pt]
noncomputable def unitTensorCofan (i : I) : TensorCofan tensorUnit X i :=
  TensorCofan.mk _ _ _ (X i) (fun a b h =>
    if ha : a = 0
      then
        ((tensorUnit₀' C a ha).hom ⊗ 𝟙 (X b) : tensorUnit a ⊗ X b ⟶ 𝟙_ C ⊗ X b) ≫
          (leftUnitor (X b)).hom ≫ eqToHom (by
            obtain rfl : b = i := by rw [← h, ha, zero_add]
            rfl)
      else IsInitial.to (isInitialTensor _ _ (isInitialTensorUnitApply _ _ ha)) _)

@[simp]
lemma unitTensorCofan_ι₀ (i : I) :
    (unitTensorCofan X i).proj ⟨⟨0, i⟩, zero_add i⟩ =
      ((tensorUnit₀ I C).hom ⊗ (𝟙 (X i))) ≫ (λ_ (X i)).hom := by
  dsimp [unitTensorCofan]
  rw [dif_pos rfl]
  simp

noncomputable def isColimitUnitTensorCofan (i : I) : IsColimit (unitTensorCofan X i) :=
  mkCofanColimit _
    (fun s => (leftUnitor (X i)).inv ≫
      ((tensorUnit₀ I C).inv ⊗ 𝟙 (X i)) ≫ s.proj ⟨⟨0, i⟩, zero_add i⟩)
    (fun s ⟨⟨a, b⟩, (hi : a + b = i)⟩ => by
      by_cases a = 0
      · subst h
        obtain rfl : b = i := by rw [← hi, zero_add]
        simp
      · apply IsInitial.hom_ext
        apply isInitialTensor
        exact isInitialTensorUnitApply  _ _ h)
    (fun s m hm => by
      dsimp
      rw [← hm ⟨⟨0, i⟩, zero_add i⟩ ]
      simp)

instance : HasTensor tensorUnit X :=
  TensorCofan.hasTensor _ _ _ (fun i => isColimitUnitTensorCofan X i)

noncomputable def leftUnitor :
    tensorObj tensorUnit X ≅ X := isoMk _ _
      (fun i => ((unitTensorCofan X i).iso (isColimitUnitTensorCofan X i)).symm)

lemma leftUnitor_inv_apply (i : I) :
    (leftUnitor X).inv i =
      (λ_ _).inv ≫ ((tensorUnit₀ I C).inv ⊗ 𝟙 (X i)) ≫ ιTensorObj tensorUnit X 0 i i (zero_add i) := by
  rfl

lemma leftUnitor_inv_naturality {X₁ X₂ : GradedObject I C} (f : X₁ ⟶ X₂) :
    f ≫ (leftUnitor X₂).inv = (leftUnitor X₁).inv ≫ tensorHom (𝟙 tensorUnit) f := by
  ext i
  dsimp
  rw [leftUnitor_inv_apply, leftUnitor_inv_apply, assoc, assoc, ι_tensorHom,
    leftUnitor_inv_naturality_assoc, id_tensor_comp_tensor_id_assoc]
  dsimp
  rw [tensor_id_comp_id_tensor_assoc]

lemma leftUnitor_naturality {X₁ X₂ : GradedObject I C} (f : X₁ ⟶ X₂) :
    tensorHom (𝟙 tensorUnit) f ≫ (leftUnitor X₂).hom = (leftUnitor X₁).hom ≫ f := by
  rw [← cancel_mono (leftUnitor X₂).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    leftUnitor_inv_naturality, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma ιTensorObj_leftUnitor_hom (X : GradedObject I C) (i : I) :
    ιTensorObj tensorUnit X 0 i i (zero_add i) ≫ (leftUnitor X).hom i =
      ((tensorUnit₀ I C).hom ⊗ 𝟙 (X i)) ≫ (λ_ (X i)).hom := by
  rw [← cancel_mono ((leftUnitor X).inv i), assoc, assoc,
    iso_hom_inv_id_apply, comp_id, leftUnitor_inv_apply,
    Iso.hom_inv_id_assoc, hom_inv_id_tensor_assoc, MonoidalCategory.tensor_id,
    id_comp, id_comp]

@[simps! pt]
noncomputable def tensorUnitCofan (i : I) : TensorCofan X tensorUnit i :=
  TensorCofan.mk _ _ _ (X i) (fun a b h =>
    if hb : b = 0
      then
        (𝟙 (X a) ⊗ (tensorUnit₀' C b hb).hom) ≫ (rightUnitor (X a)).hom ≫ eqToHom (by
          obtain rfl : a = i := by rw [← h, hb, add_zero]
          rfl)
      else IsInitial.to (tensorIsInitial _ _ (isInitialTensorUnitApply _ _ hb)) _)

@[simp]
lemma tensorUnitCofan_ι₀ (i : I) :
    (tensorUnitCofan X i).proj ⟨⟨i, 0⟩, add_zero i⟩ =
      (𝟙 (X i) ⊗ (tensorUnit₀ I C).hom) ≫ (rightUnitor (X i)).hom := by
  dsimp [tensorUnitCofan]
  rw [dif_pos rfl]
  simp

noncomputable def isColimitTensorUnitCofan (i : I) : IsColimit (tensorUnitCofan X i) :=
  mkCofanColimit _
    (fun s => (rightUnitor (X i)).inv ≫
      (𝟙 (X i) ⊗ (tensorUnit₀ I C).inv) ≫ s.proj ⟨⟨i, 0⟩, add_zero i⟩)
    (fun s ⟨⟨a, b⟩, (hi : a + b = i)⟩ => by
      by_cases b = 0
      · subst h
        obtain rfl : a = i := by rw [← hi, add_zero]
        simp
      · apply IsInitial.hom_ext
        apply tensorIsInitial
        exact isInitialTensorUnitApply  _ _ h)
    (fun s m hm => by
      dsimp
      rw [← hm ⟨⟨i, 0⟩, add_zero i⟩ ]
      simp)

instance : HasTensor X tensorUnit :=
  TensorCofan.hasTensor _ _ _ (fun i => isColimitTensorUnitCofan X i)

noncomputable def rightUnitor :
    tensorObj X tensorUnit ≅ X := isoMk _ _
      (fun i => ((tensorUnitCofan X i).iso (isColimitTensorUnitCofan X i)).symm)

lemma rightUnitor_inv_apply (i : I) :
    (rightUnitor X).inv i =
      (ρ_ _).inv ≫ (𝟙 (X i) ⊗ (tensorUnit₀ I C).inv) ≫ ιTensorObj X tensorUnit i 0 i (add_zero i) := by
  rfl

lemma rightUnitor_inv_naturality {X₁ X₂ : GradedObject I C} (f : X₁ ⟶ X₂) :
    f ≫ (rightUnitor X₂).inv = (rightUnitor X₁).inv ≫ tensorHom f (𝟙 tensorUnit) := by
  ext i
  dsimp
  rw [rightUnitor_inv_apply, rightUnitor_inv_apply, assoc, assoc, ι_tensorHom,
    rightUnitor_inv_naturality_assoc, tensor_id_comp_id_tensor_assoc]
  dsimp
  rw [id_tensor_comp_tensor_id_assoc]

lemma rightUnitor_naturality {X₁ X₂ : GradedObject I C} (f : X₁ ⟶ X₂) :
    tensorHom f (𝟙 tensorUnit) ≫ (rightUnitor X₂).hom = (rightUnitor X₁).hom ≫ f := by
  rw [← cancel_mono (rightUnitor X₂).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    rightUnitor_inv_naturality, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma ιTensorObj_rightUnitor_hom (X : GradedObject I C) (i : I) :
    ιTensorObj X tensorUnit i 0 i (add_zero i) ≫ (rightUnitor X).hom i =
      (𝟙 (X i ) ⊗ (tensorUnit₀ I C).hom) ≫ (ρ_ (X i)).hom := by
  rw [← cancel_mono ((rightUnitor X).inv i), assoc, assoc,
    iso_hom_inv_id_apply, comp_id, rightUnitor_inv_apply,
    Iso.hom_inv_id_assoc, ← MonoidalCategory.tensor_comp_assoc, id_comp,
    Iso.hom_inv_id, MonoidalCategory.tensor_id, id_comp]

lemma triangle (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]
    [HasTensor (tensorObj X₁ tensorUnit) X₂]
    [HasTensor X₁ (tensorObj tensorUnit X₂)] [HasGoodTensor₁₂Tensor X₁ tensorUnit X₂]
    [HasGoodTensorTensor₂₃ X₁ tensorUnit X₂] :
  (associator X₁ tensorUnit X₂).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₂).hom =
    tensorHom (rightUnitor X₁).hom (𝟙 X₂) := by
  ext j i₁ k i₂ h
  simp only [categoryOfGradedObjects_comp, ιTensorObj₃'_associator_hom_assoc]
  by_cases h' : k = 0
  · subst h'
    rw [ιTensorObj₃_eq X₁ tensorUnit X₂ i₁ 0 i₂ j h i₂ (zero_add i₂),
      ιTensorObj₃'_eq X₁ tensorUnit X₂ i₁ 0 i₂ j h i₁ (add_zero i₁), assoc, assoc,
      ι_tensorHom, ι_tensorHom, categoryOfGradedObjects_id, categoryOfGradedObjects_id,
      ← cancel_epi ((𝟙 (X₁ i₁) ⊗ (tensorUnit₀ I C).inv) ⊗ 𝟙 (X₂ i₂)),
      associator_naturality_assoc (𝟙 (X₁ i₁)) (tensorUnit₀ I C).inv (𝟙 (X₂ i₂)),
      ← MonoidalCategory.tensor_comp_assoc, ← MonoidalCategory.tensor_comp_assoc,
      assoc, assoc, id_comp, id_comp, ιTensorObj_leftUnitor_hom,
      ← MonoidalCategory.tensor_comp_assoc, id_comp, Iso.inv_hom_id, MonoidalCategory.tensor_id,
      id_comp, triangle_assoc, ← MonoidalCategory.tensor_comp_assoc,
      ← MonoidalCategory.tensor_comp_assoc, comp_id, comp_id, assoc, ιTensorObj_rightUnitor_hom,
      ← MonoidalCategory.tensor_comp_assoc, id_comp, Iso.inv_hom_id, MonoidalCategory.tensor_id,
      id_comp]
  · apply IsInitial.hom_ext
    apply isInitialTensor
    apply tensorIsInitial
    exact isInitialTensorUnitApply C k h'

end

section

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₃ X₄]
  [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]

noncomputable def ιTensorObj₄ (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j :=
  (𝟙 _ ⊗ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j (by rw [← h, ← add_assoc, ← add_assoc])

lemma ιTensorObj₄_eq (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I) (hi : i₂ + i₃ + i₄ = i₂₃₄) :
    ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h =
      (𝟙 _ ⊗ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ hi) ≫
        ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ i₂₃₄ j (by rw [← hi, ← add_assoc, ← add_assoc, h]) := by
  subst hi
  rfl

abbrev _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt := ∀ (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

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

section pentagon

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
  -- working on the LHS
  rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, assoc, ι_tensorHom_assoc,
    categoryOfGradedObjects_id, ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ιTensorObj₃_associator_inv, ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl,
    id_tensor_comp, id_tensor_comp, assoc, assoc,
    ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
      (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
      (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]),
    assoc, ι_tensorHom, categoryOfGradedObjects_id, associator_inv_naturality_assoc,
    ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ← MonoidalCategory.tensor_comp_assoc, id_comp, assoc,
    ← ιTensorObj₃_eq_assoc X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl,
    ιTensorObj₃_associator_inv, comp_tensor_id, assoc, pentagon_inv_assoc]
  -- working on the RHS
  have H := (ιTensorObj X₁ X₂ i₁ i₂ _ rfl ⊗ 𝟙 _) ≫=
    ιTensorObj₃_associator_inv (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h
  rw [ιTensorObj₃_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl, assoc,
    ← MonoidalCategory.tensor_comp_assoc, comp_id, id_comp] at H
  rw [ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, id_tensor_comp, assoc,
    ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
      (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
    ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_assoc,
    ιTensorObj₃'_eq X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j (by rw [← add_assoc, h]) _ rfl,
    assoc, ← MonoidalCategory.tensor_comp_assoc, comp_id, MonoidalCategory.tensor_id,
    id_comp, H, ← MonoidalCategory.tensor_id, MonoidalCategory.associator_inv_naturality_assoc,
    ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
    ← MonoidalCategory.tensor_comp_assoc, id_comp,
    ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

lemma pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
      (associator X₁ (tensorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom =
    (associator (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← pentagon_inv_assoc, ← tensor_comp_assoc, id_comp, Iso.inv_hom_id,
    tensor_id, id_comp, Iso.inv_hom_id_assoc, ← tensor_comp, id_comp, Iso.inv_hom_id,
    tensor_id]

end pentagon

end Monoidal

section

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

noncomputable instance monoidalCategory : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit' := Monoidal.tensorUnit
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
    X₁ ⊗ X₂ ≅ mapBifunctorMapObj
      (curryObj (MonoidalCategory.tensor C)) (fun ⟨i, j⟩ => i + j) X₁ X₂ := Iso.refl _

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
  refine' Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by linarith⟩, ⟨i₂, by linarith⟩) : Fin (n + 1) × Fin (n + 1) )) _
  rintro ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ ⟨⟨j₁, j₂⟩, (hj : j₁ + j₂ = n)⟩ h
  simpa using h

instance (n : ℕ) : Finite ({ i : (ℕ × ℕ × ℕ) | i.1 + i.2.1 + i.2.2 = n }) := by
  refine' Finite.of_injective (fun ⟨⟨i₁, i₂, i₃⟩, (hi : i₁ + i₂ + i₃ = n)⟩ =>
    (⟨⟨i₁, by linarith⟩, ⟨i₂, by linarith⟩, ⟨i₃, by linarith⟩⟩ :
      Fin (n+1) × Fin (n+1) × Fin (n+1))) _
  rintro ⟨⟨i₁, i₂, i₃⟩, hi : i₁ + i₂ + i₃ = n⟩ ⟨⟨j₁, j₂, j₃⟩, hj : j₁ + j₂ + j₃ = n⟩ h
  simpa using h

noncomputable example [HasFiniteCoproducts C]
    [∀ (X : C), PreservesFiniteCoproducts ((curryObj (tensor C)).obj X)]
    [∀ (X : C), PreservesFiniteCoproducts ((curryObj (tensor C)).flip.obj X)] :
    MonoidalCategory (GradedObject ℕ C) := inferInstance

end

end GradedObject

end CategoryTheory
