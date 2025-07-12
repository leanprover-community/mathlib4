/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
import Mathlib.CategoryTheory.GradedObject.Unitor
import Mathlib.Data.Fintype.Prod

/-!
# The monoidal category structures on graded objects

Assuming that `C` is a monoidal category and that `I` is an additive monoid,
we introduce a partially defined tensor product on the category `GradedObject I C`:
given `X₁` and `X₂` two objects in `GradedObject I C`, we define
`GradedObject.Monoidal.tensorObj X₁ X₂` under the assumption `HasTensor X₁ X₂`
that the coproduct of `X₁ i ⊗ X₂ j` for `i + j = n` exists for any `n : I`.

Under suitable assumptions about the existence of coproducts and the
preservation of certain coproducts by the tensor products in `C`, we
obtain a monoidal category structure on `GradedObject I C`.
In particular, if `C` has finite coproducts to which the tensor
product commutes, we obtain a monoidal category structure on `GradedObject ℕ C`.

-/

universe u

namespace CategoryTheory

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category C] [MonoidalCategory C]

namespace GradedObject

/-- The tensor product of two graded objects `X₁` and `X₂` exists if for any `n`,
the coproduct of the objects `X₁ i ⊗ X₂ j` for `i + j = n` exists. -/
abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)

lemma hasTensor_of_iso {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) [HasTensor X₁ X₂] :
    HasTensor Y₁ Y₂ := by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ ↦ (eval i).mapIso e₁ ⊗ᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

namespace Monoidal

/-- The tensor product of two graded objects. -/
noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

section

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

/-- The inclusion of a summand in a tensor product of two graded objects. -/
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

/-- Constructor for morphisms from a tensor product of two graded objects. -/
noncomputable def tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) : tensorObj X₁ X₂ k ⟶ A :=
  mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]
lemma ι_tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) (i₁ i₂ : I) (hi : i₁ + i₂ = k) :
    ιTensorObj X₁ X₂ i₁ i₂ k hi ≫ tensorObjDesc f = f i₁ i₂ hi := by
  apply ι_mapBifunctorMapObjDesc

end

/-- The morphism `tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂` induced by morphisms of graded
objects `f : X₁ ⟶ X₂` and `g : Y₁ ⟶ Y₂`. -/
noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]
lemma ι_tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ ⊗ₘ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  rw [tensorHom_def, assoc]
  apply ι_mapBifunctorMapMap

/-- The morphism `tensorObj X Y₁ ⟶ tensorObj X Y₂` induced by a morphism of graded objects
`φ : Y₁ ⟶ Y₂`. -/
noncomputable abbrev whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
    [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  tensorHom (𝟙 X) φ

/-- The morphism `tensorObj X₁ Y ⟶ tensorObj X₂ Y` induced by a morphism of graded objects
`φ : X₁ ⟶ X₂`. -/
noncomputable abbrev whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
    [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom φ (𝟙 Y)

@[simp]
lemma tensor_id (X Y : GradedObject I C) [HasTensor X Y] :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

@[reassoc]
lemma tensorHom_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₃ Y₃] :
    tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ = tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  dsimp only [tensorHom, mapBifunctorMapMap]
  rw [← mapMap_comp]
  apply congr_mapMap
  simp

/-- The isomorphism `tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂` induced by isomorphisms of graded
objects `e : X₁ ≅ X₂` and `e' : Y₁ ≅ Y₂`. -/
@[simps]
noncomputable def tensorIso {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂ where
  hom := tensorHom e.hom e'.hom
  inv := tensorHom e.inv e'.inv
  hom_inv_id := by simp [tensorHom_comp_tensorHom]
  inv_hom_id := by simp [tensorHom_comp_tensorHom]

lemma tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₂ Y₁] :
    tensorHom f g = whiskerRight f Y₁ ≫ whiskerLeft X₂ g := by
  rw [tensorHom_comp_tensorHom, id_comp, comp_id]

/-- This is the addition map `I × I × I → I` for an additive monoid `I`. -/
def r₁₂₃ : I × I × I → I := fun ⟨i, j, k⟩ => i + j + k

/-- Auxiliary definition for `associator`. -/
@[reducible] def ρ₁₂ : BifunctorComp₁₂IndexData (r₁₂₃ : _ → I) where
  I₁₂ := I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

/-- Auxiliary definition for `associator`. -/
@[reducible] def ρ₂₃ : BifunctorComp₂₃IndexData (r₁₂₃ : _ → I) where
  I₂₃ := I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm

variable (I) in
/-- Auxiliary definition for `associator`. -/
@[reducible]
def triangleIndexData : TriangleIndexData (r₁₂₃ : _ → I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  p₁₂ := fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add

/-- Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁₂ : I` and `i₃ : I`, the tensor product functor `- ⊗ X₃ i₃`
commutes with the coproduct of the objects `X₁ i₁ ⊗ X₂ i₂` such that `i₁ + i₂ = i₁₂`. -/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

/-- Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁ : I` and `i₂₃ : I`, the tensor product functor `X₁ i₁ ⊗ -`
commutes with the coproduct of the objects `X₂ i₂ ⊗ X₃ i₃` such that `i₂ + i₃ = i₂₃`. -/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

section

variable (Z : C) (X₁ X₂ X₃ : GradedObject I C)
  {Y₁ Y₂ Y₃ : GradedObject I C}

section
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)]

/-- The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j`
when `i₁ + i₂ + i₃ = j`. -/
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

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
lemma ιTensorObj₃_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom f₁ (tensorHom f₂ f₃) j =
      (f₁ i₁ ⊗ₘ f₂ i₂ ⊗ₘ f₃ i₃) ≫ ιTensorObj₃ Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _  rfl,
    ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _  rfl, assoc, ι_tensorHom,
    ← id_tensorHom, ← id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc, ι_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, comp_id]

@[ext (iff := false)]
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ g) :
      f = g := by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor Y₁ Y₂]
  [HasTensor (tensorObj Y₁ Y₂) Y₃]

/-- The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j`
when `i₁ + i₂ + i₃ = j`. -/
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
lemma ιTensorObj₃'_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom (tensorHom f₁ f₂) f₃ j =
      ((f₁ i₁ ⊗ₘ f₂ i₂) ⊗ₘ f₃ i₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl,
    ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _  rfl, assoc, ι_tensorHom,
    ← tensorHom_id, ← tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp,
    ι_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc, comp_id]

@[ext (iff := false)]
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    [H : HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) :
      f = g := by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)]

/-- The associator isomorphism for graded objects. -/
noncomputable def associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
  tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
    mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

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

variable [HasTensor Y₁ Y₂] [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)] in
lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
        #adaptation_note /-- https://github.com/leanprover/lean4/pull/4154
        this used to be aesop_cat -/
        ext x i₁ i₂ i₃ h : 2
        simp only [categoryOfGradedObjects_comp, ιTensorObj₃'_tensorHom_assoc,
          associator_conjugation, ιTensorObj₃'_associator_hom, assoc, Iso.inv_hom_id_assoc,
          ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_tensorHom]

end

/-- Given `Z : C` and three graded objects `X₁`, `X₂` and `X₃` in `GradedObject I C`,
this typeclass expresses that functor `Z ⊗ _` commutes with the coproduct of
the objects `X₁ i₁ ⊗ (X₂ i₂ ⊗ X₃ i₃)` such that `i₁ + i₂ + i₃ = j` for a certain `j`.
See lemma `left_tensor_tensorObj₃_ext`. -/
abbrev _root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt (j : I) := PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) ↦
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
   ((curriedTensor C).obj Z)

variable {X₁ X₂ X₃}
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)]

@[ext (iff := false)]
lemma left_tensor_tensorObj₃_ext {j : I} {A : C} (Z : C)
    (f g : Z ⊗ tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [hZ : HasLeftTensor₃ObjExt Z X₁ X₂ X₃ j]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ f =
        (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ g) : f = g := by
    refine (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) (j := j)) hZ).hom_ext ?_
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

end

section

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₃ X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]

/-- The inclusion
`X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j`
when `i₁ + i₂ + i₃ + i₄ = j`. -/
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

/-- Given four graded objects, this is the condition
`HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄` for all indices `i₁` and `i₂₃₄`,
see the lemma `tensorObj₄_ext`. -/
abbrev _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt :=
  ∀ (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

variable {X₁ X₂ X₃ X₄}

@[ext (iff := false)]
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
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄] [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
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
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc, ιTensorObj₃_associator_inv,
      ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl, ιTensorObj₃_associator_inv,
      MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl,
      ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_associator_inv, whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

lemma pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
    (associator X₁ (tensorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom =
    (associator (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← pentagon_inv_assoc]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

end Pentagon

section TensorUnit

variable [DecidableEq I] [HasInitial C]

/-- The unit of the tensor product on graded objects is `(single₀ I).obj (𝟙_ C)`. -/
noncomputable def tensorUnit : GradedObject I C := (single₀ I).obj (𝟙_ C)

/-- The canonical isomorphism `tensorUnit 0 ≅ 𝟙_ C` -/
noncomputable def tensorUnit₀ : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C :=
  singleObjApplyIso (0 : I) (𝟙_ C)

/-- `tensorUnit i` is an initial object when `i ≠ 0`. -/
noncomputable def isInitialTensorUnitApply (i : I) (hi : i ≠ 0) :
    IsInitial ((tensorUnit : GradedObject I C) i) :=
  isInitialSingleObjApply _ _ _ hi

end TensorUnit

section LeftUnitor

variable [DecidableEq I] [HasInitial C]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  (X X' : GradedObject I C)

instance : HasTensor tensorUnit X :=
  mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _

instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj
    ((single₀ I).obj (𝟙_ C))).obj X) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
  (inferInstance : HasTensor tensorUnit X)

/-- The left unitor isomorphism for graded objects. -/
noncomputable def leftUnitor : tensorObj tensorUnit X ≅ X :=
    mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X

lemma leftUnitor_inv_apply (i : I) :
    (leftUnitor X).inv i = (λ_ (X i)).inv ≫ tensorUnit₀.inv ▷ (X i) ≫
      ιTensorObj tensorUnit X 0 i i (zero_add i) := rfl

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

/-- The right unitor isomorphism for graded objects. -/
noncomputable def rightUnitor : tensorObj X tensorUnit ≅ X :=
    mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X

lemma rightUnitor_inv_apply (i : I) :
    (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (X i) ◁ tensorUnit₀.inv ≫
      ιTensorObj X tensorUnit i 0 i (add_zero i) := rfl

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
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

end

section

instance (n : ℕ) : Finite ((fun (i : ℕ × ℕ) => i.1 + i.2) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by omega⟩, ⟨i₂, by omega⟩) : Fin (n + 1) × Fin (n + 1) )) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

instance (n : ℕ) : Finite ({ i : (ℕ × ℕ × ℕ) | i.1 + i.2.1 + i.2.2 = n }) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂, i₃⟩, (hi : i₁ + i₂ + i₃ = n)⟩ =>
    (⟨⟨i₁, by omega⟩, ⟨i₂, by omega⟩, ⟨i₃, by omega⟩⟩ :
      Fin (n + 1) × Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _, _⟩, _⟩ ⟨⟨_, _, _⟩, _⟩ h
  simpa using h

/-!
The monoidal category structure on `GradedObject ℕ C` can be inferred
from the assumptions `[HasFiniteCoproducts C]`,
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]` and
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]`.
This requires importing `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`.
-/

end

end GradedObject

end CategoryTheory
