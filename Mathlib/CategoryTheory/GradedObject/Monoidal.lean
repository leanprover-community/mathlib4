import Mathlib.CategoryTheory.GradedObject.Trifunctor

namespace CategoryTheory

open Limits MonoidalCategory Category

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

abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctorFunctor (curryObj (MonoidalCategory.tensor C)) I I).obj X₁).obj X₂)
    (fun x => x.1 + x.2)

noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curryObj (MonoidalCategory.tensor C)) (fun x => x.1 + x.2) X₁ X₂

abbrev TensorCandidate (X₁ X₂ : GradedObject I C) (j : I) :=
  (((mapBifunctorFunctor (curryObj (MonoidalCategory.tensor C)) I I).obj X₁).obj X₂).MapObjCandidate (fun ⟨i, j⟩ => i + j) j

@[simps! pt]
def TensorCandidate.mk (X₁ X₂ : GradedObject I C) (j : I) (pt : C)
    (ι : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ pt) : TensorCandidate X₁ X₂ j :=
  MapObjCandidate.mk _ _ _ pt (fun ⟨i₁, i₂⟩ h => ι i₁ i₂ h)

@[simp]
lemma TensorCandidate.mk_ι' (X₁ X₂ : GradedObject I C) (j : I) (pt : C)
    (ι : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), X₁ i₁ ⊗ X₂ i₂ ⟶ pt) (i₁ i₂ : I) (h : i₁ + i₂ = j) :
    (TensorCandidate.mk X₁ X₂ j pt ι).ι' ⟨i₁, i₂⟩ h = ι i₁ i₂ h := rfl

lemma TensorCandidate.hasTensor (X₁ X₂ : GradedObject I C)
    (c : ∀ i, TensorCandidate X₁ X₂ i) (hc : ∀ i, IsColimit (c i)) :
    HasTensor X₁ X₂ :=
  MapObjCandidate.hasMap _ _ c hc

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

@[reassoc]
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

section

variable (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor X₂ X₃]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]

noncomputable def associator [H : HasAssociator X₁ X₂ X₃] :
  tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
    mapBifunctorBifunctorAssociator (H := H)

noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j :=
  (𝟙 _ ⊗ ιTensorObj X₂ X₃ i₂ i₃ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j (by rw [← add_assoc, h])

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

noncomputable def ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
    (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h' ⊗ 𝟙 _) ≫
        ιTensorObj (tensorObj X₁ X₂) X₃ i₁₂ i₃ j (by rw [←h', h]) := by
  subst h'
  rfl

section

variable {X₁ X₂ X₃}

/-@[ext]
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  sorry

@[ext]
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  sorry-/

end

/-@[reassoc (attr := simp)]
lemma ιTensorObj₃'_associator_hom [HasAssociator X₁ X₂ X₃] (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).hom j =
      (α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := sorry

@[reassoc (attr := simp)]
lemma ιTensorObj₃_associator_inv [HasAssociator X₁ X₂ X₃] (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).inv j =
      (α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h := sorry-/

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
noncomputable def unitTensorCandidate (i : I) : TensorCandidate tensorUnit X i :=
  TensorCandidate.mk _ _ _ (X i) (fun a b h =>
    if ha : a = 0
      then
        ((tensorUnit₀' C a ha).hom ⊗ 𝟙 (X b) : tensorUnit a ⊗ X b ⟶ 𝟙_ C ⊗ X b) ≫
          (leftUnitor (X b)).hom ≫ eqToHom (by
            obtain rfl : b = i := by rw [← h, ha, zero_add]
            rfl)
      else IsInitial.to (isInitialTensor _ _ (isInitialTensorUnitApply _ _ ha)) _)

@[simp]
lemma unitTensorCandidate_ι₀ (i : I) :
    (unitTensorCandidate X i).ι' ⟨0, i⟩ (zero_add i) =
      ((tensorUnit₀ I C).hom ⊗ (𝟙 (X i))) ≫ (λ_ (X i)).hom := by
  dsimp [unitTensorCandidate]
  rw [dif_pos rfl]
  simp

noncomputable def isColimitUnitTensorCandidate (i : I) : IsColimit (unitTensorCandidate X i) :=
  mkCofanColimit _
    (fun s => (leftUnitor (X i)).inv ≫
      ((tensorUnit₀ I C).inv ⊗ 𝟙 (X i)) ≫ s.inj ⟨⟨0, i⟩, zero_add i⟩)
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
  TensorCandidate.hasTensor _ _ _ (fun i => isColimitUnitTensorCandidate X i)

noncomputable def leftUnitor :
    tensorObj tensorUnit X ≅ X := isoMk _ _
      (fun i => ((unitTensorCandidate X i).iso (isColimitUnitTensorCandidate X i)).symm)

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
noncomputable def tensorUnitCandidate (i : I) : TensorCandidate X tensorUnit i :=
  TensorCandidate.mk _ _ _ (X i) (fun a b h =>
    if hb : b = 0
      then
        (𝟙 (X a) ⊗ (tensorUnit₀' C b hb).hom) ≫ (rightUnitor (X a)).hom ≫ eqToHom (by
          obtain rfl : a = i := by rw [← h, hb, add_zero]
          rfl)
      else IsInitial.to (tensorIsInitial _ _ (isInitialTensorUnitApply _ _ hb)) _)

@[simp]
lemma tensorUnitCandidate_ι₀ (i : I) :
    (tensorUnitCandidate X i).ι' ⟨i, 0⟩ (add_zero i) =
      (𝟙 (X i) ⊗ (tensorUnit₀ I C).hom) ≫ (rightUnitor (X i)).hom := by
  dsimp [tensorUnitCandidate]
  rw [dif_pos rfl]
  simp

noncomputable def isColimitTensorUnitCandidate (i : I) : IsColimit (tensorUnitCandidate X i) :=
  mkCofanColimit _
    (fun s => (rightUnitor (X i)).inv ≫
      (𝟙 (X i) ⊗ (tensorUnit₀ I C).inv) ≫ s.inj ⟨⟨i, 0⟩, add_zero i⟩)
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
  TensorCandidate.hasTensor _ _ _ (fun i => isColimitTensorUnitCandidate X i)

noncomputable def rightUnitor :
    tensorObj X tensorUnit ≅ X := isoMk _ _
      (fun i => ((tensorUnitCandidate X i).iso (isColimitTensorUnitCandidate X i)).symm)

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

/-lemma triangle (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]
    [HasTensor (tensorObj X₁ tensorUnit) X₂]
    [HasTensor X₁ (tensorObj tensorUnit X₂)] [HasAssociator X₁ tensorUnit X₂] :
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
    exact isInitialTensorUnitApply C k h'-/

end

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasAssociator X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂)]

/-noncomputable instance : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def f g := tensorHom_def f g
  whiskerLeft X _ _ φ := whiskerLeft X φ
  whiskerRight {_ _ φ Y} := whiskerRight φ Y
  tensorUnit' := tensorUnit
  associator X₁ X₂ X₃ := associator X₁ X₂ X₃
  associator_naturality := sorry
  leftUnitor X := leftUnitor X
  leftUnitor_naturality := leftUnitor_naturality
  rightUnitor X := rightUnitor X
  rightUnitor_naturality := rightUnitor_naturality
  tensor_comp f₁ f₂ g₁ g₂ := tensor_comp f₁ g₁ f₂ g₂
  pentagon := sorry
  triangle X₁ X₂ := sorry-/

end GradedObject

end CategoryTheory
