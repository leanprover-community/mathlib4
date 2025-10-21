/-
Copyright (c) 2019 Kim Morrison, Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon, Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Categories with chosen finite products

We introduce a class, `CartesianMonoidalCategory`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

For better defeqs, we also extend `MonoidalCategory`.

## Implementation notes

For Cartesian monoidal categories, the oplax-monoidal/monoidal/braided structure of a functor `F`
preserving finite products is uniquely determined. See the `ofChosenFiniteProducts` declarations.

We however develop the theory for any `F.OplaxMonoidal`/`F.Monoidal`/`F.Braided` instance instead of
requiring it to be the `ofChosenFiniteProducts` one. This is to avoid diamonds: Consider
e.g. `𝟭 C` and `F ⋙ G`.

In applications requiring a finite-product-preserving functor to be
oplax-monoidal/monoidal/braided, avoid `attribute [local instance] ofChosenFiniteProducts` but
instead turn on the corresponding `ofChosenFiniteProducts` declaration for that functor only.

# Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open MonoidalCategory Limits

variable (C) in
/--
An instance of `CartesianMonoidalCategory C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class CartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isTerminalTensorUnit : IsTerminal (𝟙_ C)
  /-- The first projection from the product. -/
  fst (X Y : C) : X ⊗ Y ⟶ X
  /-- The second projection from the product. -/
  snd (X Y : C) : X ⊗ Y ⟶ Y
  /-- The monoidal product is the categorical product. -/
  tensorProductIsBinaryProduct (X Y : C) : IsLimit <| BinaryFan.mk (fst X Y) (snd X Y)
  fst_def (X Y : C) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom := by cat_disch
  snd_def (X Y : C) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (λ_ Y).hom := by cat_disch

@[deprecated (since := "2025-05-15")] alias ChosenFiniteProducts := CartesianMonoidalCategory

namespace CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

section OfChosenFiniteProducts
variable (𝒯 : LimitCone (Functor.empty.{0} C)) (ℬ : ∀ X Y : C, LimitCone (pair X Y))
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C}

namespace ofChosenFiniteProducts

/-- Implementation of the tensor product for `CartesianMonoidalCategory.ofChosenFiniteProducts`. -/
abbrev tensorObj (X Y : C) : C := (ℬ X Y).cone.pt

/-- Implementation of the tensor product of morphisms for
`CartesianMonoidalCategory.ofChosenFiniteProducts`. -/
abbrev tensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj ℬ X₁ X₂ ⟶ tensorObj ℬ Y₁ Y₂ :=
  (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

lemma id_tensorHom_id (X Y : C) : tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [tensorHom]

@[deprecated (since := "2025-07-14")] alias tensor_id := id_tensorHom_id

lemma tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ = tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [tensorHom]

lemma pentagon (W X Y Z : C) :
    tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).hom ≫
          tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom =
      (BinaryFan.associatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).hom ≫
        (BinaryFan.associatorOfLimitCone ℬ W X (tensorObj ℬ Y Z)).hom := by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

lemma triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
        tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
      tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp

lemma leftUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
      (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
  simp [tensorHom]

lemma rightUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
      (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
  simp [tensorHom]

lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom =
      (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ tensorHom ℬ f₁ (tensorHom ℬ f₂ f₃) := by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

end ofChosenFiniteProducts

open ofChosenFiniteProducts

/-- Construct an instance of `CartesianMonoidalCategory C` given a terminal object and limit cones
over arbitrary pairs of objects. -/
abbrev ofChosenFiniteProducts : CartesianMonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorUnit := 𝒯.cone.pt
    tensorObj := tensorObj ℬ
    tensorHom := tensorHom ℬ
    whiskerLeft X {_ _} g := tensorHom ℬ (𝟙 X) g
    whiskerRight {_ _} f Y := tensorHom ℬ f (𝟙 Y)
    associator := BinaryFan.associatorOfLimitCone ℬ
    leftUnitor X := BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X).isLimit
    rightUnitor X := BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit
  }
  {
  toMonoidalCategory := .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id ℬ)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom ℬ)
    (pentagon := pentagon ℬ)
    (triangle := triangle 𝒯 ℬ)
    (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ)
    (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ)
    (associator_naturality := associator_naturality ℬ)
  isTerminalTensorUnit :=
    .ofUniqueHom (𝒯.isLimit.lift <| asEmptyCone ·) fun _ _ ↦ 𝒯.isLimit.hom_ext (by simp)
  fst X Y := BinaryFan.fst (ℬ X Y).cone
  snd X Y := BinaryFan.snd (ℬ X Y).cone
  tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.2)
    (fun f g m hf hg ↦
      BinaryFan.IsLimit.hom_ext (ℬ X Y).isLimit (by simpa using hf) (by simpa using hg))
  fst_def X Y := (((ℬ X 𝒯.cone.pt).isLimit.fac
    (BinaryFan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm
  snd_def X Y := (((ℬ 𝒯.cone.pt Y).isLimit.fac
    (BinaryFan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm
  }

omit 𝒯 in
/-- Construct an instance of `CartesianMonoidalCategory C` given the existence of finite products
in `C`. -/
noncomputable abbrev ofHasFiniteProducts [HasFiniteProducts C] : CartesianMonoidalCategory C :=
  .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

@[deprecated (since := "2025-05-08")] alias ofFiniteProducts := ofHasFiniteProducts

end OfChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open MonoidalCategory

/--
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C := isTerminalTensorUnit.from _

instance (X : C) : Unique (X ⟶ 𝟙_ C) := isTerminalEquivUnique _ _ isTerminalTensorUnit _

lemma default_eq_toUnit (X : C) : default = toUnit X := rfl

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
@[ext]
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _

@[simp] lemma toUnit_unit : toUnit (𝟙_ C) = 𝟙 (𝟙_ C) := toUnit_unique ..

@[reassoc (attr := simp)]
theorem comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  toUnit_unique _ _

/--
Construct a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.2

instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_fst _ _

instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_snd _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct X Y) h_fst h_snd

-- Similarly to `CategoryTheory.Limits.prod.comp_lift`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[simp]
lemma lift_fst_snd {X Y : C} : lift (fst X Y) (snd X Y) = 𝟙 (X ⊗ Y) := by ext <;> simp

@[simp]
lemma lift_comp_fst_snd {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    lift (f ≫ fst _ _) (f ≫ snd _ _) = f := by
  cat_disch

@[reassoc (attr := simp)]
lemma whiskerLeft_fst (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma whiskerLeft_snd (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f := by
  simp [snd_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]
lemma whiskerRight_fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f := by
  simp [fst_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]
lemma whiskerRight_snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ fst _ _ = fst _ _ ≫ f := by simp [tensorHom_def]

@[reassoc (attr := simp)]
lemma tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ snd _ _ = snd _ _ ≫ g := by simp [tensorHom_def]

@[reassoc (attr := simp)]
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h ⊗ₘ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
lemma lift_fst_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (fst _ _ ≫ g) (snd _ _ ≫ g') = g ⊗ₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
lemma lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) :
    lift f g ≫ (h ▷ Z) = lift (f ≫ h) g := by
  cat_disch

@[reassoc (attr := simp)]
lemma lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) :
    lift f g ≫ (Y ◁ h) = lift f (g ≫ h) := by
  cat_disch

@[reassoc (attr := simp)]
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h) := by
  cat_disch

@[reassoc (attr := simp)]
lemma lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h := by
  cat_disch

lemma leftUnitor_hom (X : C) : (λ_ X).hom = snd _ _ := by simp [snd_def]
lemma rightUnitor_hom (X : C) : (ρ_ X).hom = fst _ _ := by simp [fst_def]

@[reassoc (attr := simp)]
lemma leftUnitor_inv_fst (X : C) :
    (λ_ X).inv ≫ fst _ _ = toUnit _ := toUnit_unique _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_snd (X : C) :
    (λ_ X).inv ≫ snd _ _ = 𝟙 X := by simp [snd_def]

@[reassoc (attr := simp)]
lemma rightUnitor_inv_fst (X : C) :
    (ρ_ X).inv ≫ fst _ _ = 𝟙 X := by simp [fst_def]

@[reassoc (attr := simp)]
lemma rightUnitor_inv_snd (X : C) :
    (ρ_ X).inv ≫ snd _ _ = toUnit _ := toUnit_unique _ _

@[reassoc]
lemma whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y := by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]
lemma whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (λ_ Y).hom = snd X Y := by
  rw [← cancel_mono (λ_ Y).inv]; aesop

@[reassoc (attr := simp)]
lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
    lift f g ≫ (λ_ Y).hom = g := by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]
lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
    lift f g ≫ (ρ_ Y).hom = f := by
  rw [← Iso.eq_comp_inv]
  cat_disch

/-- Universal property of the Cartesian product: Maps to `X ⊗ Y` correspond to pairs of maps to `X`
and to `Y`. -/
@[simps]
def homEquivToProd {X Y Z : C} : (Z ⟶ X ⊗ Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

section BraidedCategory

variable [BraidedCategory C]

@[reassoc (attr := simp)]
theorem braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]
theorem braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_fst (X Y : C) : (β_ X Y).inv ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_snd (X Y : C) : (β_ X Y).inv ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]
lemma tensorμ_fst (W X Y Z : C) : tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ₘ fst Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorμ_snd (W X Y Z : C) : tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ₘ snd Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorδ_fst (W X Y Z : C) : tensorδ W X Y Z ≫ fst (W ⊗ X) (Y ⊗ Z) = fst W Y ⊗ₘ fst X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma tensorδ_snd (W X Y Z : C) : tensorδ W X Y Z ≫ snd (W ⊗ X) (Y ⊗ Z) = snd W Y ⊗ₘ snd X Z := by
  ext <;> simp [tensorδ]

theorem lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom := by cat_disch

@[simp, reassoc]
lemma lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (snd _ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' ⊗ₘ g) := by cat_disch

@[reassoc (attr := simp)]
lemma lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ X Y).hom = lift g f := by aesop

@[reassoc (attr := simp)]
lemma lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ Y X).inv = lift g f := by aesop

-- See note [lower instance priority]
instance (priority := low) toSymmetricCategory [BraidedCategory C] : SymmetricCategory C where

/-- `CartesianMonoidalCategory` implies `BraidedCategory`.
This is not an instance to prevent diamonds. -/
def _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory : BraidedCategory C where
  braiding X Y := { hom := lift (snd _ _) (fst _ _), inv := lift (snd _ _) (fst _ _) }

@[deprecated (since := "2025-05-15")]
alias _root_.CategoryTheory.BraidedCategory.ofChosenFiniteProducts :=
  BraidedCategory.ofCartesianMonoidalCategory

instance : Nonempty (BraidedCategory C) := ⟨.ofCartesianMonoidalCategory⟩

instance : Subsingleton (BraidedCategory C) where
  allEq
  | ⟨e₁, a₁, b₁, c₁, d₁⟩, ⟨e₂, a₂, b₂, c₂, d₂⟩ => by
      congr
      ext
      · exact (@braiding_hom_fst C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_fst C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm
      · exact (@braiding_hom_snd C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_snd C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm

instance : Subsingleton (SymmetricCategory C) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

end BraidedCategory

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk ⟨_, tensorProductIsBinaryProduct _ _⟩
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ C)
  hasFiniteProducts_of_has_binary_and_terminal

section CartesianMonoidalCategoryComparison

variable {D : Type u₁} [Category.{v₁} D] [CartesianMonoidalCategory D] (F : C ⥤ D)
variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

section terminalComparison

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`. -/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := toUnit _

@[reassoc]
lemma map_toUnit_comp_terminalComparison (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

open Limits

/-- If `terminalComparison F` is an Iso, then `F` preserves terminal objects. -/
lemma preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
  apply isLimitChangeEmptyCone D isTerminalTensorUnit
  exact asIso (terminalComparison F)|>.symm

/-- If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism. -/
noncomputable def preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] :
    F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalTensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalTensorUnit

@[simp]
lemma preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (preservesTerminalIso F).hom = terminalComparison F := toUnit_unique _ _

instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  cat_disch

@[simp]
lemma preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)] :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  cat_disch

end terminalComparison

section prodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`prodComparison F A B` is the canonical comparison morphism from `F (A ⊗ B)` to `F(A) ⊗ F(B)`. -/
def prodComparison (A B : C) : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B :=
  lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B) :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B) :=
  lift_snd _ _

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (fst _ _) = fst _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (snd _ _) = snd _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f ⊗ₘ g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ (F.map f ⊗ₘ F.map g) := by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

/-- Naturality of the `prodComparison` morphism in the right argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerLeft (g : B ⟶ B') :
    F.map (A ◁ g) ≫ prodComparison F A B' =
      prodComparison F A B ≫ (F.obj A ◁ F.map g) := by
  ext <;> simp [← Functor.map_comp]

/-- Naturality of the `prodComparison` morphism in the left argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerRight (f : A ⟶ A') :
    F.map (f ▷ B) ≫ prodComparison F A' B =
      prodComparison F A B ≫ (F.map f ▷ F.obj B) := by
  ext <;> simp [← Functor.map_comp]

section
variable [IsIso (prodComparison F A B)]

/-- If the product comparison morphism is an iso, its inverse is natural in both argument. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (f ⊗ₘ g) =
      (F.map f ⊗ₘ F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- If the product comparison morphism is an iso, its inverse is natural in the right argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison F A B')] :
    inv (prodComparison F A B) ≫ F.map (A ◁ g) =
      (F.obj A ◁ F.map g) ≫ inv (prodComparison F A B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerLeft]

/-- If the product comparison morphism is an iso, its inverse is natural in the left argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodComparison F A' B)] :
    inv (prodComparison F A B) ≫ F.map (f ▷ B) =
      (F.map f ▷ F.obj B) ≫ inv (prodComparison F A' B) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerRight]

end

lemma prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]
lemma prodComparison_id :
    prodComparison (𝟭 C) A B = 𝟙 (A ⊗ B) := lift_fst_snd

/-- The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonNatTrans (A : C) :
    (curriedTensor C).obj A ⋙ F ⟶ F ⋙ (curriedTensor D).obj (F.obj A) where
  app B := prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedTensor_obj_obj,
      Functor.comp_map, curriedTensor_obj_map, Category.assoc, prodComparison_fst, whiskerLeft_fst,
      prodComparison_snd, prodComparison_snd_assoc, whiskerLeft_snd, ← F.map_comp]

theorem prodComparisonNatTrans_comp :
    prodComparisonNatTrans (F ⋙ G) A = Functor.whiskerRight (prodComparisonNatTrans F A) G ≫
      Functor.whiskerLeft F (prodComparisonNatTrans G (F.obj A)) := by
  ext; simp [prodComparison_comp]

@[simp]
lemma prodComparisonNatTrans_id :
    prodComparisonNatTrans (𝟭 C) A = 𝟙 _ := by ext; simp

/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonBifunctorNatTrans :
    curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ⟶
      F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F where
  app A := prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

theorem prodComparisonBifunctorNatTrans_comp : prodComparisonBifunctorNatTrans (F ⋙ G) =
    Functor.whiskerRight
      (prodComparisonBifunctorNatTrans F) ((Functor.whiskeringRight _ _ _).obj G) ≫
        Functor.whiskerLeft F (Functor.whiskerRight (prodComparisonBifunctorNatTrans G)
          ((Functor.whiskeringLeft _ _ _).obj F)) := by
  ext; simp [prodComparison_comp]

instance (A : C) [∀ B, IsIso (prodComparison F A B)] : IsIso (prodComparisonNatTrans F A) := by
  letI : ∀ X, IsIso ((prodComparisonNatTrans F A).app X) := by assumption
  apply NatIso.isIso_of_isIso_app

instance [∀ A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F) := by
  letI : ∀ X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ ↦ by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

open Limits
section PreservesLimitPairs

section
variable (A B)
variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map fst A B, F.map (snd A B))` is a limit cone. -/
noncomputable def isLimitCartesianMonoidalCategoryOfPreservesLimits :
    IsLimit <| BinaryFan.mk (F.map (fst A B)) (F.map (snd A B)) :=
  mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _) <|
    (tensorProductIsBinaryProduct A B).ofIsoLimit <|
      isoBinaryFanMk (BinaryFan.mk (fst A B) (snd A B))

@[deprecated (since := "2025-05-15")]
alias isLimitChosenFiniteProductsOfPreservesLimits :=
  isLimitCartesianMonoidalCategoryOfPreservesLimits

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
noncomputable def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

@[simp]
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B :=
  rfl

instance isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance

@[simp] lemma prodComparisonIso_id : prodComparisonIso (𝟭 C) A B = .refl _ := by ext <;> simp

@[simp]
lemma prodComparisonIso_comp [PreservesLimit (pair A B) (F ⋙ G)]
    [PreservesLimit (pair (F.obj A) (F.obj B)) G] :
    prodComparisonIso (F ⋙ G) A B =
      G.mapIso (prodComparisonIso F A B) ≪≫ prodComparisonIso G (F.obj A) (F.obj B) := by
  ext <;> simp [CartesianMonoidalCategory.prodComparison, ← G.map_comp]

end

/-- The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes). -/
@[simps! hom inv]
noncomputable def prodComparisonNatIso (A : C) [∀ B, PreservesLimit (pair A B) F] :
    (curriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A) :=
  asIso (prodComparisonNatTrans F A)

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps! hom inv]
noncomputable def prodComparisonBifunctorNatIso [∀ A B, PreservesLimit (pair A B) F] :
    curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F :=
  asIso (prodComparisonBifunctorNatTrans F)

end PreservesLimitPairs

section ProdComparisonIso

/-- If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pair A B`. -/
lemma preservesLimit_pair_of_isIso_prodComparison (A B : C)
    [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
  apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (fst (F.obj A) (F.obj B)) (snd _ _)).extend (prodComparison F A B))
      (BinaryFan.ext (by exact Iso.refl _) ?_ ?_) |>.invFun
      (IsLimit.extendIso _ (tensorProductIsBinaryProduct (F.obj A) (F.obj B)))
  · dsimp only [BinaryFan.fst]
    simp [pairComp]
  · dsimp only [BinaryFan.snd]
    simp [pairComp]

/-- If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves limits of shape
`Discrete (WalkingPair)`. -/
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    [∀ A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

end ProdComparisonIso

end prodComparison

end CartesianMonoidalCategoryComparison

open Limits

variable {P : ObjectProperty C}

-- TODO: Introduce `ClosedUnderFiniteProducts`?
/-- The restriction of a Cartesian-monoidal category along an object property that's closed under
finite products is Cartesian-monoidal. -/
noncomputable def fullSubcategory (hP₀ : ClosedUnderLimitsOfShape (Discrete PEmpty) P)
    (hP₂ : ClosedUnderLimitsOfShape (Discrete WalkingPair) P) :
    CartesianMonoidalCategory P.FullSubcategory where
  __ := MonoidalCategory.fullSubcategory P (hP₀ isTerminalTensorUnit <| by simp)
    fun X Y hX hY ↦ hP₂ (tensorProductIsBinaryProduct X Y) (by rintro ⟨_ | _⟩ <;> simp [hX, hY])
  isTerminalTensorUnit := .ofUniqueHom (fun X ↦ toUnit X.1) fun _ _ ↦ by ext
  fst X Y := fst X.1 Y.1
  snd X Y := snd X.1 Y.1
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (lift (C := C)) (lift_fst (C := C)) (lift_snd (C := C))
      (by rintro T f g m rfl rfl; symm; exact lift_comp_fst_snd _)
  fst_def X Y := fst_def X.1 Y.1
  snd_def X Y := snd_def X.1 Y.1

end CartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory

variable
  {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]
  (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C}

open Functor.LaxMonoidal Functor.OplaxMonoidal
open Limits (PreservesFiniteProducts)

namespace Functor.OplaxMonoidal
variable [F.OplaxMonoidal]

lemma η_of_cartesianMonoidalCategory :
    η F = CartesianMonoidalCategory.terminalComparison F := toUnit_unique ..

@[reassoc (attr := simp)]
lemma δ_fst (X Y : C) :
    δ F X Y ≫ fst _ _ = F.map (fst _ _) := by
  trans F.map (X ◁ toUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_fst _ (F.map (toUnit Y)), δ_natural_right_assoc]
    simp [← OplaxMonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]
lemma δ_snd (X Y : C) :
    δ F X Y ≫ snd _ _ = F.map (snd _ _) := by
  trans F.map (toUnit X ▷ Y) ≫ F.map (λ_ Y).hom
  · rw [← whiskerRight_snd (F.map (toUnit X)), δ_natural_left_assoc]
    simp [← OplaxMonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]
lemma lift_δ (f : X ⟶ Y) (g : X ⟶ Z) : F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g) := by
  ext <;> simp [← map_comp]

lemma δ_of_cartesianMonoidalCategory (X Y : C) :
    δ F X Y = CartesianMonoidalCategory.prodComparison F X Y := by cat_disch

variable [PreservesFiniteProducts F]

instance : IsIso (η F) :=
  η_of_cartesianMonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F

instance (X Y : C) : IsIso (δ F X Y) :=
  δ_of_cartesianMonoidalCategory F X Y ▸ isIso_prodComparison_of_preservesLimit_pair F X Y

omit [F.OplaxMonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax monoidal structure on
the identity and composition of functors. -/
def ofChosenFiniteProducts (F : C ⥤ D) : F.OplaxMonoidal where
  η := terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left f X := by ext <;> simp [← Functor.map_comp]
  δ_natural_right X g := by ext <;> simp [← Functor.map_comp]
  oplax_associativity _ _ _ := by ext <;> simp [← Functor.map_comp]
  oplax_left_unitality _ := by ext; simp [← Functor.map_comp]
  oplax_right_unitality _ := by ext; simp [← Functor.map_comp]

omit [F.OplaxMonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal in a unique way. -/
instance : Subsingleton F.OplaxMonoidal where
  allEq a b := by
    ext1
    · exact toUnit_unique _ _
    · ext1; ext1; rw [δ_of_cartesianMonoidalCategory, δ_of_cartesianMonoidalCategory]

end OplaxMonoidal

namespace Monoidal
variable [F.Monoidal] [G.Monoidal]

@[reassoc (attr := simp)]
lemma toUnit_ε (X : C) : toUnit (F.obj X) ≫ ε F = F.map (toUnit X) := by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]
lemma lift_μ (f : X ⟶ Y) (g : X ⟶ Z) : lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_fst (X Y : C) : μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_snd (X Y : C) : μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
@[reassoc]
lemma μ_comp [(F ⋙ G).Monoidal] (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

variable [PreservesFiniteProducts F]

lemma ε_of_cartesianMonoidalCategory : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext

lemma μ_of_cartesianMonoidalCategory (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianMonoidalCategory F X Y

attribute [local instance] Functor.OplaxMonoidal.ofChosenFiniteProducts in
omit [F.Monoidal] in
/-- A finite-product-preserving functor between Cartesian monoidal categories is monoidal.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Monoidal :=
  .ofOplaxMonoidal F

instance : Subsingleton F.Monoidal := (toOplaxMonoidal_injective F).subsingleton

end Monoidal

namespace Monoidal

instance [F.Monoidal] : PreservesFiniteProducts F :=
  have (A B : _) : IsIso (CartesianMonoidalCategory.prodComparison F A B) :=
    δ_of_cartesianMonoidalCategory F A B ▸ inferInstance
  have : IsIso (CartesianMonoidalCategory.terminalComparison F) :=
    η_of_cartesianMonoidalCategory F ▸ inferInstance
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison F
  have := preservesLimit_empty_of_isIso_terminalComparison F
  have := Limits.preservesLimitsOfShape_pempty_of_preservesTerminal F
  .of_preserves_binary_and_terminal _

attribute [local instance] OplaxMonoidal.ofChosenFiniteProducts in
/--
A functor between Cartesian monoidal categories is monoidal iff it preserves finite products.
-/
lemma nonempty_monoidal_iff_preservesFiniteProducts :
    Nonempty F.Monoidal ↔ PreservesFiniteProducts F :=
  ⟨fun ⟨_⟩ ↦ inferInstance, fun _ ↦ ⟨ofChosenFiniteProducts F⟩⟩

end Monoidal

namespace Braided
variable [BraidedCategory C] [BraidedCategory D]

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
/-- A finite-product-preserving functor between Cartesian monoidal categories is braided.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Braided where
  braided X Y := by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

instance : Subsingleton F.Braided := (Braided.toMonoidal_injective F).subsingleton

end Braided

@[deprecated (since := "2025-04-24")]
alias oplaxMonoidalOfChosenFiniteProducts := OplaxMonoidal.ofChosenFiniteProducts

@[deprecated (since := "2025-04-24")]
alias monoidalOfChosenFiniteProducts := Monoidal.ofChosenFiniteProducts

@[deprecated (since := "2025-04-24")]
alias braidedOfChosenFiniteProducts := Braided.ofChosenFiniteProducts

namespace EssImageSubcategory
variable [F.Full] [F.Faithful] [PreservesFiniteProducts F] {T X Y Z : F.EssImageSubcategory}

@[simps!]
noncomputable instance instCartesianMonoidalCategory :
     CartesianMonoidalCategory F.EssImageSubcategory :=
  .fullSubcategory (.essImage _) (.essImage _)

lemma tensor_obj (X Y : F.EssImageSubcategory) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = lift (T := T.1) f g := rfl

lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl

lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := rfl

lemma toUnit_def (X : F.EssImageSubcategory) : toUnit X = toUnit X.obj := toUnit_unique ..

end Functor.EssImageSubcategory

namespace NatTrans
variable (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]

instance IsMonoidal.of_cartesianMonoidalCategory (α : F ⟶ G) : IsMonoidal α where
  unit := (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply CartesianMonoidalCategory.hom_ext <;> simp

end NatTrans

end CategoryTheory
