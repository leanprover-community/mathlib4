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

We introduce a class, `CocartesianMonoidalCategory`, which bundles explicit choices
for an initial object and binary coproducts in a category `C`.
This is primarily useful for categories which have finite coproducts with good
definitional properties, such as the category of types.

For better defeqs, we also extend `AddMonoidalCategory`.

-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open AddMonoidalCategory Limits

variable (C) in
/--
An instance of `CocartesianMonoidalCategory C` bundles an explicit choice of a binary
coproduct of two objects of `C`, and an initial object in `C`.

Users should use the additive monoidal notation: `X ⊕ₒ Y` for the coproduct and `𝟘_ C` for
the initial object.
-/
class CocartesianMonoidalCategory (C : Type u) [Category.{v} C] extends AddMonoidalCategory C where
  /-- The additive unit is an initial object. -/
  isInitialAddUnit : IsInitial (𝟘_ C)
  /-- The first injection into the coproduct. -/
  inl (X Y : C) : X ⟶ X ⊕ₒ Y
  /-- The second injection into the coproduct. -/
  inr (X Y : C) : Y ⟶ X ⊕ₒ Y
  /-- The monoidal product is the categorical product. -/
  addHomIsBinaryCoproduct (X Y : C) : IsColimit <| BinaryCofan.mk (inl X Y) (inr X Y)
  inl_def (X Y : C) : inl X Y = (ρ⁺ X).inv ≫ X ◁⁺ isInitialAddUnit.to Y := by cat_disch
  inr_def (X Y : C) : inr X Y = (λ⁺ Y).inv ≫ isInitialAddUnit.to X ▷⁺ Y := by cat_disch

namespace CocartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

section OfChosenFiniteCoproducts
variable (𝒯 : ColimitCocone (Functor.empty.{0} C)) (ℬ : ∀ X Y : C, ColimitCocone (pair X Y))
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C}

namespace ofChosenFiniteCoproducts

/-- Implementation of addition for `CocartesianMonoidalCategory.ofChosenFiniteCoproducts`. -/
abbrev addObj (X Y : C) : C := (ℬ X Y).cocone.pt

/-- Implementation of the addition of morphisms for
`CocartesianMonoidalCategory.ofChosenFiniteCoproducts`. -/
abbrev addHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : addObj ℬ X₁ X₂ ⟶ addObj ℬ Y₁ Y₂ :=
  (BinaryCofan.IsColimit.desc' (ℬ X₁ X₂).isColimit
      (f ≫ (ℬ Y₁ Y₂).cocone.ι.app ⟨.left⟩)
      (g ≫ ((ℬ Y₁ Y₂).cocone.ι.app ⟨.right⟩ : Y₂ ⟶ (ℬ Y₁ Y₂).cocone.pt))).val

lemma id_addHom_id (X Y : C) : addHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (addObj ℬ X Y) :=
  (ℬ _ _).isColimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [addHom]

lemma addHom_comp_addHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    addHom ℬ f₁ f₂ ≫ addHom ℬ g₁ g₂ = addHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  (ℬ _ _).isColimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [addHom]

-- TODO: BinaryCofan.{associatorOfColimitCocone, leftUnitor, rightUnitor}
-- lemma pentagon (W X Y Z : C) :
--     tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).hom (𝟙 Z) ≫
--         (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).hom ≫
--           tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom =
--       (BinaryFan.associatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).hom ≫
--         (BinaryFan.associatorOfLimitCone ℬ W X (tensorObj ℬ Y Z)).hom := by
--   dsimp [tensorHom]
--   apply (ℬ _ _).isLimit.hom_ext
--   rintro ⟨_ | _⟩
--   · simp
--   apply (ℬ _ _).isLimit.hom_ext
--   rintro ⟨_ | _⟩
--   · simp
--   apply (ℬ _ _).isLimit.hom_ext
--   rintro ⟨_ | _⟩ <;> simp

-- lemma triangle (X Y : C) :
--     (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
--         tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
--       tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) :=
--   (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp

-- lemma leftUnitor_naturality (f : X₁ ⟶ X₂) :
--     tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
--       (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
--   simp [tensorHom]

-- lemma rightUnitor_naturality (f : X₁ ⟶ X₂) :
--     tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit
--       (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
--       (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
--   simp [tensorHom]

-- lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
--     tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom =
--       (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ tensorHom ℬ f₁ (tensorHom ℬ f₂ f₃) := by
--   dsimp [tensorHom]
--   apply (ℬ _ _).isLimit.hom_ext
--   rintro ⟨_ | _⟩
--   · simp
--   apply (ℬ _ _).isLimit.hom_ext
--   rintro ⟨_ | _⟩ <;> simp

end ofChosenFiniteCoproducts

-- open ofChosenFiniteCoproducts

-- /-- Construct an instance of `CocartesianMonoidalCategory C` given a terminal object and colimit
-- cocones over arbitrary pairs of objects. -/
-- abbrev ofChosenFiniteProducts : CocartesianMonoidalCategory C :=
--   letI : MonoidalCategoryStruct C := {
--     tensorUnit := 𝒯.cocone.pt
--     tensorObj := addObj ℬ
--     tensorHom := addHom ℬ
--     whiskerLeft X {_ _} g := addHom ℬ (𝟙 X) g
--     whiskerRight {_ _} f Y := addHom ℬ f (𝟙 Y)
--     associator := BinaryFan.associatorOfLimitCone ℬ
--     leftUnitor X := BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X).isLimit
--     rightUnitor X := BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit
--   }
--   {
--   toAddMonoidalCategory := .ofTensorHom
--     (id_tensorHom_id := id_tensorHom_id ℬ)
--     (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom ℬ)
--     (pentagon := pentagon ℬ)
--     (triangle := triangle 𝒯 ℬ)
--     (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ)
--     (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ)
--     (associator_naturality := associator_naturality ℬ)
--   isTerminalTensorUnit :=
--     .ofUniqueHom (𝒯.isLimit.lift <| asEmptyCone ·) fun _ _ ↦ 𝒯.isLimit.hom_ext (by simp)
--   fst X Y := BinaryFan.fst (ℬ X Y).cone
--   snd X Y := BinaryFan.snd (ℬ X Y).cone
--   tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
--     (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).1)
--     (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.1)
--     (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.2)
--     (fun f g m hf hg ↦
--       BinaryFan.IsLimit.hom_ext (ℬ X Y).isLimit (by simpa using hf) (by simpa using hg))
--   fst_def X Y := (((ℬ X 𝒯.cone.pt).isLimit.fac
--     (BinaryFan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm
--   snd_def X Y := (((ℬ 𝒯.cone.pt Y).isLimit.fac
--     (BinaryFan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm
--   }

-- omit 𝒯 in
-- /-- Construct an instance of `CartesianMonoidalCategory C` given the existence of finite products
-- in `C`. -/
-- noncomputable abbrev ofHasFiniteCoproducts [HasFiniteCoproducts C]
--   : CocartesianMonoidalCategory C
--   := .ofChosenFiniteCoproducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

end OfChosenFiniteCoproducts

variable {C : Type u} [Category.{v} C] [CocartesianMonoidalCategory C]

open AddMonoidalCategory

/--
The unique map from the initial object.
-/
def fromUnit (X : C) : 𝟘_ C ⟶ X := isInitialAddUnit.to _

instance (X : C) : Unique (𝟘_ C ⟶ X) := isInitialEquivUnique _ _ isInitialAddUnit _

lemma default_eq_fromUnit (X : C) : default = fromUnit X := rfl

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply fromUnit_unique` forcing
lean to do the necessary elaboration.
-/
@[ext]
lemma fromUnit_unique {X : C} (f g : 𝟘_ _ ⟶ X) : f = g :=
  Subsingleton.elim _ _

@[simp] lemma fromUnit_unit : fromUnit (𝟘_ C) = 𝟙 (𝟘_ C) := fromUnit_unique ..

@[reassoc (attr := simp)]
theorem fromUnit_comp {X Y : C} (f : X ⟶ Y) : fromUnit X ≫ f = fromUnit Y :=
  fromUnit_unique _ _

/--
Construct a morphism from the coproduct given its two components.
-/
def desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⊕ₒ Y ⟶ T :=
  (BinaryCofan.IsColimit.desc' (addHomIsBinaryCoproduct X Y) f g).1

@[reassoc (attr := simp)]
lemma inl_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inl _ _ ≫ desc f g = f :=
  (BinaryCofan.IsColimit.desc' (addHomIsBinaryCoproduct X Y) f g).2.1

@[reassoc (attr := simp)]
lemma inr_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inr _ _ ≫ desc f g = g :=
  (BinaryCofan.IsColimit.desc' (addHomIsBinaryCoproduct X Y) f g).2.2

instance epi_desc_of_epi_left {W X Y : C} (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (desc f g) :=
  epi_of_epi_fac <| inl_desc _ _

instance epi_desc_of_epi_right {W X Y : C} (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (desc f g) :=
  epi_of_epi_fac <| inr_desc _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : X ⊕ₒ Y ⟶ T)
    (h_fst : inl _ _ ≫ f = inl _ _ ≫ g)
    (h_snd : inr _ _ ≫ f = inr _ _ ≫ g) :
    f = g :=
  BinaryCofan.IsColimit.hom_ext (addHomIsBinaryCoproduct X Y) h_fst h_snd

@[reassoc, simp]
lemma comp_lift {V W X Y : C} (f : X ⟶ W) (g : Y ⟶ W) (h : W ⟶ V) :
    desc f g ≫ h = desc (f ≫ h) (g ≫ h) := by ext <;> simp

@[simp]
lemma desc_inl_inr {X Y : C} : desc (inl X Y) (inr X Y) = 𝟙 (X ⊕ₒ Y) := by ext <;> simp

@[simp]
lemma desc_inl_inr_comp {X Y Z : C} (f : X ⊕ₒ Y ⟶ Z) :
    desc (inl _ _ ≫ f) (inr _ _ ≫ f) = f := by
  cat_disch

@[reassoc (attr := simp)]
lemma inl_addWhiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : inl _ _ ≫ X ◁⁺ f = inl _ _ := by
  simp [inl_def, <-addWhiskerLeft_comp]

@[reassoc (attr := simp)]
lemma inr_addWhiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : inr _ _ ≫ X ◁⁺ f = f ≫ inr _ _ := by
  simp [inr_def, <-addWhisker_exchange]

@[reassoc (attr := simp)]
lemma inl_addWhiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : inl _ _ ≫ f ▷⁺ Z = f ≫ inl _ _ := by
  simp [inl_def, addWhisker_exchange]

@[reassoc (attr := simp)]
lemma inr_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : inr _ _ ≫ f ▷⁺ Z = inr _ _ := by
  simp [inr_def, ←comp_addWhiskerRight]

@[reassoc (attr := simp)]
lemma inl_addHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inl _ _ ≫ (f ⊕ₘ g) = f ≫ inl _ _ := by simp [addHom_def]

@[reassoc (attr := simp)]
lemma inr_addHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inr _ _ ≫ (f ⊕ₘ g) = g ≫ inr _ _ := by simp [addHom_def]

@[reassoc (attr := simp)]
lemma map_desc {V W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ V) (k : Z ⟶ V) :
    (f ⊕ₘ g) ≫ desc h k = desc (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
lemma desc_comp_inl_comp_inr {W X Y Z : C} (g : X ⟶ W) (g' : Z ⟶ Y) :
    desc (g ≫ inl _ _) (g' ≫ inr _ _) = g ⊕ₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
lemma whiskerRight_desc {X Y Z W : C} (f : Y ⟶ W) (g : W ⟶ X) (h : Z ⟶ X) :
    (f ▷⁺ Z) ≫ desc g h = desc (f ≫ g) h := by
  cat_disch

-- @[reassoc (attr := simp)]
-- lemma whiskerLeft_desc {X Y Z W : C} (f : Z ⟶ W) (g : Y ⟶ X) (h : W ⟶ X) :
--     (Y ◁⁺ f) ≫ desc g h = desc g (f ≫ h) := by
--   cat_disch

-- @[reassoc (attr := simp)]
-- lemma inr_addAssociator_hom (X Y Z : C) :
--     inr _ _ ≫ (α⁺ X Y Z).hom = inr _ _ ≫ inr _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma inr_inl_addAssociator_hom (X Y Z : C) :
--     inr _ _ ≫ inl _ _ ≫ (α⁺ X Y Z).hom = inl _ _ ≫ inr _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma inl_inl_addAssociator_hom (X Y Z : C) :
--     inl _ _ ≫ inl _ _ ≫ (α⁺ X Y Z).hom = inl _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma inl_addAssociator_inv (X Y Z : C) :
--     inl _ _ ≫ (α⁺ X Y Z).inv = inl _ _ ≫ inl _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma inl_inr_addAssociator_inv (X Y Z : C) :
--     inl _ _ ≫ inr _ _ ≫ (α⁺ X Y Z).inv = inr _ _ ≫ inl _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma inr_inr_addAssociator_inv (X Y Z : C) :
--     inr _ _ ≫ inr _ _ ≫ (α⁺ X Y Z).inv = inr _ _ := by sorry

-- @[reassoc (attr := simp)]
-- lemma addAssociator_hom_desc_desc {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X) (h : W ⟶ X) :
--     (α⁺ Y Z W).hom ≫ desc f (desc g h) = desc (desc f g) h := by
--   cat_disch

-- @[reassoc (attr := simp)]
-- lemma addAssociator_inv_desc_desc {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X) (h : W ⟶ X) :
--     (α⁺ Y Z W).inv ≫ desc (desc f g) h = desc f (desc g h) := by
--   cat_disch

lemma addLeftUnitor_inv (X : C) : (λ⁺ X).inv = inr _ _ := by simp [inr_def]
lemma addRightUnitor_inv (X : C) : (ρ⁺ X).inv = inl _ _ := by simp [inl_def]

@[reassoc (attr := simp)]
lemma inl_leftUnitor_hom (X : C) :
    inl _ _ ≫ (λ⁺ X).hom = fromUnit _ := fromUnit_unique _ _

@[reassoc (attr := simp)]
lemma inr_leftUnitor_hom (X : C) :
    inr _ _ ≫ (λ⁺ X).hom = 𝟙 X := by simp [inr_def]

@[reassoc (attr := simp)]
lemma inl_rightUnitor_hom (X : C) :
    inl _ _ ≫ (ρ⁺ X).hom = 𝟙 X := by simp [inl_def]

@[reassoc (attr := simp)]
lemma inr_rightUnitor_hom (X : C) :
    inr _ _ ≫ (ρ⁺ X).hom = fromUnit _ := fromUnit_unique _ _

-- @[reassoc]
-- lemma whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).hom
-- = fst X Y := by
--   rw [← cancel_mono (ρ_ X).inv]; aesop

-- @[reassoc]
-- lemma whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (λ_ Y).hom
-- = snd X Y := by
--   rw [← cancel_mono (λ_ Y).inv]; aesop

-- @[reassoc (attr := simp)]
-- lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
--     lift f g ≫ (λ_ Y).hom = g := by
--   rw [← Iso.eq_comp_inv]
--   cat_disch

-- @[reassoc (attr := simp)]
-- lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
--     lift f g ≫ (ρ_ Y).hom = f := by
--   rw [← Iso.eq_comp_inv]
--   cat_disch

/-- Universal property of the coproduct: Maps from `X ⊕ Y` correspond to pairs of maps from `X`
and from `Y`. -/
@[simps]
def homEquivToProd {X Y Z : C} : (X ⊕ₒ Y ⟶ Z) ≃ (X ⟶ Z) × (Y ⟶ Z) where
  toFun f := ⟨inl _ _ ≫ f, inr _ _ ≫ f⟩
  invFun f := desc f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

instance (priority := 100) : Limits.HasFiniteCoproducts C :=
  letI : ∀ (X Y : C), Limits.HasColimit (Limits.pair X Y) := fun _ _ =>
    .mk ⟨_, addHomIsBinaryCoproduct _ _⟩
  letI : Limits.HasBinaryCoproducts C := Limits.hasBinaryCoproducts_of_hasColimit_pair _
  letI : Limits.HasInitial C := Limits.hasInitial_of_unique (𝟘_ C)
  hasFiniteCoproducts_of_has_binary_and_initial

variable {P : ObjectProperty C}

-- TODO: Introduce `ClosedUnderFiniteProducts`?
/-- The restriction of a Cartesian-monoidal category along an object property that's closed under
finite products is Cartesian-monoidal. -/
noncomputable def fullSubcategory (hP₀ : ClosedUnderColimitsOfShape (Discrete PEmpty) P)
    (hP₂ : ClosedUnderColimitsOfShape (Discrete WalkingPair) P) :
    CocartesianMonoidalCategory P.FullSubcategory where
  __ := AddMonoidalCategory.fullSubcategory P (hP₀ isInitialAddUnit <| by simp)
    fun X Y hX hY ↦ hP₂ (addHomIsBinaryCoproduct X Y) (by rintro ⟨_ | _⟩ <;> simp [hX, hY])
  isInitialAddUnit := .ofUniqueHom (fun X ↦ fromUnit X.1) fun _ _ ↦ by ext
  inl X Y := inl X.1 Y.1
  inr X Y := inr X.1 Y.1
  addHomIsBinaryCoproduct X Y :=
    BinaryCofan.IsColimit.mk _ (desc (C := C)) (inl_desc (C := C)) (inr_desc (C := C))
      (by rintro T f g m rfl rfl; symm; exact desc_inl_inr_comp _)
  inl_def X Y := inl_def X.1 Y.1
  inr_def X Y := inr_def X.1 Y.1

end CocartesianMonoidalCategory

end CategoryTheory
