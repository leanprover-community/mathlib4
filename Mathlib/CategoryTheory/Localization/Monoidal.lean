/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Localization.Trifunctor
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Localization of monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure: this means `W`
is multiplicative and stable by left and right whiskerings (this is
the type class `W.IsMonoidal`). Let `L : C ⥤ D` be a localization functor
for `W`. In the file, we shall construct a monoidal category structure
on `D` such that the localization functor is monoidal. The structure
is actually defined on a type synonym `LocalizedMonoidal L W ε`.
Here, the data `ε : L.obj (𝟙_ C) ≅ unit` is an isomorphism to some
object `unit : D` which allows the user to provide a preferred choice
of a unit object.

-/

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

/-- A class of morphisms `W` in a monoidal category is monoidal if it is multiplicative
and stable under left and right whiskering. Under this condition, the localized
category can be equipped with a monoidal category structure, see `LocalizedMonoidal`. -/
class IsMonoidal extends W.IsMultiplicative : Prop where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

variable [W.IsMonoidal]

lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  IsMonoidal.whiskerLeft _ _ hg

lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  IsMonoidal.whiskerRight _ hf Y

lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f ⊗ g) := by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

end MorphismProperty

/-- Given a monoidal category `C`, a localization functor `L : C ⥤ D` with respect
to `W : MorphismProperty C` which satisfies `W.IsMonoidal`, and a choice
of object `unit : D` with an isomorphism `L.obj (𝟙_ C) ≅ unit`, this is a
type synonym for `D` on which we define the localized monoidal category structure. -/
@[nolint unusedArguments]
def LocalizedMonoidal (L : C ⥤ D) (W : MorphismProperty C)
    [W.IsMonoidal] [L.IsLocalization W] {unit : D} (_ : L.obj (𝟙_ C) ≅ unit) :=
  D

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

namespace Localization

instance : Category (LocalizedMonoidal L W ε) :=
  inferInstanceAs (Category D)

namespace Monoidal

/-- The monoidal functor from a monoidal category `C` to
its localization `LocalizedMonoidal L W ε`. -/
def toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε := L

/-- The isomorphism `ε : L.obj (𝟙_ C) ≅ unit`,
as `(toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit`. -/
abbrev ε' : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit := ε

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

lemma isInvertedBy₂ :
    MorphismProperty.IsInvertedBy₂ W W
      (curriedTensor C ⋙ (whiskeringRight C C D).obj L') := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

/-- The localized tensor product, as a bifunctor. -/
noncomputable def tensorBifunctor :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

noncomputable instance : Lifting₂ L' L' W W (curriedTensor C ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε) :=
  inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

/-- The bifunctor `tensorBifunctor` on `LocalizedMonoidal L W ε` is induced by
`curriedTensor C`. -/
noncomputable abbrev tensorBifunctorIso :
    (((whiskeringLeft₂ D).obj L').obj L').obj (tensorBifunctor L W ε) ≅
      (Functor.postcompose₂.obj L').obj (curriedTensor C) :=
  Lifting₂.iso L' L' W W (curriedTensor C ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε)

noncomputable instance (X : C) :
    Lifting L' W (tensorLeft X ⋙ L') ((tensorBifunctor L W ε).obj ((L').obj X)) := by
  apply Lifting₂.liftingLift₂ (hF := isInvertedBy₂ L W ε)

noncomputable instance (Y : C) :
    Lifting L' W (tensorRight Y ⋙ L') ((tensorBifunctor L W ε).flip.obj ((L').obj Y)) := by
  apply Lifting₂.liftingLift₂Flip (hF := isInvertedBy₂ L W ε)

/-- The left unitor in the localized monoidal category `LocalizedMonoidal L W ε`. -/
noncomputable def leftUnitor : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).obj ((L').obj (𝟙_ _))) _
        (isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- The right unitor in the localized monoidal category `LocalizedMonoidal L W ε`. -/
noncomputable def rightUnitor : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- The associator in the localized monoidal category `LocalizedMonoidal L W ε`. -/
noncomputable def associator :
    bifunctorComp₁₂ (tensorBifunctor L W ε) (tensorBifunctor L W ε) ≅
      bifunctorComp₂₃ (tensorBifunctor L W ε) (tensorBifunctor L W ε) :=
  Localization.associator L' L' L' L' L' L' W W W W W
    (curriedAssociatorNatIso C) (tensorBifunctor L W ε) (tensorBifunctor L W ε)
    (tensorBifunctor L W ε) (tensorBifunctor L W ε)

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (LocalizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W ε).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W ε).map f).app Y
  tensorUnit := unit
  associator X Y Z := (((associator L W ε).app X).app Y).app Z
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

/-- The compatibility isomorphism of the monoidal functor `toMonoidalCategory L W ε`
with respect to the tensor product. -/
noncomputable def μ (X Y : C) : (L').obj X ⊗ (L').obj Y ≅ (L').obj (X ⊗ Y) :=
  ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]
lemma μ_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom =
      (μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y) :=
  NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]
lemma μ_inv_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (μ L W ε X₁ Y).inv ≫ (L').map f ▷ (L').obj Y =
      (L').map (f ▷ Y) ≫ (μ L W ε X₂ Y).inv := by
  simp [Iso.eq_comp_inv]

@[reassoc (attr := simp)]
lemma μ_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
      (μ L W ε X Y₁).hom ≫ (L').map (X ◁ g) :=
  ((tensorBifunctorIso L W ε).hom.app X).naturality g

@[reassoc (attr := simp)]
lemma μ_inv_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (μ L W ε X Y₁).inv ≫ (L').obj X ◁ (L').map g =
      (L').map (X ◁ g) ≫ (μ L W ε X Y₂).inv := by
  simp [Iso.eq_comp_inv]

lemma leftUnitor_hom_app (Y : C) :
    (λ_ ((L').obj Y)).hom =
      (ε' L W ε).inv ▷ (L').obj Y ≫ (μ _ _ _ _ _).hom ≫ (L').map (λ_ Y).hom := by
  dsimp [monoidalCategoryStruct, leftUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε  _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

lemma rightUnitor_hom_app (X : C) :
    (ρ_ ((L').obj X)).hom =
      (L').obj X ◁ (ε' L W ε).inv ≫ (μ _ _ _ _ _).hom ≫
        (L').map (ρ_ X).hom := by
  dsimp [monoidalCategoryStruct, rightUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε  _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

lemma associator_hom_app (X₁ X₂ X₃ : C) :
    (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom =
      ((μ L W ε _ _).hom ⊗ 𝟙 _) ≫ (μ L W ε _ _).hom ≫ (L').map (α_ X₁ X₂ X₃).hom ≫
        (μ L W ε  _ _).inv ≫ (𝟙 _ ⊗ (μ L W ε  _ _).inv) := by
  dsimp [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl

lemma id_tensorHom (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ f = X ◁ f := by
  simp [monoidalCategoryStruct]

lemma tensorHom_id {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) :
    f ⊗ 𝟙 Y = f ▷ Y := by
  simp [monoidalCategoryStruct]

@[reassoc]
lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
  simp [monoidalCategoryStruct]

lemma tensor_id (X₁ X₂ : LocalizedMonoidal L W ε) : 𝟙 X₁ ⊗ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by
  simp [monoidalCategoryStruct]

@[reassoc]
theorem whiskerLeft_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g := by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc]
theorem whiskerRight_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g) ▷ Q = f ▷ Q ≫ g ▷ Q := by
  simp only [← tensorHom_id, ← tensor_comp, comp_id]

lemma whiskerLeft_id (X Y : LocalizedMonoidal L W ε) :
    X ◁ (𝟙 Y) = 𝟙 _ := by simp [monoidalCategoryStruct]

lemma whiskerRight_id (X Y : LocalizedMonoidal L W ε) :
    (𝟙 X) ▷ Y = 𝟙 _ := by simp [monoidalCategoryStruct]

@[reassoc]
lemma whisker_exchange {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ Z) :
    Q ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

@[reassoc]
lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁, assoc, reassoc_of% h₂, reassoc_of% h₃]

@[reassoc]
lemma associator_naturality₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁) :
    ((f₁ ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ▷ (X₂ ⊗ X₃)) := by
  simp only [← tensorHom_id, associator_naturality, Iso.cancel_iso_hom_left, tensor_id]

@[reassoc]
lemma associator_naturality₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂) :
    ((X₁ ◁ f₂) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (f₂ ▷ X₃)) := by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]
lemma associator_naturality₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃) :
    ((X₁ ⊗ X₂) ◁ f₃) ≫ (α_ X₁ X₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (X₂ ◁ f₃)) := by
  simp only [← id_tensorHom, ← tensor_id, associator_naturality]

end Monoidal

end CategoryTheory
