import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Monoidal.Category

namespace CategoryTheory

open MonoidalCategory

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

class Monoidal extends W.IsMultiplicative : Prop where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

variable [W.Monoidal]

lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  Monoidal.whiskerLeft _ _ hg

lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  Monoidal.whiskerRight _ hf Y

lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f ⊗ g) := by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

end MorphismProperty

namespace Localization

@[nolint unusedArguments]
def localizedMonoidal (L : C ⥤ D) (W : MorphismProperty C)
    [W.Monoidal] [L.IsLocalization W] {unit : D}
    (_ : L.obj (𝟙_ C) ≅ unit) := D

variable [W.Monoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

instance : Category (localizedMonoidal L W ε) :=
  inferInstanceAs (Category D)

namespace Monoidal

lemma isInvertedBy₂ :
    MorphismProperty.IsInvertedBy₂ W W
      ((whiskeringRight₂' _ _ L).obj (curriedTensor C)) := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

noncomputable abbrev tensorBifunctor : D ⥤ D ⥤ D :=
  Localization.lift₂ _ (isInvertedBy₂ L W) L L

noncomputable instance (X : C) :
    Lifting L W (tensorLeft X ⋙ L) ((tensorBifunctor L W).obj (L.obj X)) :=
  inferInstanceAs (Lifting L W ((((whiskeringRight₂' _ _ L).obj (curriedTensor C))).obj X)
    ((tensorBifunctor L W).obj (L.obj X)))

noncomputable instance (Y : C) :
    Lifting L W (tensorRight Y ⋙ L) ((tensorBifunctor L W).flip.obj (L.obj Y)) :=
  inferInstanceAs (Lifting L W ((((whiskeringRight₂' _ _ L).obj (curriedTensor C))).flip.obj Y)
    ((tensorBifunctor L W).flip.obj (L.obj Y)))

noncomputable def leftUnitor : (tensorBifunctor L W).obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W).mapIso ε.symm ≪≫
    Localization.liftNatIso L W (tensorLeft (𝟙_ C) ⋙ L) L _ _
      (isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

noncomputable def rightUnitor : (tensorBifunctor L W).flip.obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L W (tensorRight (𝟙_ C) ⋙ L) L _ _
      (isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (localizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W).map f).app Y
  tensorUnit := unit
  associator := sorry -- needs localization of trifunctors
  leftUnitor X := (leftUnitor L W ε).app X
  rightUnitor Y := (rightUnitor L W ε).app Y

noncomputable instance :
    MonoidalCategory (localizedMonoidal L W ε) where
  tensorHom_def := by intros; simp [monoidalCategoryStruct]
  tensor_id := by intros; simp [monoidalCategoryStruct]
  tensor_comp := by intros; simp [monoidalCategoryStruct]
  whiskerLeft_id := by intros; simp [monoidalCategoryStruct]
  id_whiskerRight := by intros; simp [monoidalCategoryStruct]
  associator_naturality := sorry
  leftUnitor_naturality := by intros; simp [monoidalCategoryStruct]
  rightUnitor_naturality f := (rightUnitor L W ε).hom.naturality f
  pentagon := sorry
  triangle := sorry

end Monoidal

end Localization

namespace Localization

end Localization

end CategoryTheory
