import Mathlib.CategoryTheory.Localization.Predicate
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

variable [W.Monoidal]

--@[nolint unusedArguments]
--abbrev localizedMonoidal (_ : C ⥤ D) (_ : MorphismProperty C) := D
--
--#check

lemma isInvertedBy₂ :

def tensorBifunctor : D ⥤ D ⥤ D := by
  sorry

--instance : MonoidalCategoryStruct D where
--  tensorObj := by
--    sorry
--  whiskerLeft := sorry
--  whiskerRight := sorry
--  tensorUnit := sorry
--  associator := sorry
--  leftUnitor := sorry
--  rightUnitor := sorry


namespace Localization

end Localization

end CategoryTheory
