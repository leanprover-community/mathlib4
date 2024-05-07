import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Monoidal.Functor

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

@[nolint unusedArguments]
def LocalizedMonoidal (L : C ⥤ D) (W : MorphismProperty C)
    [W.Monoidal] [L.IsLocalization W] {unit : D}
    (_ : L.obj (𝟙_ C) ≅ unit) := D

variable [W.Monoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

namespace Localization

instance : Category (LocalizedMonoidal L W ε) :=
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

noncomputable abbrev tensorBifunctorIso :
    (whiskeringLeft₂ObjObj L L D).obj (tensorBifunctor L W) ≅
      (whiskeringRight₂' C C L).obj (curriedTensor C) :=
  Lifting₂.iso L L W W (((whiskeringRight₂' _ _ L).obj (curriedTensor C))) (tensorBifunctor L W)

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
    MonoidalCategoryStruct (LocalizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W).map f).app Y
  tensorUnit := unit
  associator := sorry -- needs localization of trifunctors
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

def toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε := L

def ε' : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit := ε

local notation "L'" => toMonoidalCategory L W ε

noncomputable def μ (X Y : C) : (L').obj X ⊗ (L').obj Y ≅ (L').obj (X ⊗ Y) :=
  ((tensorBifunctorIso L W).app X).app Y

@[reassoc (attr := simp)]
lemma μ_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom =
      (μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y) :=
  NatTrans.naturality_app (tensorBifunctorIso L W).hom Y f

@[reassoc (attr := simp)]
lemma μ_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
      (μ L W ε X Y₁).hom ≫ (toMonoidalCategory L W ε).map (X ◁ g) :=
  ((tensorBifunctorIso L W).hom.app X).naturality g

lemma leftUnitor_hom_app (Y : C) :
    (λ_ ((L').obj Y)).hom =
      (ε' L W ε).inv ▷ (L').obj Y ≫ (μ _ _ _ _ _).hom ≫ (L').map (λ_ Y).hom := by
  sorry

lemma rightUnitor_hom_app (X : C) :
    (ρ_ ((L').obj X)).hom =
      (L').obj X ◁ (ε' L W ε).inv ≫ (μ _ _ _ _ _).hom ≫
        (L').map (ρ_ X).hom := by
  sorry

variable {L W ε} in
lemma pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) :
    (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
      (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom := by
  suffices ∀ (X₁ X₂ X₃ X₄ : C),
    (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) (((L').obj X₂) ⊗ ((L').obj X₃)) ((L').obj X₄)).hom ≫
      ((L').obj X₁) ◁ (α_ ((L').obj X₂) ((L').obj X₃) ((L').obj X₄)).hom =
    (α_ (((L').obj X₁) ⊗ ((L').obj X₂)) ((L').obj X₃) ((L').obj X₄)).hom ≫
      (α_ ((L').obj X₁) ((L').obj X₂) (((L').obj X₃) ⊗ ((L').obj X₄))).hom by
    -- better do a general lemma `pentagon_of_iso` assuming `MonoidalCategoryStruct`
    sorry
  sorry

noncomputable instance :
    MonoidalCategory (LocalizedMonoidal L W ε) where
  tensorHom_def := by intros; simp [monoidalCategoryStruct]
  tensor_id := by intros; simp [monoidalCategoryStruct]
  tensor_comp := by intros; simp [monoidalCategoryStruct]
  whiskerLeft_id := by intros; simp [monoidalCategoryStruct]
  id_whiskerRight := by intros; simp [monoidalCategoryStruct]
  associator_naturality := sorry
  leftUnitor_naturality := by intros; simp [monoidalCategoryStruct]
  rightUnitor_naturality f := (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := sorry

end Monoidal

end Localization

open Localization.Monoidal

noncomputable def toLocalizedMonoidal :
    MonoidalFunctor C (LocalizedMonoidal L W ε) where
  toFunctor := toMonoidalCategory L W ε
  ε := ε.inv
  μ X Y := (μ L W ε X Y).hom
  associativity := sorry
  left_unitality Y := leftUnitor_hom_app L W ε Y
  right_unitality X := rightUnitor_hom_app L W ε X

end CategoryTheory
