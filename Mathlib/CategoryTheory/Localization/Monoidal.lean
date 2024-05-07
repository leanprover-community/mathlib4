import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Monoidal.Functor

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategoryStruct C]

def Pentagon (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
    (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
      (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom

variable (naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃))
    (tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), f ⊗ g = f ▷ X₂ ≫ Y₁ ◁ g)

variable {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
  (e₄ : X₄ ≅ Y₄)

lemma pentagon_of_iso (h : Pentagon X₁ X₂ X₃ X₄) : Pentagon Y₁ Y₂ Y₃ Y₄ := by
  dsimp [Pentagon] at h ⊢
  have := @naturality
  refine' Eq.trans _ (((((e₁.inv ⊗ e₂.inv) ⊗ e₃.inv) ⊗ e₄.inv) ≫= h =≫ (e₁.hom ⊗ e₂.hom ⊗ e₃.hom ⊗ e₄.hom)).trans sorry)
  · dsimp
    simp only [assoc]
    --rw [← tensorHom_id]
    sorry

end MonoidalCategory

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

def toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε := L

abbrev ε' : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit := ε

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

lemma isInvertedBy₂ :
    MorphismProperty.IsInvertedBy₂ W W
      ((whiskeringRight₂' _ _ L').obj (curriedTensor C)) := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

noncomputable abbrev tensorBifunctor :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

noncomputable abbrev tensorBifunctorIso :
    (whiskeringLeft₂ObjObj L' L' D).obj (tensorBifunctor L W ε) ≅
      (whiskeringRight₂' C C L').obj (curriedTensor C) :=
  Lifting₂.iso L L W W (((whiskeringRight₂' _ _ L').obj (curriedTensor C))) (tensorBifunctor L W ε)

noncomputable abbrev tensorLeftFunctor (X : LocalizedMonoidal L W ε) :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε := (tensorBifunctor L W ε).obj X

noncomputable abbrev tensorRightFunctor (Y : LocalizedMonoidal L W ε) :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  (tensorBifunctor L W ε).flip.obj Y

noncomputable instance (X : C) :
    Lifting L' W (tensorLeft X ⋙ L') (tensorLeftFunctor L W ε ((L').obj X)) :=
  inferInstanceAs (Lifting L W ((((whiskeringRight₂' _ _ L').obj (curriedTensor C))).obj X)
    ((tensorBifunctor L W ε).obj (L.obj X)))

noncomputable instance (Y : C) :
    Lifting L' W (tensorRight Y ⋙ L') (tensorRightFunctor L W ε ((L').obj Y)) :=
  inferInstanceAs (Lifting L W ((((whiskeringRight₂' _ _ L').obj (curriedTensor C))).flip.obj Y)
    ((tensorBifunctor L W ε).flip.obj (L.obj Y)))

noncomputable def leftUnitor : tensorLeftFunctor L W ε unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      (tensorLeftFunctor L W ε ((L').obj (𝟙_ _))) _
      (isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

noncomputable def rightUnitor : tensorRightFunctor L W ε unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      (tensorRightFunctor L W ε ((L').obj (𝟙_ _))) _
      (isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (LocalizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := (tensorLeftFunctor L W ε X).map g
  whiskerRight f Y := (tensorRightFunctor L W ε Y).map f
  tensorUnit := unit
  associator := sorry -- needs localization of trifunctors
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

noncomputable def μ (X Y : C) : (L').obj X ⊗ (L').obj Y ≅ (L').obj (X ⊗ Y) :=
  ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]
lemma μ_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom =
      (μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y) :=
  NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]
lemma μ_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
      (μ L W ε X Y₁).hom ≫ (toMonoidalCategory L W ε).map (X ◁ g) :=
  ((tensorBifunctorIso L W ε).hom.app X).naturality g

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

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := sorry

variable {L W ε} in
lemma pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) :
    Pentagon Y₁ Y₂ Y₃ Y₄ := by
  have : (L').EssSurj := Localization.essSurj L' W
  obtain ⟨X₁, ⟨e₁⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : ∃ X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : ∃ X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : ∃ X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  apply pentagon_of_iso (associator_naturality L W ε) e₁ e₂ e₃ e₄
  dsimp [Pentagon]
  sorry

noncomputable instance :
    MonoidalCategory (LocalizedMonoidal L W ε) where
  tensorHom_def := by intros; simp [monoidalCategoryStruct]
  tensor_id := by intros; simp [monoidalCategoryStruct]
  tensor_comp := by intros; simp [monoidalCategoryStruct]
  whiskerLeft_id := by intros; simp [monoidalCategoryStruct]
  id_whiskerRight := by intros; simp [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    sorry
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
