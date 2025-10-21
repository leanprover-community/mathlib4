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
for `W`. In the file, we construct a monoidal category structure
on `D` such that the localization functor is monoidal. The structure
is actually defined on a type synonym `LocalizedMonoidal L W ε`.
Here, the data `ε : L.obj (𝟙_ C) ≅ unit` is an isomorphism to some
object `unit : D` which allows the user to provide a preferred choice
of a unit object.

The symmetric case is considered in the file `Mathlib.CategoryTheory.Localization.Monoidal.Braided`.

-/

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

/-- A class of morphisms `W` in a monoidal category is monoidal if it is multiplicative
and stable under left and right whiskering. Under this condition, the localized
category can be equipped with a monoidal category structure, see `LocalizedMonoidal`. -/
class IsMonoidal : Prop extends W.IsMultiplicative where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

variable [W.IsMonoidal]

lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  IsMonoidal.whiskerLeft _ _ hg

lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  IsMonoidal.whiskerRight _ hf Y

lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f ⊗ₘ g) := by
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
      (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L') := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

/-- The localized tensor product, as a bifunctor. -/
noncomputable def tensorBifunctor :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

noncomputable instance : Lifting₂ L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε) :=
  inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

/-- The bifunctor `tensorBifunctor` on `LocalizedMonoidal L W ε` is induced by
`curriedTensor C`. -/
noncomputable abbrev tensorBifunctorIso :
    (((Functor.whiskeringLeft₂ D).obj L').obj L').obj (tensorBifunctor L W ε) ≅
      (Functor.postcompose₂.obj L').obj (curriedTensor C) :=
  Lifting₂.iso L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
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
        (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- The right unitor in the localized monoidal category `LocalizedMonoidal L W ε`. -/
noncomputable def rightUnitor : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

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
      ((μ L W ε _ _).hom ⊗ₘ 𝟙 _) ≫ (μ L W ε _ _).hom ≫ (L').map (α_ X₁ X₂ X₃).hom ≫
        (μ L W ε  _ _).inv ≫ (𝟙 _ ⊗ₘ (μ L W ε  _ _).inv) := by
  dsimp [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl

lemma id_tensorHom (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ₘ f = X ◁ f := by
  simp [monoidalCategoryStruct]

lemma tensorHom_id {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) :
    f ⊗ₘ 𝟙 Y = f ▷ Y := by
  simp [monoidalCategoryStruct]

@[reassoc]
lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) = (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) := by
  simp [monoidalCategoryStruct]

lemma id_tensorHom_id (X₁ X₂ : LocalizedMonoidal L W ε) : 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by
  simp [monoidalCategoryStruct]

@[deprecated (since := "2025-07-14")] alias tensor_id := id_tensorHom_id

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
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ f₂ ⊗ₘ f₃) := by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁, assoc, reassoc_of% h₂, reassoc_of% h₃]

@[reassoc]
lemma associator_naturality₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁) :
    ((f₁ ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ▷ (X₂ ⊗ X₃)) := by
  simp only [← tensorHom_id, associator_naturality, id_tensorHom_id]

@[reassoc]
lemma associator_naturality₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂) :
    ((X₁ ◁ f₂) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (f₂ ▷ X₃)) := by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]
lemma associator_naturality₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃) :
    ((X₁ ⊗ X₂) ◁ f₃) ≫ (α_ X₁ X₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (X₂ ◁ f₃)) := by
  simp only [← id_tensorHom, ← id_tensorHom_id, associator_naturality]

lemma pentagon_aux₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁) :
    ((i.hom ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom ≫ (i.inv ▷ (X₂ ⊗ X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₁_assoc, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, comp_id]

lemma pentagon_aux₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂) :
    ((X₁ ◁ i.hom) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom ≫ (X₁ ◁ (i.inv ▷ X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₂_assoc, ← whiskerLeft_comp, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, whiskerLeft_id, comp_id]

lemma pentagon_aux₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃) :
    ((X₁ ⊗ X₂) ◁ i.hom) ≫ (α_ X₁ X₂ Y₃).hom ≫ (X₁ ◁ (X₂ ◁ i.inv)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₃_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]

instance : (L').EssSurj := Localization.essSurj L' W

variable {L W ε} in
lemma pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) :
    Pentagon Y₁ Y₂ Y₃ Y₄ := by
  obtain ⟨X₁, ⟨e₁⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : ∃ X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : ∃ X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : ∃ X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  suffices Pentagon ((L').obj X₁) ((L').obj X₂) ((L').obj X₃) ((L').obj X₄) by
    dsimp [Pentagon]
    refine Eq.trans ?_ (((((e₁.inv ⊗ₘ e₂.inv) ⊗ₘ e₃.inv) ⊗ₘ e₄.inv) ≫= this =≫
      (e₁.hom ⊗ₘ e₂.hom ⊗ₘ e₃.hom ⊗ₘ e₄.hom)).trans ?_)
    · rw [← id_tensorHom, ← id_tensorHom, ← tensorHom_id, ← tensorHom_id, assoc, assoc,
        ← tensor_comp, ← associator_naturality, id_comp, ← comp_id e₁.hom,
        tensor_comp, ← associator_naturality_assoc, ← comp_id (𝟙 ((L').obj X₄)),
        ← tensor_comp_assoc, associator_naturality, comp_id, comp_id,
        ← tensor_comp_assoc, assoc, e₄.inv_hom_id, ← tensor_comp, e₁.inv_hom_id,
        ← tensor_comp, e₂.inv_hom_id, e₃.inv_hom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
    · rw [assoc, associator_naturality_assoc, associator_naturality_assoc,
        ← tensor_comp, e₁.inv_hom_id, ← tensor_comp, e₂.inv_hom_id, ← tensor_comp,
        e₃.inv_hom_id, e₄.inv_hom_id, id_tensorHom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
  dsimp [Pentagon]
  have : ((L').obj X₁ ◁ (μ L W ε X₂ X₃).inv) ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) ((L').obj X₂ ⊗ (L').obj X₃) ((L').obj X₄)).hom ≫
        (L').obj X₁ ◁ (μ L W ε X₂ X₃).hom ▷ (L').obj X₄ =
          (α_ ((L').obj X₁) ((L').obj (X₂ ⊗ X₃)) ((L').obj X₄)).hom :=
    pentagon_aux₂ _ _ _ (μ L W ε X₂ X₃).symm
  rw [associator_hom_app, tensorHom_id, id_tensorHom, associator_hom_app, tensorHom_id,
    whiskerLeft_comp, whiskerRight_comp, whiskerRight_comp, whiskerRight_comp, assoc, assoc,
    assoc, whiskerRight_comp, assoc,
    reassoc_of% this, associator_hom_app, tensorHom_id,
    ← pentagon_aux₁ (X₂ := (L').obj X₃) (X₃ := (L').obj X₄) (i := μ L W ε X₁ X₂),
    ← pentagon_aux₃ (X₁ := (L').obj X₁) (X₂ := (L').obj X₂) (i := μ L W ε X₃ X₄),
    associator_hom_app, associator_hom_app]
  simp only [assoc, ← whiskerRight_comp_assoc, Iso.inv_hom_id, comp_id, μ_natural_left_assoc,
    id_tensorHom, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (L').map_comp_assoc, whiskerLeft_comp, μ_inv_natural_right_assoc, ← (L').map_comp_assoc]
  simp only [assoc, MonoidalCategory.pentagon, Functor.map_comp, tensorHom_id,
    whiskerRight_comp_assoc]
  congr 3; simp only [← assoc]; congr
  simp only [← cancel_mono (μ L W ε (X₁ ⊗ X₂) (X₃ ⊗ X₄)).inv, assoc, id_comp,
    whisker_exchange_assoc, ← whiskerRight_comp_assoc,
    Iso.inv_hom_id, whiskerRight_id, ← whiskerLeft_comp,
    whiskerLeft_id]

lemma leftUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    𝟙_ (LocalizedMonoidal L W ε) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  simp [monoidalCategoryStruct]

lemma rightUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    f ▷ 𝟙_ (LocalizedMonoidal L W ε) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f :=
  (rightUnitor L W ε).hom.naturality f

@[reassoc]
lemma triangle_aux₁ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (i₁ : X₁ ≅ Y₁) (i₂ : X₂ ≅ Y₂) (i₃ : X₃ ≅ Y₃) :
    ((i₁.hom ⊗ₘ i₂.hom) ⊗ₘ i₃.hom) ≫ (α_ Y₁ Y₂ Y₃).hom ≫ (i₁.inv ⊗ₘ i₂.inv ⊗ₘ i₃.inv) =
      (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality_assoc, ← tensor_comp, Iso.hom_inv_id, id_tensorHom,
    whiskerLeft_id, comp_id]

lemma triangle_aux₂ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) :
      e₁.hom ⊗ₘ (ε.hom ⊗ₘ e₂.hom) ≫ (λ_ Y).hom =
        (L').obj X' ◁ ((ε' L W ε).hom ▷ (L').obj Y' ≫
          𝟙_ _ ◁ e₂.hom ≫ (λ_ Y).hom) ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, comp_id, id_comp,
    ← tensor_comp_assoc, id_comp]
  congr 3
  exact (comp_id _).symm

lemma triangle_aux₃ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) : (ρ_ X).hom ▷ _ =
      ((e₁.inv ⊗ₘ ε.inv) ⊗ₘ e₂.inv) ≫ _ ◁ e₂.hom ≫ ((μ L W ε X' (𝟙_ C)).hom ≫
        (L').map (ρ_ X').hom) ▷ Y ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, assoc, comp_id,
    id_comp, Iso.inv_hom_id]
  congr
  rw [← cancel_mono e₁.inv, assoc, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← rightUnitor_naturality, rightUnitor_hom_app,
    ← tensorHom_id, ← id_tensorHom, ← tensor_comp_assoc, comp_id, id_comp]

variable {L W ε} in
lemma triangle (X Y : LocalizedMonoidal L W ε) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  obtain ⟨X', ⟨e₁⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
  obtain ⟨Y', ⟨e₂⟩⟩ : ∃ X₂, Nonempty ((L').obj X₂ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
  have h₁ := (associator_hom_app L W ε X' (𝟙_ _) Y' =≫
    (𝟙 ((L').obj X') ⊗ₘ (μ L W ε (𝟙_ C) Y').hom))
  simp only [assoc, id_tensorHom, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id, Iso.inv_hom_id,
    ← cancel_mono (μ L W ε X' (𝟙_ C ⊗ Y')).hom] at h₁
  have h₂ := (ε' L W ε).hom ▷ (L').obj Y' ≫= leftUnitor_hom_app L W ε Y'
  simp only [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id, id_comp] at h₂
  have h₃ := (((μ L W ε _ _).hom ⊗ₘ 𝟙 _) ≫ (μ L W ε _ _).hom) ≫=
    ((L').congr_map (MonoidalCategory.triangle X' Y'))
  simp only [assoc, Functor.map_comp, ← reassoc_of% h₁] at h₃
  rw [← μ_natural_left, tensorHom_id, ← whiskerRight_comp_assoc,
    ← μ_natural_right, ← Iso.comp_inv_eq, assoc, assoc, assoc,
    Iso.hom_inv_id, comp_id, ← whiskerLeft_comp, ← h₂] at h₃
  replace h₃ := ((e₁.inv ⊗ₘ ε.inv) ⊗ₘ e₂.inv) ≫= (h₃ =≫ (_ ◁ e₂.hom)) =≫ (e₁.hom ▷ _)
  simp only [← whiskerLeft_comp, assoc, ← leftUnitor_naturality, ← whisker_exchange] at h₃
  have : _ = (α_ X (𝟙_ (LocalizedMonoidal L W ε)) Y).hom :=
    triangle_aux₁ _ _ _ e₁.symm ε.symm e₂.symm
  simp only [← this, Iso.symm_hom, Iso.symm_inv, assoc,
    ← id_tensorHom, ← tensor_comp, comp_id]
  convert h₃
  · exact triangle_aux₂ _ _ _ e₁ e₂
  · exact triangle_aux₃ _ _ _ e₁ e₂

noncomputable instance :
    MonoidalCategory (LocalizedMonoidal L W ε) where
  tensorHom_def := by intros; simp [monoidalCategoryStruct]
  id_tensorHom_id := by intros; simp [monoidalCategoryStruct]
  tensorHom_comp_tensorHom := by intros; simp [monoidalCategoryStruct]
  whiskerLeft_id := by intros; simp [monoidalCategoryStruct]
  id_whiskerRight := by intros; simp [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by apply associator_naturality
  leftUnitor_naturality := by intros; simp [monoidalCategoryStruct]
  rightUnitor_naturality := fun f ↦ (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := triangle

end Monoidal

end Localization

open Localization.Monoidal

noncomputable instance : (toMonoidalCategory L W ε).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ε.symm
      μIso X Y := μ L W ε X Y
      associativity X Y Z := by simp [associator_hom_app L W ε X Y Z]
      left_unitality Y := leftUnitor_hom_app L W ε Y
      right_unitality X := rightUnitor_hom_app L W ε X }

local notation "L'" => toMonoidalCategory L W ε

lemma associator_hom (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom =
    (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
      (Functor.LaxMonoidal.μ (L') (X ⊗ Y) Z) ≫
        (L').map (α_ X Y Z).hom ≫
          (Functor.OplaxMonoidal.δ (L') X (Y ⊗ Z)) ≫
            ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z) := by
  simp

lemma associator_inv (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv =
    (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
      (Functor.LaxMonoidal.μ (L') X (Y ⊗ Z)) ≫
        (L').map (α_ X Y Z).inv ≫
          (Functor.OplaxMonoidal.δ (L') (X ⊗ Y) Z) ≫
            (Functor.OplaxMonoidal.δ (L') X Y) ▷ ((L').obj Z) := by
  simp


end CategoryTheory
