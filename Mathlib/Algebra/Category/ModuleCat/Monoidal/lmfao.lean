import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Basic

universe v u

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

class SemigroupalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C
  /-- left whiskering for morphisms -/
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  /-- right whiskering for morphisms -/
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)

namespace SemigroupalCategory
export SemigroupalCategoryStruct (tensorObj whiskerLeft whiskerRight tensorHom associator)
end SemigroupalCategory
namespace MonoidalCategory
export SemigroupalCategoryStruct (tensorObj whiskerLeft whiskerRight tensorHom associator)
end MonoidalCategory

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`MonoidalCategory`. -/
class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] extends
    SemigroupalCategoryStruct C where
  tensorUnit : C
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory
export MonoidalCategoryStruct (tensorUnit leftUnitor rightUnitor)
end MonoidalCategory

namespace SemigroupalCategory

/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
scoped infixr:70 " ⊗ " => tensorObj

/-- Notation for the `whiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ " => whiskerLeft

/-- Notation for the `whiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ " => whiskerRight

/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
scoped infixr:70 " ⊗ " => tensorHom

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => associator

end SemigroupalCategory

open scoped SemigroupalCategory in
class SemigroupalCategory (C : Type u) [𝒞 : Category.{v} C] extends
    SemigroupalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      aesop_cat
  /-- Tensor product of identity maps is the identity: `(𝟙 X₁ ⊗ 𝟙 X₂) = 𝟙 (X₁ ⊗ X₂)` -/
  tensor_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊗ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by aesop_cat
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ g₁) ∘ (f₂ ⊗ g₂) = (f₁ ∘ f₂) ⊗ (g₁ ⊗ g₂)`
  -/
  tensor_comp :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
    aesop_cat
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    aesop_cat
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ f₂) ⊗ f₃ ≃ f₁ ⊗ (f₂ ⊗ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by
    aesop_cat
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    aesop_cat

attribute [reassoc] SemigroupalCategory.tensorHom_def
attribute [reassoc, simp] SemigroupalCategory.whiskerLeft_id
attribute [reassoc, simp] SemigroupalCategory.id_whiskerRight
attribute [reassoc] SemigroupalCategory.tensor_comp
attribute [simp] SemigroupalCategory.tensor_comp
attribute [reassoc] SemigroupalCategory.associator_naturality
attribute [reassoc (attr := simp)] SemigroupalCategory.pentagon

namespace MonoidalCategory

export SemigroupalCategory (tensorHom_def tensor_id tensor_comp whiskerLeft_id id_whiskerRight
  associator_naturality pentagon)

open scoped SemigroupalCategory

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:max => (MonoidalCategoryStruct.tensorUnit : C)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Used to ensure that `𝟙_` notation is used, as the ascription makes this not automatic. -/
@[delab app.CategoryTheory.MonoidalCategoryStruct.tensorUnit]
def delabTensorUnit : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  let e ← getExpr
  guard <| e.isAppOfArity ``MonoidalCategoryStruct.tensorUnit 3
  let C ← withNaryArg 0 delab
  `(𝟙_ $C)

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

end MonoidalCategory

open MonoidalCategory SemigroupalCategory in
/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
-- Porting note: The Mathport did not translate the temporary notation
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends
    MonoidalCategoryStruct C, SemigroupalCategory C where
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
    aesop_cat
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
    aesop_cat

attribute [reassoc] MonoidalCategory.leftUnitor_naturality
attribute [reassoc] MonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] MonoidalCategory.triangle

namespace SemigroupalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [SemigroupalCategory C]

@[simp]
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ f = X ◁ f := by
  simp [tensorHom_def]

@[simp]
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ 𝟙 Y = f ▷ Y := by
  simp [tensorHom_def]

@[reassoc, simp]
theorem whiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g := by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc, simp]
theorem tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc, simp]
theorem comp_whiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) :
    (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z := by
  simp only [← tensorHom_id, ← tensor_comp, id_comp]

@[reassoc, simp]
theorem whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [associator_naturality]
  simp [tensor_id]

@[reassoc, simp]
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc]
theorem whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

@[reassoc]
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ f ≫ X ◁ inv f = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ Z ≫ inv f ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
theorem whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ inv f ≫ X ◁ f = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[simps]
def whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X ⊗ Y ≅ X ⊗ Z where
  hom := X ◁ f.hom
  inv := X ◁ f.inv

instance whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f) :=
  (whiskerLeftIso X (asIso f)).isIso_hom

@[simp]
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  aesop_cat

@[simp]
lemma whiskerLeftIso_refl (W X : C) :
    whiskerLeftIso W (Iso.refl X) = Iso.refl (W ⊗ X) :=
  Iso.ext (whiskerLeft_id W X)

@[simp]
lemma whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    whiskerLeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g :=
  Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]
lemma whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (whiskerLeftIso W f).symm = whiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⊗ Z ≅ Y ⊗ Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z

instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  (whiskerRightIso (asIso f) Z).isIso_hom

@[simp]
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  aesop_cat

@[simp]
lemma whiskerRightIso_refl (X W : C) :
    whiskerRightIso (Iso.refl X) W = Iso.refl (X ⊗ W) :=
  Iso.ext (id_whiskerRight X W)

@[simp]
lemma whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    whiskerRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W :=
  Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]
lemma whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (whiskerRightIso f W).symm = whiskerRightIso f.symm W := rfl

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv
  hom_inv_id := by rw [← tensor_comp, Iso.hom_inv_id, Iso.hom_inv_id, ← tensor_id]
  inv_hom_id := by rw [← tensor_comp, Iso.inv_hom_id, Iso.inv_hom_id, ← tensor_id]

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
infixr:70 " ⊗ " => tensorIso

theorem tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g :=
  Iso.ext (tensorHom_def f.hom g.hom)

theorem tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ g = whiskerLeftIso X g ≪≫ whiskerRightIso f Y' :=
  Iso.ext (tensorHom_def' f.hom g.hom)

instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  (asIso f ⊗ asIso g).isIso_hom

@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ g) = inv f ⊗ inv g := by
  simp [tensorHom_def ,whisker_exchange]

variable {U V W X Y Z : C}

theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl

theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl

theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ if h : P then g h else g' h) =
    if h : P then f ⊗ g h else f ⊗ g' h := by split_ifs <;> rfl

theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ f =
    if h : P then g h ⊗ f else g' h ⊗ f := by split_ifs <;> rfl

@[simp]
theorem whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ eqToHom f = eqToHom (congr_arg₂ tensorObj rfl f) := by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]
theorem eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ Z = eqToHom (congr_arg₂ tensorObj f rfl) := by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by simp

@[reassoc]
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by simp

@[reassoc]
theorem whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv := by simp

@[reassoc]
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z := by simp

@[reassoc]
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by simp

@[reassoc]
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom := by simp

@[reassoc]
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f := by simp

@[reassoc]
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by simp

@[reassoc]
theorem tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := simp)]
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_hom_inv :
    (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom =
      W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv := by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv), ← cancel_mono (α_ (W ⊗ X) Y Z).inv]
  simp

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_inv :
    (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom =
      (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv =
      (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z := by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_hom_hom :
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv =
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_hom :
    (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv =
      (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z := by
  rw [← cancel_epi (α_ W X (Y ⊗ Z)).inv, ← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_inv_hom :
    (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv =
      (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_hom :
    (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
      (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom := by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_inv_inv :
    (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z =
      W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

end

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) := by
  simp [tensorHom_def]

@[reassoc, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g) ⊗ h = (α_ X Y Z).hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ g ⊗ h = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]

@[reassoc]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ g) ≫ (f.inv ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, f.hom_inv_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.hom ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, f.inv_hom_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.hom) ≫ (h ⊗ f.inv) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, f.hom_inv_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.hom) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, f.inv_hom_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, IsIso.hom_inv_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, IsIso.inv_hom_id]; simp [id_tensorHom]

@[reassoc (attr := simp)]
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, IsIso.hom_inv_id]; simp [tensorHom_id]

@[reassoc (attr := simp)]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, IsIso.inv_hom_id]; simp [tensorHom_id]


/--
A constructor for monoidal categories that requires `tensorHom` instead of `whiskerLeft` and
`whiskerRight`.
-/
abbrev ofTensorHom [SemigroupalCategoryStruct C]
    (tensor_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      aesop_cat)
    (id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      aesop_cat)
    (tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      aesop_cat)
    (tensor_comp :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
          aesop_cat)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            aesop_cat)
    (pentagon :
      ∀ W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            aesop_cat) :
      SemigroupalCategory C where
  tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← tensor_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, tensor_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]

@[reassoc]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) := by
  simp

@[reassoc]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) := by
  simp

@[reassoc]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f := by
  rw [← tensor_comp]
  simp

@[reassoc]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f := by
  rw [← tensor_comp]
  simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ f.2

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ f.2.1) ⊗ f.2.2

@[simp]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[simp]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ f.2.1 ⊗ f.2.2

@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl

/-- The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[simps]
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⊗ Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps!]
def tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps!]
def tensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
-- Porting Note: Had to add a `simps!` because Lean was complaining this wasn't a constructor app.
/-- The associator as a natural isomorphism. -/
@[simps!]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[simps!]
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedTensor C) ≅
      bifunctorComp₂₃ (curriedTensor C) (curriedTensor C) :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

section

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

@[simp]
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
abbrev tensoringLeft : C ⥤ C ⥤ C := curriedTensor C

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
abbrev tensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip


variable {C}

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

@[simp]
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [tensorRightTensor]

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [SemigroupalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [SemigroupalCategory.{v₂} C₂]

attribute [local simp] tensor_id associator_naturality pentagon

@[simps! tensorObj tensorHom whiskerLeft whiskerRight associator]
instance prodSemigroupal : SemigroupalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom f g := (f.1 ⊗ g.1, f.2 ⊗ g.2)
  whiskerLeft X _ _ f := (whiskerLeft X.1 f.1, whiskerLeft X.2 f.2)
  whiskerRight f X := (whiskerRight f.1 X.1, whiskerRight f.2 X.2)
  tensorHom_def := by simp [tensorHom_def]
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)

end
end SemigroupalCategory
namespace MonoidalCategory
open SemigroupalCategory

variable {C : Type u} [Category.{v} C]

section

variable [MonoidalCategory C]

@[reassoc, simp]
theorem whiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← assoc, ← rightUnitor_naturality]; simp [tensorHom_id]

@[reassoc, simp]
theorem id_whiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv := by
  rw [← assoc, ← leftUnitor_naturality]; simp [id_tensorHom]


@[reassoc]
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ _ ◁ f := by simp

@[reassoc]
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ_ X).inv ≫ 𝟙_ C ◁ f ≫ (λ_ X').hom := by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _ := by simp

@[reassoc]
theorem whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom := by
  simp

theorem whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g := by simp

theorem whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g := by simp


@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (λ_ Y).inv := by
  simp [← cancel_mono (X ◁ (λ_ Y).hom)]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
@[reassoc, simp]
theorem leftUnitor_whiskerRight (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom := by
  rw [← whiskerLeft_iff, SemigroupalCategory.whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
theorem leftUnitor_inv_whiskerRight (X Y : C) :
    (λ_ X).inv ▷ Y = (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
theorem whiskerLeft_rightUnitor (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (X ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← SemigroupalCategory.whiskerLeft_comp_assoc,
      triangle_assoc_comp_right, associator_inv_naturality_right]

@[reassoc, simp]
theorem whiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ (ρ_ Y).inv = (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
theorem leftUnitor_tensor (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y := by simp

@[reassoc]
theorem leftUnitor_tensor_inv (X Y : C) :
    (λ_ (X ⊗ Y)).inv = (λ_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
theorem rightUnitor_tensor (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by simp

@[reassoc]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv := by simp

end

/--
A constructor for monoidal categories that requires `tensorHom` instead of `whiskerLeft` and
`whiskerRight`.
-/
abbrev ofTensorHom [MonoidalCategoryStruct C]
    (tensor_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      aesop_cat)
    (id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      aesop_cat)
    (tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      aesop_cat)
    (tensor_comp :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
          aesop_cat)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            aesop_cat)
    (leftUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom (𝟙 tensorUnit) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          aesop_cat)
    (rightUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom f (𝟙 tensorUnit) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          aesop_cat)
    (pentagon :
      ∀ W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            aesop_cat)
    (triangle :
      ∀ X Y : C,
        (associator X tensorUnit Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
          tensorHom (rightUnitor X).hom (𝟙 Y) := by
            aesop_cat) :
      MonoidalCategory C where
  tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← tensor_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, tensor_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

section

variable [MonoidalCategory C]

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by simp

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by simp

variable (C)

/-- The functor `fun X ↦ 𝟙_ C ⊗ X`. -/
abbrev tensorUnitLeft : C ⥤ C := tensorLeft (𝟙_ C)

/-- The functor `fun X ↦ X ⊗ 𝟙_ C`. -/
abbrev tensorUnitRight : C ⥤ C := tensorRight (𝟙_ C)

-- Porting Note: same as above
/-- The left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.leftUnitor

-- Porting Note: same as above
/-- The right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.rightUnitor

instance : (tensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

instance : (tensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] leftUnitor_naturality rightUnitor_naturality triangle

@[simps! tensorObj tensorHom tensorUnit whiskerLeft whiskerRight associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) :=
{ prodSemigroupal C₁ C₂ with
  toSemigroupalCategoryStruct := inferInstance
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂) }

@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ_ X).hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ_ X).hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv := by
  cases X
  rfl

end
end MonoidalCategory

end CategoryTheory
