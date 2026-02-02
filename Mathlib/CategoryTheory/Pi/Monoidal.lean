/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The pointwise monoidal structure on the product of families of monoidal categories

Given a family of monoidal categories `C i`, we define a monoidal structure on
`Π i, C i` where the tensor product is defined pointwise.

-/

@[expose] public section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Pi

open Category MonoidalCategory

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  [∀ i, MonoidalCategory (C i)]

@[simps tensorObj tensorHom whiskerLeft whiskerRight tensorUnit]
instance monoidalCategoryStruct : MonoidalCategoryStruct (∀ i, C i) where
  tensorObj X Y i := X i ⊗ Y i
  tensorHom f g i := f i ⊗ₘ g i
  whiskerLeft X _ _ f i := X i ◁ f i
  whiskerRight f Y i := f i ▷ Y i
  tensorUnit i := 𝟙_ (C i)
  leftUnitor X := isoMk (fun i ↦ λ_ (X i))
  rightUnitor X := isoMk (fun i ↦ ρ_ (X i))
  associator X Y Z := isoMk (fun i ↦ α_ (X i) (Y i) (Z i))

@[simp]
theorem associator_hom_apply {X Y Z : ∀ i, C i} {i : I} :
    (α_ X Y Z).hom i = (α_ (X i) (Y i) (Z i)).hom := rfl

@[simp]
theorem associator_inv_apply {X Y Z : ∀ i, C i} {i : I} :
    (α_ X Y Z).inv i = (α_ (X i) (Y i) (Z i)).inv := rfl

@[simp]
theorem isoApp_associator {X Y Z : ∀ i, C i} {i : I} :
    isoApp (α_ X Y Z) i = α_ (X i) (Y i) (Z i) := rfl

@[simp]
theorem left_unitor_hom_apply {X : ∀ i, C i} {i : I} :
    (λ_ X).hom i = (λ_ (X i)).hom := rfl

@[simp]
theorem left_unitor_inv_apply {X : ∀ i, C i} {i : I} :
    (λ_ X).inv i = (λ_ (X i)).inv := rfl

@[simp]
theorem isoApp_left_unitor {X : ∀ i, C i} {i : I} :
    isoApp (λ_ X) i = λ_ (X i) := rfl

@[simp]
theorem right_unitor_hom_apply {X : ∀ i, C i} {i : I} :
    (ρ_ X).hom i = (ρ_ (X i)).hom := rfl

@[simp]
theorem right_unitor_inv_apply {X : ∀ i, C i} {i : I} :
    (ρ_ X).inv i = (ρ_ (X i)).inv := rfl

@[simp]
theorem isoApp_right_unitor {X : ∀ i, C i} {i : I} :
    isoApp (ρ_ X) i = ρ_ (X i) := rfl

/-- `Pi.monoidalCategory C` equips the product of an indexed family of categories with
the pointwise monoidal structure. -/
instance monoidalCategory : MonoidalCategory.{max w₁ v₁} (∀ i, C i) where
  tensorHom_def {A B X Y} f g := by ext i; simp [tensorHom_def, whiskerLeft]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [∀ i, BraidedCategory (C i)]

/-- When each `C i` is a braided monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also braided.
-/
instance braidedCategory : BraidedCategory (∀ i, C i) where
  braiding X Y := isoMk fun i => β_ (X i) (Y i)
  hexagon_forward X Y Z := by ext i; apply hexagon_forward
  hexagon_reverse X Y Z := by ext i; apply hexagon_reverse

@[simp]
theorem braiding_hom_apply {X Y : ∀ i, C i} {i : I} :
    (β_ X Y).hom i = (β_ (X i) (Y i)).hom := rfl

@[simp]
theorem braiding_inv_apply {X Y : ∀ i, C i} {i : I} :
    (β_ X Y).inv i = (β_ (X i) (Y i)).inv := rfl

@[simp]
theorem isoApp_braiding {X Y : ∀ i, C i} {i : I} :
    isoApp (β_ X Y) i = β_ (X i) (Y i) := rfl

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [∀ i, SymmetricCategory (C i)]

/-- When each `C i` is a symmetric monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also symmetric.
-/
instance symmetricCategory : SymmetricCategory (∀ i, C i) where
  symmetry X Y := by ext i; apply symmetry

end SymmetricCategory

section Closed

open ihom

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  [∀ i, MonoidalCategory (C i)] [∀ i, MonoidalClosed (C i)]

/-- The internal hom functor `X ⟶[∀ i, C i] -` -/
@[simps!]
def ihom (X : ∀ i, C i) : (∀ i, C i) ⥤ (∀ i, C i) where
  obj Y := fun i ↦ (X i ⟶[C i] Y i)
  map {Y Z} f := fun i ↦ (CategoryTheory.ihom (X i)).map (f i)

/-- The unit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
def closedUnit (X : ∀ i, C i) : 𝟭 (∀ i, C i) ⟶ tensorLeft X ⋙ ihom X where
  app Y := fun i ↦ (ihom.coev (X i)).app (Y i)

/-- The counit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
def closedCounit (X : ∀ i, C i) : ihom X ⋙ tensorLeft X ⟶ 𝟭 (∀ i, C i) where
  app Y := fun i ↦ (ihom.ev (X i)).app (Y i)

/-- Equips the product of a family of closed monoidal categories with
a pointwise closed monoidal structure. -/
@[simps]
instance monoidalClosed : MonoidalClosed (∀ i, C i) where
  closed X := {
    rightAdj := ihom X
    adj.unit := closedUnit X
    adj.counit := closedCounit X }

end Closed

@[simps!]
instance (i : I) : (Pi.eval C i).Monoidal where
  ε := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  δ X Y := 𝟙 _

instance [∀ i, BraidedCategory (C i)] (i : I) : (Pi.eval C i).Braided where

@[simps]
instance laxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D] (F : ∀ i : I, D ⥤ C i)
    [∀ i, (F i).LaxMonoidal] :
    (Functor.pi' F).LaxMonoidal where
  ε := fun i ↦ Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i ↦ Functor.LaxMonoidal.μ (F i) X Y

@[simps]
instance opLaxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : ∀ i : I, D ⥤ C i)
    [∀ i, (F i).OplaxMonoidal] :
    (Functor.pi' F).OplaxMonoidal where
  η := fun i ↦ Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i ↦ Functor.OplaxMonoidal.δ (F i) X Y
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

@[simps!]
instance monoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).Monoidal] :
    (Functor.pi' F).Monoidal where

instance [∀ i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).LaxBraided] :
    (Functor.pi' F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _

instance [∀ i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).Braided] :
    (Functor.pi' F).Braided where

@[simps]
instance laxMonoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).LaxMonoidal] :
    (Functor.pi F).LaxMonoidal where
  ε := fun i ↦ Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i ↦ Functor.LaxMonoidal.μ (F i) (X i) (Y i)

@[simps]
instance opLaxMonoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).OplaxMonoidal] :
    (Functor.pi F).OplaxMonoidal where
  η := fun i ↦ Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i ↦ Functor.OplaxMonoidal.δ (F i) (X i) (Y i)
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

@[simps!]
instance monoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).Monoidal] :
    (Functor.pi F).Monoidal where

instance [∀ i, BraidedCategory (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, BraidedCategory (D i)]
    (F : ∀ i : I, D i ⥤ C i) [∀ i, (F i).LaxBraided] :
    (Functor.pi F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _

instance [∀ i, BraidedCategory (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, BraidedCategory (D i)]
    (F : ∀ i : I, D i ⥤ C i) [∀ i, (F i).Braided] :
    (Functor.pi F).Braided where

instance {D : Type*} [Category* D] [MonoidalCategory D]
    {F G : D ⥤ (∀ i, C i)} [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i)
    [∀ i, (τ i).IsMonoidal] :
    (NatTrans.pi' τ).IsMonoidal where
  unit := by ext i; simpa using NatTrans.IsMonoidal.unit (τ := τ i)
  tensor X Y := by ext i; simpa using NatTrans.IsMonoidal.tensor _ _ (τ := τ i)

instance {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)]
    {F G : ∀ i : I, (D i ⥤ C i)} [∀ i, (F i).LaxMonoidal]
    [∀ i, (G i).LaxMonoidal] (τ : ∀ i : I, (F i) ⟶ (G i))
    [∀ i, (τ i).IsMonoidal] :
    (NatTrans.pi τ).IsMonoidal where

end Pi

end CategoryTheory
