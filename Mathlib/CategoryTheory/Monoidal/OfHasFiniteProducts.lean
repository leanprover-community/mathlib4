/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## TODO

Replace `monoidalOfHasFiniteProducts` and `symmetricOfHasFiniteProducts`
with `CartesianMonoidalCategory.ofHasFiniteProducts`.
-/


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidalOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y ↦ X ⨯ Y
    whiskerLeft := fun _ _ _ g ↦ Limits.prod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ ↦ Limits.prod.map f (𝟙 _)
    tensorHom := fun f g ↦ Limits.prod.map f g
    tensorUnit := ⊤_ C
    associator := prod.associator
    leftUnitor := fun P ↦ Limits.prod.leftUnitor P
    rightUnitor := fun P ↦ Limits.prod.rightUnitor P
  }
  .ofTensorHom
    (pentagon := prod.pentagon)
    (triangle := prod.triangle)
    (associator_naturality := @prod.associator_naturality _ _ _)

end

namespace monoidalOfHasFiniteProducts

variable [HasTerminal C] [HasBinaryProducts C]

attribute [local instance] monoidalOfHasFiniteProducts

open scoped MonoidalCategory

@[ext] theorem unit_ext {X : C} (f g : X ⟶ 𝟙_ C) : f = g := terminal.hom_ext f g

@[ext] theorem tensor_ext {X Y Z : C} (f g : X ⟶ Y ⊗ Z)
    (w₁ : f ≫ prod.fst = g ≫ prod.fst) (w₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  Limits.prod.hom_ext w₁ w₂

@[simp] theorem tensorUnit : 𝟙_ C = ⊤_ C := rfl

@[simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨯ Y) :=
  rfl

@[simp]
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ₘ g = Limits.prod.map f g :=
  rfl

@[simp]
theorem whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.prod.map (𝟙 X) f :=
  rfl

@[simp]
theorem whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.prod.map f (𝟙 Z) :=
  rfl

@[simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = Limits.prod.snd :=
  rfl

@[simp]
theorem leftUnitor_inv (X : C) : (λ_ X).inv = prod.lift (terminal.from X) (𝟙 _) :=
  rfl

@[simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = Limits.prod.fst :=
  rfl

@[simp]
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = prod.lift (𝟙 _) (terminal.from X) :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      prod.lift (Limits.prod.fst ≫ Limits.prod.fst)
        (prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd) :=
  rfl

theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd) :=
  rfl

@[reassoc] theorem associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.fst = prod.fst ≫ prod.fst := by simp [associator_hom]

@[reassoc] theorem associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.snd ≫ prod.fst = prod.fst ≫ prod.snd := by simp [associator_hom]

@[reassoc] theorem associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ prod.snd ≫ prod.snd = prod.snd := by simp [associator_hom]

@[reassoc] theorem associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.fst ≫ prod.fst = prod.fst := by simp [associator_inv]

@[reassoc] theorem associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.fst ≫ prod.snd = prod.snd ≫ prod.fst := by simp [associator_inv]

@[reassoc] theorem associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ prod.snd = prod.snd ≫ prod.snd := by simp [associator_inv]

end monoidalOfHasFiniteProducts

section

attribute [local instance] monoidalOfHasFiniteProducts

open MonoidalCategory

/-- The monoidal structure coming from finite products is symmetric.
-/
@[simps]
def symmetricOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : SymmetricCategory C where
  braiding X Y := Limits.prod.braiding X Y
  braiding_naturality_left f X := by simp
  braiding_naturality_right X _ _ f := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteProducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteProducts.associator_inv]; simp
  symmetry X Y := by simp

end

section

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y ↦ X ⨿ Y
    whiskerLeft := fun _ _ _ g ↦ Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ ↦ Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g ↦ Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associator
    leftUnitor := fun P ↦ coprod.leftUnitor P
    rightUnitor := fun P ↦ coprod.rightUnitor P
  }
  .ofTensorHom
    (pentagon := coprod.pentagon)
    (triangle := coprod.triangle)
    (associator_naturality := @coprod.associator_naturality _ _ _)

end

namespace monoidalOfHasFiniteCoproducts

variable [HasInitial C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteCoproducts

open scoped MonoidalCategory

@[simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl

@[simp]
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ₘ g = Limits.coprod.map f g :=
  rfl

@[simp]
theorem whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.coprod.map (𝟙 X) f :=
  rfl

@[simp]
theorem whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.coprod.map f (𝟙 Z) :=
  rfl

@[simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl

@[simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl

@[simp]
theorem leftUnitor_inv (X : C) : (λ_ X).inv = Limits.coprod.inr :=
  rfl

@[simp]
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl

theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) :=
  rfl

end monoidalOfHasFiniteCoproducts

section

attribute [local instance] monoidalOfHasFiniteCoproducts

open MonoidalCategory

/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps]
def symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] :
    SymmetricCategory C where
  braiding := Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y := by simp

end

namespace monoidalOfHasFiniteProducts

attribute [local instance] monoidalOfHasFiniteProducts

variable {C}
variable {D : Type*} [Category D] (F : C ⥤ D)
  [HasTerminal C] [HasBinaryProducts C]
  [HasTerminal D] [HasBinaryProducts D]

attribute [local simp] associator_hom_fst
instance : F.OplaxMonoidal where
  η := terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left _ _ := by simp [prodComparison_natural]
  δ_natural_right _ _ := by simp [prodComparison_natural]
  oplax_associativity _ _ _ := by
    dsimp
    ext
    · dsimp
      simp only [Category.assoc, prod.map_fst, Category.comp_id, prodComparison_fst, ←
        Functor.map_comp]
      erw [associator_hom_fst, associator_hom_fst]
      simp
    · dsimp
      simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc, prodComparison_fst,
        ← Functor.map_comp]
      erw [associator_hom_snd_fst, associator_hom_snd_fst]
      simp
    · dsimp
      simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc, prodComparison_snd, ←
        Functor.map_comp]
      erw [associator_hom_snd_snd, associator_hom_snd_snd]
      simp
  oplax_left_unitality _ := by ext; simp [← Functor.map_comp]
  oplax_right_unitality _ := by ext; simp [← Functor.map_comp]

open Functor.OplaxMonoidal

lemma η_eq : η F = terminalComparison F := rfl
lemma δ_eq (X Y : C) : δ F X Y = prodComparison F X Y := rfl

variable [PreservesLimit (Functor.empty.{0} C) F]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]

instance : IsIso (η F) := by dsimp [η_eq]; infer_instance
instance (X Y : C) : IsIso (δ F X Y) := by dsimp [δ_eq]; infer_instance

/-- Promote a finite products preserving functor to a monoidal functor between
categories equipped with the monoidal category structure given by finite products. -/
instance : F.Monoidal := .ofOplaxMonoidal F

end monoidalOfHasFiniteProducts

end CategoryTheory
