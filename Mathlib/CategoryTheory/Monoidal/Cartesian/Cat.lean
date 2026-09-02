/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
/-!
# Chosen finite products in `Cat`

This file proves that the Cartesian product of a pair of categories agrees with the
product in `Cat`, and provides the associated `CartesianMonoidalCategory` instance.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Cat

open Limits

attribute [local instance] uliftCategory in
/-- The chosen terminal object in `Cat`. -/
abbrev chosenTerminal : Cat.{v, u} := Cat.of (ULift (ULiftHom (Discrete Unit)))

attribute [local instance] uliftCategory in
/-- The chosen terminal object in `Cat` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal.{v, u} :=
  IsTerminal.ofUniqueHom (fun C ↦ ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ ↦ rfl

/-- The type of functors out of the chosen terminal category is equivalent to the type of objects
in the target category. TODO: upgrade to an equivalence of categories. -/
def fromChosenTerminalEquiv {C : Type u} [Category.{v} C] : Cat.chosenTerminal ⥤ C ≃ C where
  toFun F := F.obj ⟨⟨()⟩⟩
  invFun := (Functor.const _).obj
  left_inv _ := by
    apply Functor.ext
    · rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (Functor.map_id _ _).symm
    · intro; rfl
  right_inv _ := rfl

/-- The chosen product of categories `C × D` yields a product cone in `Cat`. -/
def prodCone (C D : Cat.{v, u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

/-- The product cone in `Cat` is indeed a product. -/
def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : CartesianMonoidalCategory Cat :=
  .ofChosenFiniteProducts ⟨_, chosenTerminalIsTerminal⟩ fun X Y ↦
    { cone := X.prodCone Y, isLimit := isLimitProdCone X Y }

instance : BraidedCategory Cat := .ofCartesianMonoidalCategory

/-- A monoidal instance for `Cat` is provided from the `CartesianMonoidalCategory` instance. -/
example : MonoidalCategory Cat := by infer_instance

/-- A symmetric monoidal instance for `Cat` is provided through
`CartesianMonoidalCategory.toSymmetricCategory`. -/
example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

lemma tensorObj (C : Cat) (D : Cat) : C ⊗ D = Cat.of (C × D) := rfl

lemma whiskerLeft (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B) :
    X ◁ F = ((𝟭 X).prod F.toFunctor).toCatHom := rfl

lemma whiskerLeft_fst (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ := rfl

lemma whiskerLeft_snd (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ ⋙ f.toFunctor := rfl

lemma whiskerRight {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    f ▷ X = (f.toFunctor.prod (𝟭 X)).toCatHom := rfl

lemma whiskerRight_fst {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ ⋙ f.toFunctor := rfl

lemma whiskerRight_snd {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ := rfl

lemma tensorHom {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y) :
    f ⊗ₘ g = (f.toFunctor.prod g.toFunctor).toCatHom := rfl

lemma tensorUnit : 𝟙_ Cat = Cat.chosenTerminal := rfl

lemma associator_hom (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).hom = (Functor.prod' (Prod.fst (X × Y) Z ⋙ Prod.fst X Y)
      ((Functor.prod' ((Prod.fst (X × Y) Z ⋙ Prod.snd X Y))
      (Prod.snd (X × Y) Z : (X × Y) × Z ⥤ Z)))).toCatHom := rfl

lemma associator_inv (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).inv = (Functor.prod' (Functor.prod' (Prod.fst X (Y × Z) : X × (Y × Z) ⥤ X)
      (Prod.snd X (Y × Z) ⋙ Prod.fst Y Z)) (Prod.snd X (Y × Z) ⋙ Prod.snd Y Z)).toCatHom := rfl

lemma leftUnitor_hom (C : Cat.{v, u}) : (λ_ C).hom = (Prod.snd _ _).toCatHom := rfl

lemma leftUnitor_inv (C : Cat.{v, u}) : (λ_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toCatHom := rfl

lemma rightUnitor_hom (C : Cat.{v, u}) : (ρ_ C).hom = (Prod.fst _ _).toCatHom := rfl

lemma rightUnitor_inv (C : Cat.{v, u}) : (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCatHom := rfl

end CategoryTheory.Monoidal
