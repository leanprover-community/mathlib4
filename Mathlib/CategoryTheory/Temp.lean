import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

namespace CategoryTheory

universe v u

open MonoidalCategory

class ChosenMonoidalClosed (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] where
  closed (X : C) : Closed X

/-
def cartesianClosedOfChosenCartesianClosed
    {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C]
    (rightAdj : C ⥤ C) (adj : (X : C) → tensorLeft X ⊣ rightAdj) :
  CartesianClosed C where
    closed := _
-/

-- namespace ChosenMonoidalClosed

/-
instance (priority := 100)
    (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C] :
    CartesianClosed C where
-/

variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C]

open Simplicial SimplexCategory

noncomputable
def SSetIHom (X Y : SSet) : SSet where
  obj := fun ⟨n⟩ ↦ (X ⊗ Δ[len n]) ⟶ Y
  map := fun f g ↦ X ◁ SSet.standardSimplex.map f.unop ≫ g

noncomputable
def SSetIHomMap (X Y Z : SSet) (f : Y ⟶ Z) : SSetIHom X Y ⟶ SSetIHom X Z where
  app _ g := g ≫ f

noncomputable
def SSetRightAdj (X : SSet) : SSet ⥤ SSet where
  obj Y := SSetIHom X Y
  map f := SSetIHomMap _ _ _ f

def SSetAdj (X : SSet) : tensorLeft X ⊣ SSetRightAdj X := sorry
