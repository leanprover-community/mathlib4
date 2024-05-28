import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Presheaf

namespace CategoryTheory

universe v v' u u'

open MonoidalCategory

class ChosenCartesianClosed (C : Type u) [Category.{v} C] where
  [chosenFiniteProducts: ChosenFiniteProducts C]
  rightAdj (X : C) : C ⥤ C
  adj (X : C) : @tensorLeft _ _ (monoidalOfHasFiniteProducts _) X ⊣ rightAdj X

namespace ChosenCartesianClosed

instance (C : Type u) [Category.{v} C] [i : ChosenCartesianClosed C] : ChosenFiniteProducts C :=
  i.chosenFiniteProducts

noncomputable
def ofCartesianClosed (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C]
    [CartesianClosed C] : ChosenCartesianClosed C :=
  letI _ := ChosenFiniteProducts.ofFiniteProducts C
  letI _ : MonoidalCategory C := monoidalOfHasFiniteProducts C
{ rightAdj := fun X ↦ ihom X
  adj := fun X ↦ ihom.adjunction X
}

noncomputable
instance (C : Type u) [Category.{v} C] [ChosenCartesianClosed C] : CartesianClosed C :=
  letI _ : MonoidalCategory C := monoidalOfHasFiniteProducts C
  {
    closed := fun X ↦ {
      rightAdj := rightAdj X
      adj := adj X }
  }

variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenCartesianClosed C]

instance (c : C) : Closed c := sorry

noncomputable
example (D : Type u') [Category.{v'} D] : ChosenFiniteProducts (D ⥤ C) := inferInstance

instance (D : Type u') [Category.{v'} D] (F : D ⥤ C) : Closed F where
  rightAdj := {
    obj := fun G ↦ {
      obj := fun d ↦ F.obj d ⟶[C] G.obj d
      map := by
        intro X Y f
        sorry
    }
    map := sorry
  }
  adj := sorry
