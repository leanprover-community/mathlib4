import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

universe w v u u₁ u₂

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- Category of `V`-enriched categories for a monoidal category `V`. -/
def EnrichedCat := Bundled (EnrichedCategory.{w, v, u} V)

namespace EnrichedCat

instance : CoeSort (EnrichedCat V) (Type u) :=
  ⟨Bundled.α⟩

instance str (C : EnrichedCat.{w, v, u} V) : EnrichedCategory.{w, v, u} V C :=
  Bundled.str C

/-- Construct a bundled `EnrichedCat` from the underlying type and the typeclass. -/
def of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V :=
  Bundled.of C

open EnrichedCategory

def whiskerLeft {C D E : EnrichedCat.{w, v, u} V}
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : EnrichedNatTrans G H) :
    EnrichedFunctor.comp V F G ⟶ EnrichedFunctor.comp V F H where
  app X := α.app (F.obj X)
  naturality X Y := by
    simp only [EnrichedFunctor.comp_obj, F.comp_map]
    rw [← whiskerLeft_comp_tensorHom, Category.assoc, ← GradedNatTrans.naturality α,
     ← whiskerRight_comp_tensorHom]
    simp

def whiskerRight {C D E : EnrichedCat.{w, v, u} V}
    {F G : EnrichedFunctor V C D} (α : EnrichedNatTrans F G) (H : EnrichedFunctor V D E) :
    EnrichedFunctor.comp V F H ⟶ EnrichedFunctor.comp V G H where
  app X := α.app X ≫ H.map _ _
  naturality X Y := by
    simp only [Category.assoc, EnrichedFunctor.comp_obj, F.comp_map, tensor_comp]
    rw [← H.map_comp, reassoc_of% (GradedNatTrans.naturality α X Y)]
    simp

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H α := whiskerLeft V F α
  whiskerRight α H := whiskerRight V α H
  associator F G H := _ --Functor.associator
  leftUnitor {_} _ := _ --Functor.leftUnitor
  rightUnitor {_} _ := _ --Functor.rightUnitor
  pentagon := fun {_} {_} {_} {_} {_} => _ --Functor.pentagon
  triangle {_} {_} {_} := _ --Functor.triangle

end EnrichedCat

end CategoryTheory
