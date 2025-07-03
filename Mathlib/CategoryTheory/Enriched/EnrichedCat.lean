import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

universe w v u u₁ u₂

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

namespace EnrichedFunctor

variable (C : Type u₁) [EnrichedCategory.{w, v, u₁} V C]
variable (D : Type u₂) [EnrichedCategory.{w, v, u₂} V D]
variable (F G : EnrichedFunctor V C D)

instance category : Category (EnrichedFunctor V C D) where
  Hom F G := GradedNatTrans Center.tensorUnit  F G
  id F := sorry

end EnrichedFunctor

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

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  homCategory := fun _ _ => sorry --Functor.category
  whiskerLeft {_} {_} {_} F _ _ η := _ --whiskerLeft F η
  whiskerRight {_} {_} {_} _ _ η H := _ --whiskerRight η H
  associator {_} {_} {_} _ := _ --Functor.associator
  leftUnitor {_} _ := _ --Functor.leftUnitor
  rightUnitor {_} _ := _ --Functor.rightUnitor
  pentagon := fun {_} {_} {_} {_} {_} => _ --Functor.pentagon
  triangle {_} {_} {_} := _ --Functor.triangle

end EnrichedCat

end CategoryTheory
