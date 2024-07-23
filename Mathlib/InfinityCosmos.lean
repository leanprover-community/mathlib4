import Mathlib.AlgebraicTopology.Nerve
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory

noncomputable section

namespace CategoryTheory
open Category Limits Functor
universe v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K]

class InfinityCosmosBase extends SimplicialCategory K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  comp_isIsoFibration {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (f ≫ g)
  has_terminal : HasTerminal K
  all_objects_fibrant {X : K} (f : X ⟶ ⊤_ K) : IsIsoFibration f
  has_products : HasBinaryProducts K
  prod_map_fibrant {X Y X' Y' : K} {f : X ⟶ Y} {g : X' ⟶ Y'} :
    IsIsoFibration f → IsIsoFibration g →  IsIsoFibration (prod.map f g)

namespace InfinityCosmosBase
variable [InfinityCosmosBase.{v} K]

def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

infixr:25  " ↠ " => IsoFibration


class InfinityCosmos extends InfinityCosmosBase K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
