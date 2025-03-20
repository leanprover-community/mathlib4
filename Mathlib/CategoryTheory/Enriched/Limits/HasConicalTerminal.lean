/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts

/-!
## existence of conical terminal objects
gi-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits HasConicalLimit

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C)

variable [HasConicalLimit V F]

/-- A category has a conical terminal object
if it has a conical limit over the empty diagram. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

example [HasConicalTerminal V C] : HasTerminal C := inferInstance

/-! ### Conical Products -/

example [HasConicalProducts.{0} V C] : HasConicalTerminal V C := inferInstance

instance HasConicalProducts.hasConicalTerminal [HasConicalProducts.{w} V C] :
    HasConicalTerminal V C :=
  HasConicalLimitsOfShape.of_equiv V C (emptyEquivalence.functor)

end CategoryTheory.Enriched
