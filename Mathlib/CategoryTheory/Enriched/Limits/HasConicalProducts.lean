/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalProduct (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C] {I : Type w} (f : I → C) :=
  HasConicalLimit V (Discrete.functor f)

-- -- TODO: unecessary?
-- instance HasConicalProduct.hasProduct {I : Type w} (f : I → C) [HasConicalProduct V f] :
--     HasProduct f := inferInstance
example (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C] {I : Type w} (f : I → C)
    [HasConicalProduct V f] :
    HasProduct f :=
  inferInstance

/-- Has conical products if all discrete diagrams of bounded size have conical products. -/
class HasConicalProducts (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- All discrete diagrams of bounded size have conical products. -/
  hasConicalLimitsOfShape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance
-- TODO: is the `:= by infer_instance` good for anything?
namespace HasConicalProducts

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

instance hasProducts [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasProducts.{w, v, u} C := by
  intro I
  constructor
  intro f
  have := hyp.hasConicalLimitsOfShape I
  have : HasConicalLimit V f := inferInstance
  infer_instance

end HasConicalProducts

end CategoryTheory.Enriched
