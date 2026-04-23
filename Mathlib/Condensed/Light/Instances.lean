/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# `HasSheafify` instances

In this file, we obtain a `HasSheafify (coherentTopology LightProfinite.{u}) (Type u)`
instance (and similarly for other concrete categories). These instances
are not obtained automatically because `LightProfinite.{u}` is a large category,
but as it is essentially small, the instances can be obtained using the results
in the file `Mathlib/CategoryTheory/Sites/Equivalence.lean`.

-/

@[expose] public section

universe u u' v

open CategoryTheory Limits

namespace LightProfinite

variable (A : Type u') [Category.{u} A] [HasLimits A] [HasColimits A]
  {FA : A → A → Type v} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [PreservesFilteredColimits (forget A)]
  [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]

instance hasSheafify :
    HasSheafify (coherentTopology LightProfinite.{u}) A :=
  hasSheafifyEssentiallySmallSite _ _

instance hasSheafify_type :
    HasSheafify (coherentTopology LightProfinite.{u}) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

instance : (coherentTopology LightProfinite.{u}).WEqualsLocallyBijective A :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end LightProfinite
