/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Condensed.Light.Instances
public import Mathlib.Condensed.Light.Module
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
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

# Closed symmetric monoidal structure on light condensed modules

We define a symmetric monoidal structure on light condensed modules by localizing the symmetric
monoidal structure on the presheaf category. By Day's reflection theorem, we obtain a closed
structure.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : (coherentTopology LightProfinite.{u}).W (A := ModuleCat.{u} R) |>.IsMonoidal :=
  GrothendieckTopology.W.transport_isMonoidal _ _
    ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u}))
    (equivSmallModel.{u} LightProfinite.{u}).inverse

instance : MonoidalCategory (LightCondMod.{u} R) :=
  monoidalCategory _ _

instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod _))

instance : SymmetricCategory (LightCondMod.{u} R) :=
  symmetricCategory _ _

instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  .ofEquiv _ (equivSmallModel LightProfinite).op.congrLeft.toAdjunction

instance : MonoidalClosed (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Sheaf _ _))

instance : (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal :=
  inferInstance

instance : (free R).Monoidal := inferInstanceAs (composeAndSheafify _ _).Monoidal

end LightCondensed
