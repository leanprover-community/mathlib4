/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Topology.Category.LightProfinite.Cartesian
public import Mathlib.Condensed.Light.TopComparison
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.Condensed.Light.TopCatAdjunction
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
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functors from categories of topological spaces to light condensed sets

This file defines the embedding of the test objects (light profinite sets) into light condensed
sets.

## Main definitions

* `lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u}`
  is the yoneda sheaf functor.

-/

@[expose] public section

universe u v

open CategoryTheory Limits Functor

/-- The functor from `LightProfinite.{u}` to `LightCondSet.{u}` given by the Yoneda sheaf. -/
def lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u} :=
  (coherentTopology LightProfinite).yoneda

/-- Dot notation for the value of `lightProfiniteToLightCondSet`. -/
abbrev LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u} :=
  lightProfiniteToLightCondSet.obj S

/-- `lightProfiniteToLightCondSet` is fully faithful. -/
abbrev lightProfiniteToLightCondSetFullyFaithful :
    lightProfiniteToLightCondSet.FullyFaithful :=
  (coherentTopology LightProfinite).yonedaFullyFaithful

instance : lightProfiniteToLightCondSet.Full :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full

instance : lightProfiniteToLightCondSet.Faithful :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

/--
The functor from `LightProfinite` to `LightCondSet` factors through `TopCat`.
-/
@[simps!]
noncomputable def lightProfiniteToLightCondSetIsoTopCatToLightCondSet :
    lightProfiniteToLightCondSet.{u} ≅ LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} :=
  dsimp% NatIso.ofComponents fun X ↦ FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _) <|
    NatIso.ofComponents fun S ↦ {
      hom := TypeCat.ofHom (fun f ↦ { toFun := f.hom })
      inv := TypeCat.ofHom (fun f ↦ InducedCategory.homMk (TopCat.ofHom f)) }

/--
The functor from `LightProfinite` to `LightCondSet` preserves countable limits.
-/
instance {J : Type} [SmallCategory J] [CountableCategory J] : PreservesLimitsOfShape J
    lightProfiniteToLightCondSet.{u} :=
  haveI : Functor.IsRightAdjoint topCatToLightCondSet.{u} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimitsOfShape J LightProfinite.toTopCat.{u} :=
    inferInstanceAs (PreservesLimitsOfShape J (lightToProfinite ⋙ Profinite.toTopCat))
  preservesLimitsOfShape_of_natIso lightProfiniteToLightCondSetIsoTopCatToLightCondSet.symm

/--
The functor from `LightProfinite` to `LightCondSet` preserves finite limits.
-/
instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits _ := inferInstance

/--
The functor from `LightProfinite` to `LightCondSet` is monoidal with respect to the cartesian
monoidal structure.
-/
noncomputable instance : lightProfiniteToLightCondSet.{u}.Monoidal :=
  (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance |>.some

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u} :=
  inferInstanceAs <| PreservesFiniteCoproducts (coherentTopology _).yoneda
