/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Module
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
public import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
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

# Equivalence of light condensed objects with sheaves on a small site
-/

@[expose] public section

universe u v w

open CategoryTheory Sheaf Functor

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

variable (C) in
/--
The equivalence of categories from light condensed objects to sheaves on a small site
equivalent to light profinite sets.
-/
noncomputable abbrev equivSmall :
    LightCondensed.{u} C ≌
      Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
        (coherentTopology LightProfinite.{u})) C :=
  (equivSmallModel LightProfinite).sheafCongr _ _ _

instance (X Y : LightCondensed.{u} C) : Small.{max u v} (X ⟶ Y) where
  equiv_small :=
    ⟨(equivSmall C).functor.obj X ⟶ (equivSmall C).functor.obj Y,
      ⟨(equivSmall C).fullyFaithfulFunctor.homEquiv⟩⟩

/--
Sheafifying is preserved under conjugating with the equivalence between light condensed objects
and sheaves on a small site.
-/
noncomputable def equivSmallSheafificationIso
    [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]
    [HasWeakSheafify ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) C] :
    (equivSmallModel LightProfinite.{u}).op.congrLeft.inverse ⋙ presheafToSheaf _ _ ⋙
      (equivSmall C).functor ≅
    presheafToSheaf _ _ :=
  (conjugateIsoEquiv (sheafificationAdjunction _ _)
    (((equivSmallModel LightProfinite.{u}).op.congrLeft.symm.toAdjunction.comp
    (sheafificationAdjunction _ _)).comp (equivSmall C).toAdjunction)).symm <|
  NatIso.ofComponents (fun X ↦ ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm)

variable (R : Type u) [CommRing R]

attribute [local simp] LightCondensed.forget in
set_option backward.isDefEq.respectTransparency false in
/--
Taking the free condensed module is preserved under conjugating with the equivalence between
light condensed objects and sheaves on a small site.
-/
noncomputable def equivSmallFreeIso :
    (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (ModuleCat R)).functor ≅
    Sheaf.composeAndSheafify _ (ModuleCat.free R) :=
  conjugateIsoEquiv (Sheaf.adjunction _ (ModuleCat.adj R))
    (((equivSmall _).symm.toAdjunction.comp
      (freeForgetAdjunction R)).comp (equivSmall _).toAdjunction) |>.symm <| by
  refine NatIso.ofComponents
    (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (isoWhiskerRight ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm _ ≪≫
        (Functor.associator _ _ _)))

end LightCondensed
