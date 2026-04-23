/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
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
import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.Topology.MetricSpace.Bounded
/-!

# Light condensed objects

This file defines the category of light condensed objects in a category `C`, following the work
of Clausen-Scholze (see https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).

-/

@[expose] public section

universe u v w

open CategoryTheory Limits

/--
`LightCondensed.{u} C` is the category of light condensed objects in a category `C`, which are
defined as sheaves on `LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology LightProfinite.{u}) C

/--
Light condensed sets. Because `LightProfinite` is an essentially small category, we don't need the
same universe bump as in `CondensedSet`.
-/
abbrev LightCondSet := LightCondensed.{u} <| Type u

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

@[deprecated ObjectProperty.FullSubcategory.id_hom (since := "2026-04-08")]
lemma id_hom (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
lemma comp_hom {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
lemma hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.hom.app S = g.hom.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end LightCondensed

namespace LightCondSet

@[deprecated NatTrans.naturality_apply (since := "2026-03-19")]
lemma hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) := by
  simp

end LightCondSet
