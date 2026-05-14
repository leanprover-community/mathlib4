/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Path
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Paths between points of an object of `TopCat`

This file introduces a structure `TopCat.Path` for paths between
two points of an object `X : TopCat`. The data is defined using
a morphism `I ⟶ X` in the category `TopCat`.

-/

@[expose] public section

universe u

namespace TopCat

variable (X : TopCat.{u})

/-- Given two points `x` and `y` of `X : TopCat`, this is the type
of paths from `x` to `y`, defined using a morphism `I ⟶ X`.
Set `TopCat.pathEquiv` for the relation with `_root_.Path x y`. -/
@[ext]
protected structure Path (x y : X) where
  /-- a morphism from the unit interval -/
  hom : I ⟶ X
  hom₀ : hom 0 = x := by cat_disch
  hom₁ : hom 1 = y := by cat_disch

attribute [simp] Path.hom₀ Path.hom₁

variable {X} in
/-- The bijection between `TopCat.Path X x y` and `_root_.Path x y`. -/
@[simps!]
def pathEquiv {x y : X} : X.Path x y ≃ _root_.Path x y where
  toFun p :=
    { toContinuousMap := p.hom.hom.comp TopCat.I.homeomorph.symm
      source' := p.hom₀
      target' := p.hom₁ }
  invFun p :=
    { hom := ofHom (p.toContinuousMap.comp (toContinuousMap TopCat.I.homeomorph))
      hom₀ := p.source'
      hom₁ := p.target' }

end TopCat
