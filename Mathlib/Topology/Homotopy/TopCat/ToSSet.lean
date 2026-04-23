/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
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

/-!
# The singular simplicial set functor preserves homotopies

In this file, we define `TopCat.Homotopy.toSSet`, which shows that
if two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat` are homotopic (`h : Homotopy f g`),
then so are their images by the functor `TopCat.toSSet : TopCat ⥤ SSet`.
Indeed, if we apply the singular simplicial set functor to the morphism `h.h : X ⊗ I ⟶ Y`
and use that this functor commutes with products, we obtain a morphism
`toSSet.obj X ⊗ toSSet.obj I ⟶ toSSet.obj Y`: the homotopy
`toSSet.obj X ⊗ Δ[1] ⟶ toSSet.obj Y` is deduced by using
the morphism `SSet.stdSimplex.toSSetObjI : Δ[1] ⟶ toSSet.obj I`,
which corresponds to the isomorphism `SSet.stdSimplex.toTopObjIsoI|Δ[1]| ≅ TopCat.I`
by adjunction.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

/-- If two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat` are homotopic, then so
are their images by the functor `TopCat.toSSet : TopCat ⥤ SSet`. -/
noncomputable def TopCat.Homotopy.toSSet {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : Homotopy f g) :
    SSet.Homotopy (toSSet.map f) (toSSet.map g) where
  h := _ ◁ SSet.stdSimplex.toSSetObjI ≫ μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map h.h
  h₀ := by simp [← Functor.map_comp]
  h₁ := by simp [← Functor.map_comp]
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩
