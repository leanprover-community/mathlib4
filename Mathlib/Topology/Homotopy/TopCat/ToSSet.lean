/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# The singular simplicial set functor preserves homotopies

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
