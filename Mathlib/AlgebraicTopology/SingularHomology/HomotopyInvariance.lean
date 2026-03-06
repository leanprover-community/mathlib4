/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.SimplicialHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Homotopy invariance of singular homology (simplicial step)

This file proves that simplicially homotopic morphisms of simplicial sets induce the same maps
on singular homology (with coefficients in an object of a preadditive category with coproducts).
-/

@[expose] public section

universe v u

open CategoryTheory SimplicialObject Homotopy
open AlgebraicTopology.SSet

variable (C : Type u) [Category.{v} C]
variable [CategoryTheory.Preadditive C] [CategoryTheory.Limits.HasCoproducts C]
variable {C}
variable (R : C)
variable {X Y : SSet} (f g : X ⟶ Y)

/--
If `f` and `g` are simplicially homotopic maps of simplicial sets, then they induce chain-homotopic
maps on the singular chain complexes with coefficients in `R`.
-/
noncomputable def singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy
    (H : Homotopy f g) :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map g)
      (((singularChainComplexFunctor C).obj R).map f) := by
  simpa [singularChainComplexFunctor] using
    (toChainHomotopy (H := whiskerRight (F := (_ : Type _ ⥤ C)) H))

/--
Simplicially homotopic maps of simplicial sets induce the same map on homology of the singular
chain complex (with coefficients in `R`).
-/
theorem singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
    [CategoryWithHomology C]
    (H : Homotopy f g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor C _ n).map
        (((singularChainComplexFunctor C).obj R).map f) =
      (HomologicalComplex.homologyFunctor C _ n).map
        (((singularChainComplexFunctor C).obj R).map g) := by
  simpa [eq_comm] using
    (singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy
        (C := C) (R := R) (f := f) (g := g) H).homologyMap_eq n
