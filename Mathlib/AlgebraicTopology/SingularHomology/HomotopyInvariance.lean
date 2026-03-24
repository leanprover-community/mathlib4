/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Homotopy invariance of singular homology (simplicial step)

This file proves that simplicially homotopic morphisms of simplicial sets induce the same maps
on singular homology (with coefficients in an object of a preadditive category with coproducts).
-/

@[expose] public section

universe v u w

open CategoryTheory Limits AlgebraicTopology.SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} {f g : X ⟶ Y}

namespace CategoryTheory.SimplicialObject.Homotopy

/--
If `f` and `g` are simplicially homotopic maps of simplicial sets, then they induce chain-homotopic
maps on the singular chain complexes with coefficients in `R`.
-/
noncomputable def singularChainComplexFunctorObjMap
    (H : Homotopy f g) (R : C) :
    _root_.Homotopy
      (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  toChainHomotopy (H.whiskerRight _)

@[deprecated (since := "2026-03-24")]
alias _root_.singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy :=
  Homotopy.singularChainComplexFunctorObjMap

open HomologicalComplex in
/--
Simplicially homotopic maps of simplicial sets induce the same map on homology of the singular
chain complex (with coefficients in `R`).
-/
theorem congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C]
    (H : Homotopy f g) (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
    homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

@[deprecated (since := "2026-03-24")]
alias singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy :=
  congr_homologyMap_singularChainComplexFunctor

end CategoryTheory.SimplicialObject.Homotopy
