/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Homotopy invariance of simplicial homology

This file proves that homotopic morphisms of simplicial sets induce
the same maps on singular homology (with coefficients in an object `R`
of a preadditive category `C` with coproducts).

First, in the case where the homotopy between two morphisms of simplicial sets
`f : X ⟶ Y` and `g : X ⟶ Y` is given as combinatorial simplicial homotopy
(`SimplicialObject.Homotopy`), i.e. as family of morphisms `X _⦋n⦌ ⟶ Y _⦋n + 1⦌`,
we use the fact that we still have a similar kind of homotopy between
the corresponding morphisms on the simplicial objects in `C` that are
obtained after applying the "free object" functor `sigmaConst.obj R : Type _ ⥤ C`
degreewise, and that a combinatoral homotopy of simplicial objects
in a preadditive category induces a homotopy on the alternating face map
complexes (see `SimplicialObject.Homotopy.toChainHomotopy`, which is defined
in the file `Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`).

Secondly, in the case where the homotopy between `f` and `g` is given
by a usual homotopy of morphisms of simplicial sets (`SSet.Homotopy`),
i.e. by a morphism `h : X ⊗ Δ[1] ⟶ Y`, we apply the construction above
to the combinatorial simplicial homotopy that is deduced from `h` by
using the definition `SSet.Homotopy.toSimplicialObjectHomotopy` from the file
`Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

/-! The invariance of singular homology (of topological spaces)
is obtained in the file
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvarianceTopCat.lean`. -/
assert_not_exists TopologicalSpace

universe v u w

open CategoryTheory Limits AlgebraicTopology.SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} {f g : X ⟶ Y}

namespace CategoryTheory.SimplicialObject.Homotopy

/--
If `f` and `g` are simplicially homotopic maps of simplicial sets,
then they induce chain-homotopic maps on the singular chain complexes
with coefficients in `R`. The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.chainComplexMap` for the
variant using `SSet.Homotopy` as an assumption.
-/
noncomputable def sSetChainComplexMap
    (H : SimplicialObject.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R) :=
  toChainHomotopy (H.whiskerRight _)

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap :=
  sSetChainComplexMap

@[deprecated (since := "2026-03-24")]
alias _root_.singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy :=
  sSetChainComplexMap

open HomologicalComplex in
/--
Simplicially homotopic maps of simplicial sets induce the same map on
homology of the singular chain complex (with coefficients in `R`).
The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.congr_homologyMap` for the
variant using `SSet.Homotopy` as an assumption.
-/
theorem congr_sSetHomologyMap [CategoryWithHomology C]
    (H : SimplicialObject.Homotopy f g) (R : C) (n : ℕ) :
    SSet.homologyMap f R n = SSet.homologyMap g R n :=
  (H.sSetChainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-03-24")]
alias singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy :=
  congr_sSetHomologyMap

@[deprecated (since := "2026-04-05")] alias congr_homologyMap_singularChainComplexFunctor :=
  congr_sSetHomologyMap

end CategoryTheory.SimplicialObject.Homotopy

namespace SSet.Homotopy

/--
If `f` and `g` are homotopic maps of simplicial sets, then they induce chain-homotopic
maps on the singular chain complexes with coefficients in `R`.
-/
noncomputable def chainComplexMap
    (H : SSet.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R)  :=
  H.toSimplicialObjectHomotopy.sSetChainComplexMap R

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap := chainComplexMap

open HomologicalComplex in
/--
Homotopic maps of simplicial sets induce the same map on homology of the singular
chain complex (with coefficients in `R`).
-/
theorem congr_homologyMap [CategoryWithHomology C]
    (H : SSet.Homotopy f g) (R : C) (n : ℕ) :
    SSet.homologyMap f R n = SSet.homologyMap g R n :=
  (H.chainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-04-05")]
alias congr_homologyMap_singularChainComplexFunctor := congr_homologyMap

end SSet.Homotopy
