/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Homotopy invariance of singular homology

In this file, we show that for any homotopy `H : TopCat.Homotopy f g`
between two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat`,
the corresponding morphisms on the singular chain complexes
are homotopic, and in particular the induced morphisms
on singular homology are equal.

The proof proceeds by observing that this result is a particular
case of the homotopy invariance of the homology of simplicial sets
(see the file `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`),
applied to the morphisms `TopCat.toSSet.map f` and `TopCat.toSSet.map g`
between the singular simplicial sets of `X` and `Y`. That the homotopy `H`
induces a homotopy between these morphisms of simplicial sets
is the definition `TopCat.Homotopy.toSSet` which appeared in the file
`Mathlib/Topology/Homotopy/TopCat/ToSSet.lean`.

-/

@[expose] public section

universe v u w

open AlgebraicTopology CategoryTheory Limits

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- Two homotopic morphisms in `TopCat` induce homotopic morphisms on the
singular chain complexes. -/
noncomputable def singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.toSSet.singularChainComplexFunctorObjMap R

open HomologicalComplex in
lemma congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C]
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
    homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

end TopCat.Homotopy
