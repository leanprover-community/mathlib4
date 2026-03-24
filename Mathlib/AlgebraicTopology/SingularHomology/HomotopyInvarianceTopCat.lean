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

-/

@[expose] public section

universe v u w

open AlgebraicTopology CategoryTheory Limits

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y}

noncomputable def singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.toSSet.toSimplicialObjectHomotopy.singularChainComplexFunctorObjMap R

open HomologicalComplex in
lemma congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C]
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
    homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

end TopCat.Homotopy
