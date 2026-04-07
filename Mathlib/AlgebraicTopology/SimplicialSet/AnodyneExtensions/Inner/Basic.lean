/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.CategoryTheory.SmallObject.Basic

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial

namespace SSet

open MorphismProperty

open modelCategoryJoyal in
def innerAnodyneExtensions : MorphismProperty SSet.{u} := innerFibrations.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts--, IsStableUnderTransfiniteComposition,
  --IsStableUnderCoproducts

end SSet
