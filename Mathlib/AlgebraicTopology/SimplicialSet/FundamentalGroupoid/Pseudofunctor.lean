/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# ...

-/

@[expose] public section

universe u

open CategoryTheory Bicategory

namespace SSet

namespace FundamentalGroupoid

def pseudofunctor : LocallyDiscrete SSet.{u} ⥤ᵖ  Cat.{u, u} := by
  refine LocallyDiscrete.mkPseudofunctor (fun X ↦ .of (FundamentalGroupoid X))
    (fun f ↦ (mapFundamentalGroupoid f).toCatHom) ?_ sorry sorry sorry sorry
  sorry

end FundamentalGroupoid

end SSet
