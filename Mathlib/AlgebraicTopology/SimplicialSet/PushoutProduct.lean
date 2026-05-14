/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
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
# Pushout-products of simplicial sets

Results about pushout-products and pullback-homs in the category of simplicial sets.

-/

@[expose] public section

universe v u

namespace SSet

open CategoryTheory MonoidalCategory

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

namespace Subcomplex

namespace unionProd

/-- The inclusion `(S.unionProd T).toSSet ⟶ X ⊗ Y` is isomorphic to the pushout-product
`S.ι □ T.ι`. -/
@[simps! -isSimp]
noncomputable
def ιIso : Arrow.mk (S.unionProd T).ι ≅ S.ι □ T.ι :=
  Arrow.isoMk' _ _ (isPushout S T).isoPushout (Iso.refl _)
    (by apply (unionProd.isPushout S T).hom_ext <;>
      simp [Functor.PushoutObjObj.ofHasPushout, Functor.PushoutObjObj.ι])

end unionProd

end Subcomplex

end SSet
