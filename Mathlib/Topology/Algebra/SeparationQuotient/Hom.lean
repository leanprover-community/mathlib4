/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Lift of `MonoidHom M N` to `MonoidHom (SeparationQuotient M) N`

In this file we define the lift of a continuous monoid homomorphism `f` from `M` to `N` to
`SeparationQuotient M`, assuming that `f` maps two inseparable elements to the same element.
-/

@[expose] public section

namespace SeparationQuotient

section Monoid

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- The lift of a monoid hom from `M` to a monoid hom from `SeparationQuotient M`. -/
@[to_additive /-- The lift of an additive monoid hom from `M` to an additive monoid hom from
`SeparationQuotient M`. -/]
noncomputable def liftContinuousMonoidHom [CommMonoid M] [ContinuousMul M] [CommMonoid N]
    (f : ContinuousMonoidHom M N) (hf : ∀ x y, Inseparable x y → f x = f y) :
    ContinuousMonoidHom (SeparationQuotient M) N where
  toFun := SeparationQuotient.lift f hf
  map_one' := map_one f
  map_mul' := Quotient.ind₂ <| map_mul f
  continuous_toFun := SeparationQuotient.continuous_lift.mpr f.2

@[to_additive (attr := simp)]
theorem liftContinuousCommMonoidHom_mk [CommMonoid M] [ContinuousMul M] [CommMonoid N]
    (f : ContinuousMonoidHom M N) (hf : ∀ x y, Inseparable x y → f x = f y) (x : M) :
    liftContinuousMonoidHom f hf (mk x) = f x := rfl

end Monoid

end SeparationQuotient
