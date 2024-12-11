import Mathlib.Algebra.Category.Grp.AB5
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

universe u

open CategoryTheory Limits

variable (R : Type*) [Ring R]

instance : AB5 (ModuleCat.{u} R) where
  ofShape J _ _ :=
    hasExactColimitsOfShape_transport (J := J) (forget₂ (ModuleCat R) AddCommGrp)

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _

instance : AB4Star (ModuleCat.{u} R) := sorry
