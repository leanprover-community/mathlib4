import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The category of abelian groups is well-powered
-/

@[expose] public section


open CategoryTheory

universe u

namespace AddCommGrpCat

instance wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u} :=
  wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

end AddCommGrpCat
