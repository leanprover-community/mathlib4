import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!

# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.

-/

@[expose] public section

universe v u

variable (R : Type u) [Ring R]

instance [Small.{v} R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)
