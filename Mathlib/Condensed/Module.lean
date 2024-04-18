import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Condensed.Basic

universe u

open CategoryTheory Limits

abbrev CondensedMod (R : Type (u+1)) [Ring R] := Condensed.{u} (ModuleCat.{u+1} R)

noncomputable instance (R : Type (u+1)) [Ring R] : Abelian (CondensedMod.{u} R) := sheafIsAbelian
