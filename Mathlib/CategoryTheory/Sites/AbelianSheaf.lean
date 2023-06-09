/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.LeftExact

/-!

Sheaves of abelian groups form an abelian category.

-/

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/--
The category of abelian sheaves on a category with a Grothendieck topology `J`.
This is defined as sheaves taking values in the category of abelian groups.
-/
abbrev AbelianSheaf := Sheaf J AddCommGroupCat.{max v u}

noncomputable instance AbelianSheaf.abelian : Abelian (AbelianSheaf J) :=
  letI : Limits.PreservesLimits (forget AddCommGroupCat.{max v u}) :=
    AddCommGroupCat.forgetPreservesLimits.{max v u, max v u}
  abelianOfAdjunction _ _ (asIso <| (sheafificationAdjunction _ _).counit)
    (sheafificationAdjunction _ _)

end CategoryTheory
