/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

#align_import algebra.category.Group.zero from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace GroupCat

@[to_additive]
theorem isZero_of_subsingleton (G : GroupCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
set_option linter.uppercaseLean3 false in
#align Group.is_zero_of_subsingleton GroupCat.isZero_of_subsingleton
set_option linter.uppercaseLean3 false in
#align AddGroup.is_zero_of_subsingleton AddGroupCat.isZero_of_subsingleton

@[to_additive AddGroupCat.hasZeroObject]
instance : HasZeroObject GroupCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end GroupCat

namespace CommGroupCat

@[to_additive]
theorem isZero_of_subsingleton (G : CommGroupCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
set_option linter.uppercaseLean3 false in
#align CommGroup.is_zero_of_subsingleton CommGroupCat.isZero_of_subsingleton
set_option linter.uppercaseLean3 false in
#align AddCommGroup.is_zero_of_subsingleton AddCommGroupCat.isZero_of_subsingleton

@[to_additive AddCommGroupCat.hasZeroObject]
instance : HasZeroObject CommGroupCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end CommGroupCat
