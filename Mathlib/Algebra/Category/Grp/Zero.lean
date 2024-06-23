/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Grp.Basic
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

namespace Grp

@[to_additive]
theorem isZero_of_subsingleton (G : Grp) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
set_option linter.uppercaseLean3 false in
#align Group.is_zero_of_subsingleton Grp.isZero_of_subsingleton
set_option linter.uppercaseLean3 false in
#align AddGroup.is_zero_of_subsingleton AddGrp.isZero_of_subsingleton

@[to_additive AddGrp.hasZeroObject]
instance : HasZeroObject Grp :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end Grp

namespace CommGrp

@[to_additive]
theorem isZero_of_subsingleton (G : CommGrp) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
set_option linter.uppercaseLean3 false in
#align CommGroup.is_zero_of_subsingleton CommGrp.isZero_of_subsingleton
set_option linter.uppercaseLean3 false in
#align AddCommGroup.is_zero_of_subsingleton AddCommGrp.isZero_of_subsingleton

@[to_additive AddCommGrp.hasZeroObject]
instance : HasZeroObject CommGrp :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end CommGrp
