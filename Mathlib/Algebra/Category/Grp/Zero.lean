/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace GrpCat

@[to_additive]
theorem isZero_of_subsingleton (G : GrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]
instance : HasZeroObject GrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive AddGrpCat.hasZeroMorphisms]
instance : HasZeroMorphisms GrpCat where
  zero _ _ := ⟨ofHom 1⟩
  comp_zero := by rfl_cat
  zero_comp _ _ _ f := hom_ext (MonoidHom.ext fun x ↦ MonoidHom.map_one (Hom.hom f))

end GrpCat

namespace CommGrpCat

@[to_additive]
theorem isZero_of_subsingleton (G : CommGrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]
instance : HasZeroObject CommGrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive AddCommGrpCat.hasZeroMorphisms]
instance : HasZeroMorphisms CommGrpCat where
  zero _ _ := ⟨ofHom 1⟩
  comp_zero := by rfl_cat
  zero_comp _ _ _ f := hom_ext (MonoidHom.ext fun x ↦ MonoidHom.map_one (Hom.hom f))

end CommGrpCat
