/-
Copyright (c) 2024 Uni Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uni Marx
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
open CategoryTheory CategoryTheory.Limits

/-!
# Limits in the category of relations

We show that the category of relations has zero objects and zero morphisms.

## TODO

* Show existence of arbitrary biproducts

-/

universe v u w

namespace CategoryTheory.Limits

namespace RelCat

/-- The empty type is a zero object in the category of relations. -/
instance : HasZeroObject RelCat where zero :=
  ⟨Empty,
    { unique_to := fun _ =>
      ⟨{ default := Empty.elim,
          uniq := fun _ => funext (fun a => Empty.elim a)}⟩
      unique_from := fun _ =>
      ⟨{ default := fun _ => Empty.elim,
          uniq := fun _ => funext₂ (fun _ b => Empty.elim b)}⟩}⟩

/-- The empty relation is the zero morphism for relations. -/
instance : HasZeroMorphisms RelCat where
  zero X Y := ⟨fun _ _ => False⟩
  comp_zero _ _ := by
    ext
    exact ⟨fun ⟨_,_,a⟩ => a, False.elim⟩
  zero_comp _ _ _ _ := by
    ext
    exact ⟨fun ⟨_,a,_⟩ => a, False.elim⟩

end RelCat
end CategoryTheory.Limits
