/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal

/-!
# Orthogonals are closed under (co)limits, quotients and subobjects

Let `P` be a property of objects in a category with zero morphisms. We show that the left
orthogonal `P.leftOrthogonal` is closed under quotients and under colimits of any shape, and,
dually, that the right orthogonal `P.rightOrthogonal` is closed under subobjects and under
limits of any shape.

These are registered as instances of `IsClosedUnderQuotients`, `IsClosedUnderColimitsOfShape`,
`IsClosedUnderSubobjects` and `IsClosedUnderLimitsOfShape`. Closure of the orthogonals under
extensions is shown in `Mathlib/CategoryTheory/Abelian/OrthogonalClosed.lean`; together these
form the easy direction of [S. E. Dickson][dickson1966]'s characterisation of torsion classes,
see `CategoryTheory.Abelian.isTorsionClass_iff`.

## References

* [S. E. Dickson, *A torsion theory for Abelian categories*][dickson1966]
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- The left orthogonal of a property of objects is closed under quotients. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderQuotients where
  prop_of_epi f _ hX := (P.leftOrthogonal_iff _).mpr
    fun _ g hZ ↦ zero_of_epi_comp f (hX (f ≫ g) hZ)

/-- The left orthogonal of a property of objects is closed under colimits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simp only [comp_zero]
    exact hX.prop_diag_obj j (hX.ι.app j ≫ f) hY

/-- The right orthogonal of a property of objects is closed under subobjects. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderSubobjects where
  prop_of_mono i _ hY := (P.rightOrthogonal_iff _).mpr
    fun _ f hX ↦ zero_of_comp_mono i (hY (f ≫ i) hX)

/-- The right orthogonal of a property of objects is closed under limits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isLimit.hom_ext
    intro j
    simp only [zero_comp]
    exact hX.prop_diag_obj j (f ≫ hX.π.app j) hY

end HasZeroMorphisms

end ObjectProperty

end CategoryTheory
