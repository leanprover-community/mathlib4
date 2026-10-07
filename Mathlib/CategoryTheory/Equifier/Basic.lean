/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Equifier categories

Let `F G : C ⥤ D` be a parallel pair of functors of categories, let Φ and Ψ be
natural transformations `F ⟶ G`.
In this file, we define a category `Equifier Φ Ψ`.
It is the full subcategory of `C` consisting of objects `c : C` such that `Φ.app c = Ψ.app c`.

We prove that this full subcategory is closed under all colimits that exist in `C`
and that are preserved by `F` and is closed under all limits in `C` preserved by `G`.

## Main constructions

* `equifier Φ Ψ`: the `ObjectProperty C` describing the equifier subcategory.
* `Equifier Φ Ψ`: the equifier category.
* `Equifier.ι`: the fully faithful inclusion `Equifier Φ Ψ ⥤ C`.

## References

* [nLab, *equifier*](https://ncatlab.org/nlab/show/equifier).

## Future work

* Describe pointed algebras for a pointed endofunctor as equifiers of inserters.
* Describe algebras for a monad as further equifiers of pointed algebras for a pointed endofunctor.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- The *equifier* of a pair of natural transformations Φ Ψ between parallel functors
`F G : C ⥤ D` as an object property of `C`. It is satisfied by objects `c` such
that `Φ.app c = Ψ.app c`. -/
@[implicit_reducible]
def equifier {F G : C ⥤ D} (Φ Ψ : F ⟶ G) : ObjectProperty C := fun c ↦
  Φ.app c = Ψ.app c

/-- The *equifier* of a pair of natural transformations Φ Ψ between parallel functors
`F G : C ⥤ D` is the category of objects `c : C` such that `Φ.app c = Ψ.app c`. -/
abbrev Equifier {F G : C ⥤ D} (Φ Ψ : F ⟶ G) : Type _ := (equifier Φ Ψ).FullSubcategory

namespace Equifier

variable {F G : C ⥤ D} (Φ Ψ : F ⟶ G)

/-- The inclusion `Equifier F G ⥤ C` that sends an object to its underlying object of `C`. -/
abbrev ι : Equifier Φ Ψ ⥤ C := (equifier Φ Ψ).ι

variable {Φ Ψ} in
@[grind _=_]
lemma prop (E : Equifier Φ Ψ) : Φ.app E.obj = Ψ.app E.obj := E.property

instance {J : Type*} [Category* J]
    [Limits.PreservesColimitsOfShape J F] :
    (equifier Φ Ψ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map F).isColimit.hom_ext
    intro j
    have e1 := Φ.naturality (p.ι.app j)
    have e2 := Ψ.naturality (p.ι.app j)
    dsimp [equifier] at h e1 e2 ⊢
    simp [Limits.ColimitPresentation.map, e1, e2, h]

instance {J : Type*} [Category* J]
    [Limits.PreservesLimitsOfShape J G] :
    (equifier Φ Ψ).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map G).isLimit.hom_ext
    intro j
    have e1 := Φ.naturality (p.π.app j)
    have e2 := Ψ.naturality (p.π.app j)
    dsimp [equifier] at h e1 e2 ⊢
    simp [Limits.LimitPresentation.map, ← e1, e2, h]

end Equifier

end CategoryTheory

