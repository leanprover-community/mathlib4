/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms

/-! # Triangulated subcategories

In this file, we introduce the notion of triangulated subcategory of
a pretriangulated category.

## TODO

* define the class of morphisms whose "cone" belong to a subcategory
* obtain (pre)triangulated instances on the corresponding localized categories

## Implementation notes

In the definition of `Triangulated.Subcategory`, we do not assume that the predicate
on objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
Part of the theory would be more convenient under this stronger assumption
(e.g. `Subcategory C` would be a lattice), but some applications require this:
for example, the subcategory of bounded below complexes in the homotopy category
of an additive category is not closed under isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Triangulated

open Pretriangulated

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangulated subcategory of a pretriangulated category `C` consists of
a predicate `P : C → Prop` which contains a zero object, is stable by shifts, and such that
if `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle such that if `X₁` and `X₃` satisfy
`P` then `X₂` is isomorphic to an object satisfying `P`. -/
structure Subcategory where
  /-- the underlying predicate on objects of a triangulated subcategory -/
  P : C → Prop
  zero' : ∃ (Z : C) (_ : IsZero Z), P Z
  shift (X : C) (n : ℤ) : P X → P (X⟦n⟧)
  ext₂' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₁ → P T.obj₃ → isoClosure P T.obj₂

namespace Subcategory

variable {C}
variable (S : Subcategory C)

/-- The closure of a triangulated subcategory  -/
def isoClosure : Subcategory C where
  P := CategoryTheory.isoClosure S.P
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z, hZ, Z, hZ', ⟨Iso.refl _⟩⟩
  shift X n := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦n⟧, S.shift Y n hY, ⟨(shiftFunctor C n).mapIso e⟩⟩
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact le_isoClosure _ _
      (S.ext₂' (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by aesop_cat) (by aesop_cat) (by
          dsimp
          simp only [assoc, Iso.cancel_iso_inv_left, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

instance : ClosedUnderIsomorphisms S.isoClosure.P := by
  dsimp only [isoClosure]
  infer_instance

section

variable (P : C → Prop) (zero : P 0)
  (shift : ∀ (X : C) (n : ℤ), P X → P (X⟦n⟧))
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), P T.obj₁ → P T.obj₃ → P T.obj₂)

/-- An alternative constructor for "strictly full" triangulated subcategory. -/
def mk' : Subcategory C where
  P := P
  zero' := ⟨0, isZero_zero _, zero⟩
  shift := shift
  ext₂' T hT h₁ h₃ := le_isoClosure P _ (ext₂ T hT h₁ h₃)

instance : ClosedUnderIsomorphisms (mk' P zero shift ext₂).P where
  of_iso {X Y} e hX := by
    refine ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) ?_ hX zero
    refine isomorphic_distinguished _ (contractible_distinguished X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)

end

lemma ext₂ [ClosedUnderIsomorphisms S.P]
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : S.P T.obj₁)
    (h₃ : S.P T.obj₃) : S.P T.obj₂ := by
  simpa only [isoClosure_eq_self] using S.ext₂' T hT h₁ h₃

end Subcategory

end Triangulated

end CategoryTheory
