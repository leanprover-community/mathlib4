/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.RespectsIso

/-! # Triangulated subcategories

In this file, we introduce the notion of triangulated subcategory of
a pretriangulated category.

## TODO

* define the class of morphisms whose "cone" belong to a subcategory
* obtain (pre)triangulated instances on the corresponding localized categories

## Implementation notes

In the definition of `Triangulated.Subcategory`, we do not assume that the set of
objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
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
`set : Set C` which contains a zero object, is stable by shifts, and such that
if `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle such that if `X₁` and `X₃` are
in `set`, then `X₂` is isomorphic to an object in `set`. -/
structure Subcategory where
  /-- the underlying set of objects of a triangulated subcategory -/
  set : Set C
  zero' : ∃ (Z : C) (_ : IsZero Z), Z ∈ set
  shift (X : C) (n : ℤ) (_ : X ∈ set) : X⟦n⟧ ∈ set
  ext₂' (T : Triangle C) (_ : T ∈ distTriang C) :
    T.obj₁ ∈ set → T.obj₃ ∈ set → T.obj₂ ∈ set.isoClosure

namespace Subcategory

variable {C}
variable (S : Subcategory C)

/-- The closure of a triangulated subcategory  -/
def isoClosure : Subcategory C where
  set := S.set.isoClosure
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z, hZ, Z, hZ', ⟨Iso.refl _⟩⟩
  shift X n := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦n⟧, S.shift Y n hY, ⟨(shiftFunctor C n).mapIso e⟩⟩
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact Set.subset_isoClosure _
      (S.ext₂' (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by aesop_cat) (by aesop_cat) (by
          dsimp
          simp only [assoc, Iso.cancel_iso_inv_left, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

instance : S.isoClosure.set.RespectsIso := by
  dsimp only [isoClosure]
  infer_instance

section

variable (set : Set C) (zero : 0 ∈ set)
  (shift : ∀ (X : C) (n : ℤ) (_ : X ∈ set), X⟦n⟧ ∈ set)
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), T.obj₁ ∈ set → T.obj₃ ∈ set → T.obj₂ ∈ set)

/-- An alternative constructor for "strictly full" triangulated subcategory. -/
def mk' : Subcategory C where
  set := set
  zero' := ⟨0, isZero_zero _, zero⟩
  shift := shift
  ext₂' T hT h₁ h₃ := set.subset_isoClosure (ext₂ T hT h₁ h₃)

instance : (mk' set zero shift ext₂).set.RespectsIso where
  condition {X Y} e hX := by
    refine' ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) _ hX zero
    refine' isomorphic_distinguished _ (contractible_distinguished X) _ _
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)

end

lemma ext₂ [S.set.RespectsIso]
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ S.set)
    (h₃ : T.obj₃ ∈ S.set) : T.obj₂ ∈ S.set := by
  simpa only [S.set.isoClosure_eq_self] using S.ext₂' T hT h₁ h₃

end Subcategory

end Triangulated

end CategoryTheory
