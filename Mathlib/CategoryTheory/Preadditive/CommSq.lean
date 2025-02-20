/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# The short complex associated to a commutative square

To a commutative square in a preadditive category; we
associate a short complex `W ⟶ Y ⊞ X ⟶ Z`.

-/

universe v u

namespace CategoryTheory

open Limits Category

variable {C : Type u} [Category.{v} C] [Preadditive C] {W X Y Z : C}
  {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
  [HasBinaryBiproduct Y X]

/-- Given a commutative square in a preadditive category
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
this is the short complex `W ⟶ Y ⊞ X ⟶ Z` where
the left map is a difference and the right map a sum. -/
@[simps]
noncomputable def CommSq.shortComplex (h : CommSq t l r b) : ShortComplex C where
  f := biprod.lift l (-t)
  g := biprod.desc b r
  zero := by simp [h.w]

/-- Given a pushout square in a preadditive category
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
the complex `W ⟶ Y ⊞ X ⟶ Z ⟶ 0` is a cokernel sequence,
where the map `W ⟶ Y ⊞ X` is a difference and `Y ⊞ X ⟶ Z` a sum. -/
noncomputable def IsPushout.isColimitCokernelCofork (h : IsPushout t l r b) :
    IsColimit (CokernelCofork.ofπ _ h.shortComplex.zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb ↦ h.desc (biprod.inr ≫ b) (biprod.inl ≫ b) (by
      dsimp at hb
      simp only [biprod.lift_eq, Preadditive.neg_comp,
        Preadditive.sub_comp, assoc, ← sub_eq_add_neg, sub_eq_zero] at hb
      exact hb.symm))
    (by aesop_cat)
    (fun _ _ _ hm ↦ h.hom_ext (by simpa using biprod.inr ≫= hm)
      (by simpa using biprod.inl ≫= hm))

lemma IsPushout.epi_shortComplex_g (h : IsPushout t l r b) :
    Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

end CategoryTheory
