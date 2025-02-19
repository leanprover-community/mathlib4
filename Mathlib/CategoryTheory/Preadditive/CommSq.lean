/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# The short complex associated to a commutative square

To a commutative square in a preadditive category; we
associate a short complex `W ⟶ Y ⊞ X ⟶ Z`.

-/

universe v u

namespace CategoryTheory.CommSq

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] {W X Y Z : C}
  {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
  [HasBinaryBiproduct Y X]
  (h : CommSq t l r b)

/-- Given a commutative square
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
This is the short complex `W ⟶ Y ⊞ X ⟶ Z` where
the left map is a difference and the right map a sum. -/
@[simps]
noncomputable def shortComplex : ShortComplex C where
  f := biprod.lift l (-t)
  g := biprod.desc b r
  zero := by simp [h.w]

end CategoryTheory.CommSq
