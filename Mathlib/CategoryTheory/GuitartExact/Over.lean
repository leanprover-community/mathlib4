/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Guitart exact squares involving `Over` categories

Let `F : C ⥤ D` be a functor and `X : C`. One may consider the
commutative square of categories where vertical functors are `Over.forget`:
```
    Over.post F
Over X ⥤ Over (F.obj X)
 |          |
 v          v
 C     ⥤    D
       F
```

We show that this square is Guitart exact if for all `Y : C`, the binary product `X ⨯ Y`
exists and `F` commutes with it.

-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (X : C)

/-- Given `F : C ⥤ D` and `X : C`, this is the `2`-square
```
    Over.post F
Over X ⥤ Over (F.obj X)
 |          |
 v          v
 C     ⥤    D
       F
```
with `Over.forget` as vertical functors. -/
abbrev TwoSquare.overPost :
    TwoSquare (Over.post F) (Over.forget X) (Over.forget (F.obj X)) F :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [∀ (Y : C), HasBinaryProduct X Y] [∀ (Y : C), PreservesLimit (pair X Y) F] :
    (TwoSquare.overPost F X).GuitartExact where
  isConnected_rightwards {W Z} g := by
    let P : (TwoSquare.overPost F X).StructuredArrowRightwards g :=
      TwoSquare.StructuredArrowRightwards.mk _ _ (Over.mk (Y := X ⨯ Z) prod.fst)
        (Over.homMk (prod.lift (show W.left ⟶ F.obj X from W.hom) g ≫ inv (prodComparison F X Z))
            (by simp [inv_prodComparison_map_fst])) prod.snd
            (by simp [inv_prodComparison_map_snd])
    have := Nonempty.intro P
    let φ (Q) : Q ⟶ P := StructuredArrow.homMk (CostructuredArrow.homMk
      (Over.homMk (prod.lift Q.right.left.hom Q.right.hom))) (by
        ext
        dsimp
        rw [← cancel_mono (prodComparison F X _)]
        ext
        · simpa [← Functor.map_comp, P] using Over.w Q.hom.left
        · simpa [← Functor.map_comp, P] using CostructuredArrow.w Q.hom)
    exact zigzag_isConnected (fun Q₁ Q₂ ↦ (Zigzag.of_hom (φ Q₁)).trans (Zigzag.of_inv (φ Q₂)))

end CategoryTheory
