/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.NegOnePow
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Twist
public import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Commutation with shifts of functors in two variables

We introduce a typeclass `Functor.CommShift₂Int` for a bifunctor `G : C₁ ⥤ C₂ ⥤ D`
(with `D` a preadditive category) as the two variable analogue of `Functor.CommShift`.
We require that `G` commutes with the shifts in both variables and that the two
ways to identify `(G.obj (X₁⟦p⟧)).obj (X₂⟦q⟧)` to `((G.obj X₁).obj X₂)⟦p + q⟧`
differ by the sign `(-1) ^ (p + q)`.

This is implemented using a structure `Functor.CommShift₂` which does not depend
on the preadditive structure on `D`: instead of signs, elements in `(CatCenter D)ˣ`
are used. These elements are part of a `CommShift₂Setup` structure which extends
a `TwistShiftData` structure (see the file `CategoryTheory.Shift.Twist`).

## TODO (@joelriou)
* Show that `G : C₁ ⥤ C₂ ⥤ D` satisfies `Functor.CommShift₂Int` iff the uncurried
functor `C₁ × C₂ ⥤ D` commutes with the shift by `ℤ × ℤ`, where `C₁ × C₂` is
equipped with the obvious product shift, and `D` is equipped with
the twisted shift.

-/

@[expose] public section

namespace CategoryTheory

variable {C C₁ C₂ D : Type*} [Category C] [Category C₁] [Category C₂] [Category D]

variable (D) in
/-- Given a category `D` equipped with a shift by an additive monoid `M`, this
structure `CommShift₂Setup D M` allows to define what it means for a bifunctor
`C₁ ⥤ C₂ ⥤ D` to commute with shifts by `M` with respect to both variables.
This structure consists of a `TwistShiftData` for the shift by `M × M` on `D`
obtained by pulling back the addition map `M × M →+ M`, with two axioms `z_zero₁`
and `z_zero₂`. We also require an additional data of `ε m n : (CatCenter D)ˣ`
for `m` and `n`: even though this is determined by the `z` field of `TwistShiftData`,
we make it a separate field so as to have control on its definitional properties. -/
structure CommShift₂Setup (M : Type*) [AddCommMonoid M] [HasShift D M] extends
    TwistShiftData (PullbackShift D (AddMonoidHom.fst M M + AddMonoidHom.snd _ _)) (M × M) where
  z_zero₁ (m₁ m₂ : M) : z (0, m₁) (0, m₂) = 1 := by aesop
  z_zero₂ (m₁ m₂ : M) : z (m₁, 0) (m₂, 0) = 1 := by aesop
  /-- The invertible elements in the center of `D` that are equal
  to `(z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n)`. -/
  ε (m n : M) : (CatCenter D)ˣ
  hε (m n : M) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n) := by aesop

/-- The standard setup for the commutation of bifunctors with shifts by `ℤ`. -/
@[simps]
noncomputable def CommShift₂Setup.int [Preadditive D] [HasShift D ℤ]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] :
    CommShift₂Setup D ℤ where
  z m n := (-1) ^ (m.1 * n.2)
  assoc _ _ _ := by
    dsimp
    rw [← zpow_add, ← zpow_add]
    cutsat
  commShift _ _ := ⟨by cat_disch⟩
  ε p q := (-1) ^ (p * q)

namespace Functor

/-- A bifunctor `G : C₁ ⥤ C₂ ⥤ D` commutes with the shifts by `M` if all functors
`G.obj X₁` and `G.flip X₂` are equipped with `Functor.CommShift` structures, in a way
that is natural in `X₁` and `X₂`, and that these isomorphisms commute up to
the multiplication with an element in `(CatCenter D)ˣ` which is determined by
a `CommShift₂Setup D M` structure. (In most cases, one should use the
abbreviation `CommShift₂Int`.) -/
class CommShift₂ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) where
  commShiftObj (X₁ : C₁) : (G.obj X₁).CommShift M := by infer_instance
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (G.map f) M := by infer_instance
  commShiftFlipObj (X₂ : C₂) : (G.flip.obj X₂).CommShift M := by infer_instance
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) : NatTrans.CommShift (G.flip.map g) M := by
    infer_instance
  comm (G h) (X₁ : C₁) (X₂ : C₂) (m n : M) :
    ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
      (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' =
        ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫
          (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫
            (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

/-- A bifunctor `G : C₁ ⥤ C₂ ⥤ D` commutes with the shifts by `ℤ` if all functors
`G.obj X₁` and `G.flip X₂` are equipped with `Functor.CommShift` structures, in a way
that is natural in `X₁` and `X₂`, and that these isomorphisms for the shift by `p`
on the first variable and the shift by `q` on the second variable commute up
to the sign `(-1) ^ (p * q)`. -/
abbrev CommShift₂Int [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (G : C₁ ⥤ C₂ ⥤ D) : Type _ :=
  G.CommShift₂ .int

namespace CommShift₂

attribute [instance] commShiftObj commShiftFlipObj commShift_map commShift_flip_map

attribute [reassoc] comm

end CommShift₂

end Functor

end CategoryTheory
