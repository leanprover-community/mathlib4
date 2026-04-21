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
a `TwistShiftData` structure (see the file `Mathlib.CategoryTheory.Shift.Twist`).

## TODO (@joelriou)
* Show that `G : C₁ ⥤ C₂ ⥤ D` satisfies `Functor.CommShift₂Int` iff the uncurried
  functor `C₁ × C₂ ⥤ D` commutes with the shift by `ℤ × ℤ`, where `C₁ × C₂` is
  equipped with the obvious product shift, and `D` is equipped with
  the twisted shift.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

variable {C₁ C₁' C₂ C₂' D : Type*} [Category* C₁] [Category* C₁']
  [Category* C₂] [Category* C₂'] [Category* D]

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
    lia
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

/-- This alias for `Functor.CommShift₂.comm` allows to use the dot notation. -/
alias commShift₂_comm := CommShift₂.comm

attribute [reassoc] commShift₂_comm

/-- A bifunctor `G : C₁ ⥤ C₂ ⥤ D` commutes with the shifts by `ℤ` if all functors
`G.obj X₁` and `G.flip X₂` are equipped with `Functor.CommShift` structures, in a way
that is natural in `X₁` and `X₂`, and that these isomorphisms for the shift by `p`
on the first variable and the shift by `q` on the second variable commute up
to the sign `(-1) ^ (p * q)`. -/
abbrev CommShift₂Int [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (G : C₁ ⥤ C₂ ⥤ D) : Type _ :=
  G.CommShift₂ .int

namespace CommShift₂

attribute [instance_reducible] commShiftObj commShiftFlipObj
attribute [instance] commShiftObj commShiftFlipObj commShift_map commShift_flip_map

set_option backward.inferInstanceAs.wrap.data false in
set_option backward.isDefEq.respectTransparency false in
instance precomp₁ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₁' M]
    [HasShift C₂ M] [HasShift D M] (F : C₁' ⥤ C₁) [F.CommShift M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h] :
    (F ⋙ G).CommShift₂ h where
  commShiftObj (X₁' : C₁') := inferInstanceAs ((G.obj (F.obj X₁')).CommShift M)
  commShift_map {X₁' Y₁' : C₁'} (f : X₁' ⟶ Y₁') := by dsimp; infer_instance
  commShiftFlipObj (X₂ : C₂) := inferInstanceAs ((F ⋙ G.flip.obj X₂).CommShift M)
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :=
    inferInstanceAs (NatTrans.CommShift (whiskerLeft F (G.flip.map g)) M)
  comm X₁' X₂ m n := by
    have := G.commShift₂_comm h (F.obj X₁') X₂ m n
    dsimp [commShiftIso] at this ⊢
    simp only [Category.comp_id, Category.id_comp, map_comp, Category.assoc]
    rw [NatTrans.shift_app (G.map ((F.commShiftIso m).hom.app X₁')) n X₂]
    simp [this]

set_option backward.inferInstanceAs.wrap false in
instance precomp₂ {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂' M]
    [HasShift C₂ M] [HasShift D M] (F : C₂' ⥤ C₂) [F.CommShift M]
    (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h] :
    (G ⋙ (whiskeringLeft C₂' C₂ D).obj F).CommShift₂ h where
  commShiftObj (X₁ : C₁) := inferInstanceAs ((F ⋙ G.obj X₁).CommShift M)
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) := by dsimp; infer_instance
  commShiftFlipObj (X₂' : C₂') := inferInstanceAs ((G.flip.obj (F.obj X₂')).CommShift M)
  commShift_flip_map {X₂' Y₂' : C₂'} (g : X₂' ⟶ Y₂') :=
    inferInstanceAs (NatTrans.CommShift (G.flip.map (F.map g)) M)
  comm X₁ X₂' m n := by
    have := G.commShift₂_comm h X₁ (F.obj X₂') m n
    dsimp [commShiftIso] at this ⊢
    simp only [Category.comp_id, Category.id_comp, Category.assoc, map_comp]
    refine ((G.obj _).map _ ≫= this).trans ?_
    simp only [← Category.assoc]; congr 3
    exact (NatTrans.shift_app_comm (G.flip.map ((F.commShiftIso n).hom.app X₂')) m X₁).symm

/- TODO : If `G : C₁ ⥤ C₂ ⥤ D` and `H : D ⥤ D'` and commute with shifts,
and we have compatible "setups" on `D` and `D'`, show that `G ⋙ H` also commutes
with shifts. -/

end CommShift₂

end Functor

namespace NatTrans

section

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G₁ G₂ G₃ : C₁ ⥤ C₂ ⥤ D} (τ : G₁ ⟶ G₂) (τ' : G₂ ⟶ G₃) (h : CommShift₂Setup D M)
  [G₁.CommShift₂ h] [G₂.CommShift₂ h] [G₃.CommShift₂ h]

/-- If `τ : G₁ ⟶ G₂` is a natural transformation between two bifunctors
which commute shifts on both variables, this typeclass asserts a compatibility of `τ`
with these shifts. -/
class CommShift₂ : Prop where
  commShift_app (X₁ : C₁) : NatTrans.CommShift (τ.app X₁) M := by infer_instance
  commShift_flipApp (X₂ : C₂) : NatTrans.CommShift (τ.flipApp X₂) M := by infer_instance

namespace CommShift₂

attribute [instance] commShift_app commShift_flipApp

instance : CommShift₂ (𝟙 G₁) h where
  commShift_app _ := by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_id, id_app]
    infer_instance

instance [CommShift₂ τ h] [CommShift₂ τ' h] : CommShift₂ (τ ≫ τ') h where
  commShift_app _ := by dsimp; infer_instance
  commShift_flipApp _ := by
    simp only [flipApp, flipFunctor_obj, Functor.map_comp, comp_app]
    infer_instance

end CommShift₂

end

/-- If `τ : G₁ ⟶ G₂` is a natural transformation between two bifunctors
which commute shifts on both variables, this typeclass asserts a compatibility of `τ`
with these shifts. -/
abbrev CommShift₂Int [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} [G₁.CommShift₂Int] [G₂.CommShift₂Int] (τ : G₁ ⟶ G₂) : Prop :=
  NatTrans.CommShift₂ τ .int

end NatTrans

end CategoryTheory
