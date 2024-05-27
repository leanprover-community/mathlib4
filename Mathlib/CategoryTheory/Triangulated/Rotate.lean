/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Triangulated.Basic

#align_import category_theory.triangulated.rotate from "leanprover-community/mathlib"@"94d4e70e97c36c896cb70fb42821acfed040de60"

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasShift C ℤ]
variable (X : C)

/-- If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g       h        -f⟦1⟧'
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
```
-/
@[simps!]
def Triangle.rotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')
#align category_theory.pretriangulated.triangle.rotate CategoryTheory.Pretriangulated.Triangle.rotate

section

/-- Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `invRotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shiftEquiv C 1`)
-/
@[simps!]
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : ℤ)).counitIso.inv.app _ )
#align category_theory.pretriangulated.triangle.inv_rotate CategoryTheory.Pretriangulated.Triangle.invRotate

end

attribute [local simp] shift_shift_neg' shift_neg_shift'
  shift_shiftFunctorCompIsoId_add_neg_self_inv_app
  shift_shiftFunctorCompIsoId_add_neg_self_hom_app

variable (C)

/-- Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : Triangle C ⥤ Triangle C where
  obj := Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }
#align category_theory.pretriangulated.rotate CategoryTheory.Pretriangulated.rotate

/-- The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def invRotate : Triangle C ⥤ Triangle C where
  obj := Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [neg_comp, assoc, comp_neg, neg_inj, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp, assoc]
      erw [← NatTrans.naturality]
      rfl
    comm₃ := by
      erw [← reassoc_of% f.comm₂, Category.assoc, ← NatTrans.naturality]
      rfl }
#align category_theory.pretriangulated.inv_rotate CategoryTheory.Pretriangulated.invRotate

variable {C}
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

/-- The unit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : ℤ)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)
#align category_theory.pretriangulated.rot_comp_inv_rot CategoryTheory.Pretriangulated.rotCompInvRot

/-- The counit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C) :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : ℤ)).counitIso.app T.obj₃)
#align category_theory.pretriangulated.inv_rot_comp_rot CategoryTheory.Pretriangulated.invRotCompRot

variable (C)

/-- Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangleRotation : Equivalence (Triangle C) (Triangle C) where
  functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot
#align category_theory.pretriangulated.triangle_rotation CategoryTheory.Pretriangulated.triangleRotation

variable {C}

instance : (rotate C).IsEquivalence := by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance

instance : (invRotate C).IsEquivalence := by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance

end CategoryTheory.Pretriangulated
