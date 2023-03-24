/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw

! This file was ported from Lean 3 source module category_theory.triangulated.rotate
! leanprover-community/mathlib commit 19786714ebe478f40b503acb4705fb058ba47303
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Triangulated.Basic

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
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shift C`)
-/
@[simps!]
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompShiftFunctorNeg _ _).hom.app _) T.mor₁
    (T.mor₂ ≫ (shiftFunctorNegCompShiftFunctor C _).inv.app _)
#align category_theory.pretriangulated.triangle.inv_rotate CategoryTheory.Pretriangulated.Triangle.invRotate

end

attribute [local simp] shift_shift_neg' shift_neg_shift'
  shiftFunctorCompShiftFunctorNeg_hom_app_shift
  shiftFunctorCompShiftFunctorNeg_inv_app_shift

namespace TriangleMorphism

variable {T₁ T₂ T₃ T₄ : Triangle C}

open Triangle

/-- You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
Given a triangle morphism of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
      f'      g'      h'
```
applying `rotate` gives a triangle morphism of the form:

```
      g        h       -f⟦1⟧
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
  │       │         │         │
  │b      │c        │a⟦1⟧     │b⟦1⟧'
  V       V         V         V
  Y' ───> Z' ───> X'⟦1⟧ ───> Y'⟦1⟧
      g'      h'       -f'⟦1⟧
```
-/
@[simps]
def rotate (f : TriangleMorphism T₁ T₂) : TriangleMorphism T₁.rotate T₂.rotate
    where
  hom₁ := f.hom₂
  hom₂ := f.hom₃
  hom₃ := f.hom₁⟦1⟧'
  comm₃ := by
    dsimp
    simp only [rotate_mor₃, comp_neg, neg_comp, ← Functor.map_comp, f.comm₁]
#align category_theory.pretriangulated.triangle_morphism.rotate CategoryTheory.Pretriangulated.TriangleMorphism.rotate

/-- Given a triangle morphism of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
      f'      g'      h'
```
applying `invRotate` gives a triangle morphism that can be thought of as:
```
        -h⟦-1⟧      f         g
  Z⟦-1⟧  ───>  X   ───>  Y   ───>  Z
    │          │         │         │
    │c⟦-1⟧'    │a        │b        │c
    V          V         V         V
  Z'⟦-1⟧ ───>  X'  ───>  Y'  ───>  Z'
       -h'⟦-1⟧     f'        g'
```
(note that this diagram doesn't technically fit the definition of triangle morphism,
as `Z⟦-1⟧⟦1⟧` is not necessarily equal to `Z`, and `Z'⟦-1⟧⟦1⟧` is not necessarily equal to `Z'`,
but they are isomorphic, by the `counitIso` of `shift C`)
-/
@[simps]
def invRotate (f : TriangleMorphism T₁ T₂) : TriangleMorphism T₁.invRotate T₂.invRotate
    where
  hom₁ := f.hom₃⟦-1⟧'
  hom₂ := f.hom₁
  hom₃ := f.hom₂
  comm₁ := by
    dsimp
    simp only [neg_comp, assoc, comp_neg, neg_inj, ← Functor.map_comp_assoc, ← f.comm₃]
    rw [Functor.map_comp, assoc]
    erw [← NatTrans.naturality ]
    rfl
  comm₃ := by
    erw [← reassoc_of% f.comm₂, Category.assoc,
      ← (shiftFunctorNegCompShiftFunctor C (1 : ℤ)).inv.naturality f.hom₃]
    rfl
#align category_theory.pretriangulated.triangle_morphism.inv_rotate CategoryTheory.Pretriangulated.TriangleMorphism.invRotate

end TriangleMorphism

variable (C)

/-- Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : Triangle C ⥤ Triangle C
    where
  obj := Triangle.rotate
  map f := f.rotate
#align category_theory.pretriangulated.rotate CategoryTheory.Pretriangulated.rotate

/-- The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def invRotate : Triangle C ⥤ Triangle C
    where
  obj := Triangle.invRotate
  map f := f.invRotate
#align category_theory.pretriangulated.inv_rotate CategoryTheory.Pretriangulated.invRotate

variable {C}

variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

/-- There is a natural map from a triangle to the `invRotate` of its `rotate`. -/
@[simps]
def toInvRotateRotate (T : Triangle C) : T ⟶ (invRotate C).obj ((rotate C).obj T)
    where
  hom₁ := (shiftFunctorCompShiftFunctorNeg C (1 : ℤ)).inv.app T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃
#align category_theory.pretriangulated.to_inv_rotate_rotate CategoryTheory.Pretriangulated.toInvRotateRotate

/-- There is a natural transformation between the identity functor on triangles in `C`,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rotCompInvRotHom : 𝟭 (Triangle C) ⟶ rotate C ⋙ invRotate C
    where
  app := toInvRotateRotate
#align category_theory.pretriangulated.rot_comp_inv_rot_hom CategoryTheory.Pretriangulated.rotCompInvRotHom

/-- There is a natural map from the `invRotate` of the `rotate` of a triangle to itself. -/
@[simps]
def fromInvRotateRotate (T : Triangle C) : (invRotate C).obj ((rotate C).obj T) ⟶ T
    where
  hom₁ := (shiftFunctorCompShiftFunctorNeg C (1 : ℤ)).hom.app T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃
#align category_theory.pretriangulated.from_inv_rotate_rotate CategoryTheory.Pretriangulated.fromInvRotateRotate

/-- There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor.
-/
@[simps!]
def rotCompInvRotInv : rotate C ⋙ invRotate C ⟶ 𝟭 (Triangle C) where
  app := fromInvRotateRotate
#align category_theory.pretriangulated.rot_comp_inv_rot_inv CategoryTheory.Pretriangulated.rotCompInvRotInv

/-- The natural transformations between the identity functor on triangles in `C` and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C
    where
  hom := rotCompInvRotHom
  inv := rotCompInvRotInv
#align category_theory.pretriangulated.rot_comp_inv_rot CategoryTheory.Pretriangulated.rotCompInvRot

/-- There is a natural map from the `rotate` of the `inv_rotate` of a triangle to itself. -/
@[simps]
def fromRotateInvRotate (T : Triangle C) : (rotate C).obj ((invRotate C).obj T) ⟶ T
    where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := (shiftFunctorNegCompShiftFunctor C (1 : ℤ)).hom.app T.obj₃
#align category_theory.pretriangulated.from_rotate_inv_rotate CategoryTheory.Pretriangulated.fromRotateInvRotate

/-- There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles in `C`, and the identity functor.
-/
@[simps]
def invRotCompRotHom : invRotate C ⋙ rotate C ⟶ 𝟭 (Triangle C) where app := fromRotateInvRotate
#align category_theory.pretriangulated.inv_rot_comp_rot_hom CategoryTheory.Pretriangulated.invRotCompRotHom

/-- There is a natural map from a triangle to the `rotate` of its `inv_rotate`. -/
@[simps]
def toRotateInvRotate (T : Triangle C) : T ⟶ (rotate C).obj ((invRotate C).obj T)
    where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := (shiftFunctorNegCompShiftFunctor C (1 : ℤ)).inv.app T.obj₃
#align category_theory.pretriangulated.to_rotate_inv_rotate CategoryTheory.Pretriangulated.toRotateInvRotate

/-- There is a natural transformation between the identity functor on triangles in `C`,
and the composition of an inverse rotation with a rotation.
-/
@[simps]
def invRotCompRotInv : 𝟭 (Triangle C) ⟶ invRotate C ⋙ rotate C
    where
  app := toRotateInvRotate
#align category_theory.pretriangulated.inv_rot_comp_rot_inv CategoryTheory.Pretriangulated.invRotCompRotInv

/-- The natural transformations between the composition of a rotation with an inverse rotation
on triangles in `C`, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C)
    where
  hom := invRotCompRotHom
  inv := invRotCompRotInv
#align category_theory.pretriangulated.inv_rot_comp_rot CategoryTheory.Pretriangulated.invRotCompRot

variable (C)

/-- Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangleRotation : Equivalence (Triangle C) (Triangle C)
    where
  functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot
#align category_theory.pretriangulated.triangle_rotation CategoryTheory.Pretriangulated.triangleRotation

variable {C}

instance : IsEquivalence (rotate C) := by
  change IsEquivalence (triangleRotation C).functor
  infer_instance

instance : IsEquivalence (invRotate C) := by
  change IsEquivalence (triangleRotation C).inverse
  infer_instance

end CategoryTheory.Pretriangulated
