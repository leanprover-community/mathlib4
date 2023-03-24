/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw

! This file was ported from Lean 3 source module category_theory.triangulated.pretriangulated
! leanprover-community/mathlib commit 19786714ebe478f40b503acb4705fb058ba47303
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Shift
import Mathbin.CategoryTheory.Triangulated.Rotate

/-!
# Pretriangulated Categories

This file contains the definition of pretriangulated categories and triangulated functors
between them.

## Implementation Notes

We work under the assumption that pretriangulated categories are preadditive categories,
but not necessarily additive categories, as is assumed in some sources.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

open Category Pretriangulated

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

variable (D : Type u₂) [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`distinguishedTriangles] [] -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T₂ «expr ≅ » T₁) -/
/-- A preadditive category `C` with an additive shift, and a class of "distinguished triangles"
relative to that shift is called pretriangulated if the following hold:
* Any triangle that is isomorphic to a distinguished triangle is also distinguished.
* Any triangle of the form `(X,X,0,id,0,0)` is distinguished.
* For any morphism `f : X ⟶ Y` there exists a distinguished triangle of the form `(X,Y,Z,f,g,h)`.
* The triangle `(X,Y,Z,f,g,h)` is distinguished if and only if `(Y,Z,X⟦1⟧,g,h,-f⟦1⟧)` is.
* Given a diagram:
  ```
        f       g       h
    X  ───> Y  ───> Z  ───> X⟦1⟧
    │       │                │
    │a      │b               │a⟦1⟧'
    V       V                V
    X' ───> Y' ───> Z' ───> X'⟦1⟧
        f'      g'      h'
  ```
  where the left square commutes, and whose rows are distinguished triangles,
  there exists a morphism `c : Z ⟶ Z'` such that `(a,b,c)` is a triangle morphism.

See <https://stacks.math.columbia.edu/tag/0145>
-/
class Pretriangulated where
  distinguishedTriangles : Set (Triangle C)
  isomorphic_distinguished :
    ∀ T₁ ∈ distinguished_triangles, ∀ (T₂) (_ : T₂ ≅ T₁), T₂ ∈ distinguished_triangles
  contractible_distinguished : ∀ X : C, contractibleTriangle X ∈ distinguished_triangles
  distinguished_cocone_triangle :
    ∀ (X Y : C) (f : X ⟶ Y),
      ∃ (Z : C)(g : Y ⟶ Z)(h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distinguished_triangles
  rotate_distinguished_triangle :
    ∀ T : Triangle C, T ∈ distinguished_triangles ↔ T.rotate ∈ distinguished_triangles
  complete_distinguished_triangle_morphism :
    ∀ (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distinguished_triangles) (h₂ : T₂ ∈ distinguished_triangles)
      (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃
#align category_theory.pretriangulated CategoryTheory.Pretriangulated

namespace Pretriangulated

variable [hC : Pretriangulated C]

include hC

-- mathport name: «exprdist_triang »
notation:20 "dist_triang " C => distinguishedTriangles C

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T «expr ∈ » «exprdist_triang »(C)) -/
/-- Given any distinguished triangle `T`, then we know `T.rotate` is also distinguished.
-/
theorem rot_of_dist_triangle (T) (_ : T ∈ (dist_triang C)) : T.rotate ∈ (dist_triang C) :=
  (rotate_distinguished_triangle T).mp H
#align category_theory.pretriangulated.rot_of_dist_triangle CategoryTheory.Pretriangulated.rot_of_dist_triangle

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T «expr ∈ » «exprdist_triang »(C)) -/
/-- Given any distinguished triangle `T`, then we know `T.inv_rotate` is also distinguished.
-/
theorem inv_rot_of_dist_triangle (T) (_ : T ∈ (dist_triang C)) : T.invRotate ∈ (dist_triang C) :=
  (rotate_distinguished_triangle T.invRotate).mpr
    (isomorphic_distinguished T H T.invRotate.rotate (invRotCompRot.app T))
#align category_theory.pretriangulated.inv_rot_of_dist_triangle CategoryTheory.Pretriangulated.inv_rot_of_dist_triangle

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T «expr ∈ » «exprdist_triang »(C)) -/
/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
theorem comp_dist_triangle_mor_zero₁₂ (T) (_ : T ∈ (dist_triang C)) : T.mor₁ ≫ T.mor₂ = 0 :=
  by
  obtain ⟨c, hc⟩ :=
    complete_distinguished_triangle_morphism _ _ (contractible_distinguished T.obj₁) H (𝟙 T.obj₁)
      T.mor₁ rfl
  simpa only [contractible_triangle_mor₂, zero_comp] using hc.left.symm
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₁₂ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₁₂

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T «expr ∈ » «exprdist_triang »(C)) -/
/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
theorem comp_dist_triangle_mor_zero₂₃ (T) (_ : T ∈ (dist_triang C)) : T.mor₂ ≫ T.mor₃ = 0 :=
  comp_dist_triangle_mor_zero₁₂ C T.rotate (rot_of_dist_triangle C T H)
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₂₃ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₂₃

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (T «expr ∈ » «exprdist_triang »(C)) -/
/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `h ≫ f⟦1⟧ = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
theorem comp_dist_triangle_mor_zero₃₁ (T) (_ : T ∈ (dist_triang C)) :
    T.mor₃ ≫ (shiftEquiv C 1).Functor.map T.mor₁ = 0 :=
  by
  have H₂ := rot_of_dist_triangle C T.rotate (rot_of_dist_triangle C T H)
  simpa using comp_dist_triangle_mor_zero₁₂ C T.rotate.rotate H₂
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₃₁ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₃₁

/-
TODO: If `C` is pretriangulated with respect to a shift,
then `Cᵒᵖ` is pretriangulated with respect to the inverse shift.
-/
omit hC

/--
The underlying structure of a triangulated functor between pretriangulated categories `C` and `D`
is a functor `F : C ⥤ D` together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧`.
-/
structure TriangulatedFunctorStruct extends C ⥤ D where
  commShift : shiftFunctor C (1 : ℤ) ⋙ to_functor ≅ to_functor ⋙ shiftFunctor D (1 : ℤ)
#align category_theory.pretriangulated.triangulated_functor_struct CategoryTheory.Pretriangulated.TriangulatedFunctorStruct

namespace TriangulatedFunctorStruct

/-- The identity `triangulated_functor_struct`. -/
def id : TriangulatedFunctorStruct C C where
  obj X := X
  map _ _ f := f
  commShift := by rfl
#align category_theory.pretriangulated.triangulated_functor_struct.id CategoryTheory.Pretriangulated.TriangulatedFunctorStruct.id

instance : Inhabited (TriangulatedFunctorStruct C C) :=
  ⟨id C⟩

variable {C D}

/-- Given a `triangulated_functor_struct` we can define a functor from triangles of `C` to
triangles of `D`.
-/
@[simps]
def mapTriangle (F : TriangulatedFunctorStruct C D) : Triangle C ⥤ Triangle D
    where
  obj T := Triangle.mk (F.map T.mor₁) (F.map T.mor₂) (F.map T.mor₃ ≫ F.commShift.Hom.app T.obj₁)
  map S T f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁' := by
        dsimp
        simp only [← F.to_functor.map_comp, f.comm₁]
      comm₂' := by
        dsimp
        simp only [← F.to_functor.map_comp, f.comm₂]
      comm₃' := by
        dsimp
        erw [category.assoc, ← F.comm_shift.hom.naturality]
        simp only [functor.comp_map, ← F.to_functor.map_comp_assoc, f.comm₃] }
#align category_theory.pretriangulated.triangulated_functor_struct.map_triangle CategoryTheory.Pretriangulated.TriangulatedFunctorStruct.mapTriangle

end TriangulatedFunctorStruct

include hC

variable (C D) [Pretriangulated D]

/-- A triangulated functor between pretriangulated categories `C` and `D` is a functor `F : C ⥤ D`
together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧` such that for every
distinguished triangle `(X,Y,Z,f,g,h)` of `C`, the triangle
`(F(X), F(Y), F(Z), F(f), F(g), F(h) ≫ (ξ X))` is a distinguished triangle of `D`.
See <https://stacks.math.columbia.edu/tag/014V>
-/
structure TriangulatedFunctor extends TriangulatedFunctorStruct C D where
  map_distinguished' :
    ∀ T : Triangle C,
      T ∈ (dist_triang C) → to_triangulated_functor_struct.mapTriangle.obj T ∈ (dist_triang D)
#align category_theory.pretriangulated.triangulated_functor CategoryTheory.Pretriangulated.TriangulatedFunctor

instance : Inhabited (TriangulatedFunctor C C) :=
  ⟨{  obj := fun X => X
      map := fun _ _ f => f
      commShift := by rfl
      map_distinguished' := by
        rintro ⟨_, _, _, _⟩ Tdt
        dsimp at *
        rwa [category.comp_id] }⟩

variable {C D}

/--
Given a `triangulated_functor` we can define a functor from triangles of `C` to triangles of `D`.
-/
@[simps]
def TriangulatedFunctor.mapTriangle (F : TriangulatedFunctor C D) : Triangle C ⥤ Triangle D :=
  F.toTriangulatedFunctorStruct.mapTriangle
#align category_theory.pretriangulated.triangulated_functor.map_triangle CategoryTheory.Pretriangulated.TriangulatedFunctor.mapTriangle

/-- Given a `triangulated_functor` and a distinguished triangle `T` of `C`, then the triangle it
maps onto in `D` is also distinguished.
-/
theorem TriangulatedFunctor.map_distinguished (F : TriangulatedFunctor C D) (T : Triangle C)
    (h : T ∈ (dist_triang C)) : F.mapTriangle.obj T ∈ (dist_triang D) :=
  F.map_distinguished' T h
#align category_theory.pretriangulated.triangulated_functor.map_distinguished CategoryTheory.Pretriangulated.TriangulatedFunctor.map_distinguished

end Pretriangulated

end CategoryTheory

