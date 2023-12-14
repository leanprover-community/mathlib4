/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Triangulated functors

In this file, when `C` and `D` are categories equipped with a shift by `ℤ` and
`F : C ⥤ D` is a functor which commutes with the shift, we define the induced
functor `F.mapTriangle : Triangle C ⥤ Triangle D` on the categories of
triangles. When `C` and `D` are pretriangulated, a triangulated functor
is such a functor `F` which also sends distinguished triangles to
distinguished triangles: this defines the typeclass `Functor.IsTriangulated`.

-/

namespace CategoryTheory

open Category Limits Pretriangulated

namespace Functor

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

/-- The functor `Triangle C ⥤ Triangle D` that is induced by a functor `F : C ⥤ D`
which commutes with shift by `ℤ`. -/
@[simps]
def mapTriangle : Triangle C ⥤ Triangle D where
  obj T := Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [Functor.comp]
        simp only [Category.assoc, ← NatTrans.naturality,
          ← F.map_comp_assoc, f.comm₃] }

instance [Faithful F] : Faithful F.mapTriangle where
  map_injective {X Y} f g h := by
    ext <;> apply F.map_injective
    · exact congr_arg TriangleMorphism.hom₁ h
    · exact congr_arg TriangleMorphism.hom₂ h
    · exact congr_arg TriangleMorphism.hom₃ h

instance [Full F] [Faithful F] : Full F.mapTriangle where
  preimage {X Y} f :=
    { hom₁ := F.preimage f.hom₁
      hom₂ := F.preimage f.hom₂
      hom₃ := F.preimage f.hom₃
      comm₁ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, image_preimage] using f.comm₁)
      comm₂ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, image_preimage] using f.comm₂)
      comm₃ := F.map_injective (by
        rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app Y.obj₁)]
        simpa only [mapTriangle_obj, map_comp, assoc, commShiftIso_hom_naturality,
          image_preimage, Triangle.mk_mor₃] using f.comm₃) }

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A functor which commutes with the shift by `ℤ` is triangulated if
it sends distinguished triangles to distinguished triangles. -/
class IsTriangulated : Prop where
  map_distinguished (T : Triangle C) : (T ∈ distTriang C) → F.mapTriangle.obj T ∈ distTriang D

lemma map_distinguished [F.IsTriangulated] (T : Triangle C) (hT : T ∈ distTriang C) :
    F.mapTriangle.obj T ∈ distTriang D :=
  IsTriangulated.map_distinguished _ hT

end Functor

end CategoryTheory
