/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.ComposableArrows
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

open Category Limits Pretriangulated Preadditive

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
  map_surjective {X Y} f :=
   ⟨{ hom₁ := F.preimage f.hom₁
      hom₂ := F.preimage f.hom₂
      hom₃ := F.preimage f.hom₃
      comm₁ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using f.comm₁)
      comm₂ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using f.comm₂)
      comm₃ := F.map_injective (by
        rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app Y.obj₁)]
        simpa only [mapTriangle_obj, map_comp, assoc, commShiftIso_hom_naturality,
          map_preimage, Triangle.mk_mor₃] using f.comm₃) }, by aesop_cat⟩

section Additive

variable [Preadditive C] [Preadditive D] [F.Additive]

/-- The functor `F.mapTriangle` commutes with the shift. -/
@[simps!]
noncomputable def mapTriangleCommShiftIso (n : ℤ) :
    Triangle.shiftFunctor C n ⋙ F.mapTriangle ≅ F.mapTriangle ⋙ Triangle.shiftFunctor D n :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _
    ((F.commShiftIso n).app _) ((F.commShiftIso n).app _) ((F.commShiftIso n).app _)
    (by aesop_cat) (by aesop_cat) (by
      dsimp
      simp only [map_units_smul, map_comp, Linear.units_smul_comp, assoc,
        Linear.comp_units_smul, ← F.commShiftIso_hom_naturality_assoc]
      rw [F.map_shiftFunctorComm_hom_app T.obj₁ 1 n]
      simp only [comp_obj, assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, map_id, comp_id])) (by aesop_cat)

attribute [local simp] commShiftIso_zero commShiftIso_add
  shiftFunctorAdd'_eq_shiftFunctorAdd

set_option maxHeartbeats 400000 in
noncomputable instance [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] : (F.mapTriangle).CommShift ℤ where
  iso := F.mapTriangleCommShiftIso

/-- `F.mapTriangle` commutes with the rotation of triangles. -/
@[simps!]
def mapTriangleRotateIso :
    F.mapTriangle ⋙ Pretriangulated.rotate D ≅
      Pretriangulated.rotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((F.commShiftIso (1 : ℤ)).symm.app _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

/-- `F.mapTriangle` commutes with the inverse of the rotation of triangles. -/
@[simps!]
noncomputable def mapTriangleInvRotateIso [F.Additive] :
    F.mapTriangle ⋙ Pretriangulated.invRotate D ≅
      Pretriangulated.invRotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : ℤ)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

end Additive

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

namespace IsTriangulated

open ZeroObject

variable [F.IsTriangulated]

instance (priority := 100) : PreservesZeroMorphisms F where
  map_zero X Y := by
    have h₁ : (0 : X ⟶ Y) = 0 ≫ 𝟙 0 ≫ 0 := by simp
    have h₂ : 𝟙 (F.obj 0) = 0 := by
      rw [← IsZero.iff_id_eq_zero]
      apply Triangle.isZero₃_of_isIso₁ _
        (F.map_distinguished _ (contractible_distinguished (0 : C)))
      dsimp
      infer_instance
    rw [h₁, F.map_comp, F.map_comp, F.map_id, h₂, zero_comp, comp_zero]

end IsTriangulated

end Functor

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Triangulated

namespace Octahedron

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} {comm : u₁₂ ≫ u₂₃ = u₁₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The image of an octahedron by a triangulated functor. -/
@[simps]
def map : Octahedron (by dsimp; rw [← F.map_comp, comm])
    (F.map_distinguished _ h₁₂) (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃) where
  m₁ := F.map h.m₁
  m₃ := F.map h.m₃
  comm₁ := by simpa using F.congr_map h.comm₁
  comm₂ := by simpa using F.congr_map h.comm₂ =≫ (F.commShiftIso 1).hom.app X₁
  comm₃ := by simpa using F.congr_map h.comm₃
  comm₄ := by simpa using F.congr_map h.comm₄ =≫ (F.commShiftIso 1).hom.app X₂
  mem := isomorphic_distinguished _ (F.map_distinguished _ h.mem) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

end Octahedron

end Triangulated

open Triangulated

/-- If `F : C ⥤ D` is a triangulated functor from a triangulated category, then `D`
is also triangulated if tuples of composables arrows in `D` can be lifted to `C`. -/
lemma isTriangulated_of_essSurj_mapComposableArrows_two
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [(F.mapComposableArrows 2).EssSurj] [IsTriangulated C] :
    IsTriangulated D := by
  apply IsTriangulated.mk
  intro Y₁ Y₂ Y₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨α, ⟨e⟩⟩ : ∃ (α : ComposableArrows C 2),
      Nonempty ((F.mapComposableArrows 2).obj α ≅ ComposableArrows.mk₂ u₁₂ u₂₃) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨X₁, X₂, X₃, f, g, rfl⟩ := ComposableArrows.mk₂_surjective α
  obtain ⟨_, _, _, h₁₂'⟩ := distinguished_cocone_triangle f
  obtain ⟨_, _, _, h₂₃'⟩ := distinguished_cocone_triangle g
  obtain ⟨_, _, _, h₁₃'⟩ := distinguished_cocone_triangle (f ≫ g)
  exact ⟨Octahedron.ofIso (e₁ := (e.app 0).symm) (e₂ := (e.app 1).symm) (e₃ := (e.app 2).symm)
    (comm₁₂ := ComposableArrows.naturality' e.inv 0 1)
    (comm₂₃ := ComposableArrows.naturality' e.inv 1 2)
    (H := (someOctahedron rfl h₁₂' h₂₃' h₁₃').map F) _ _ _ _ _⟩

end CategoryTheory
