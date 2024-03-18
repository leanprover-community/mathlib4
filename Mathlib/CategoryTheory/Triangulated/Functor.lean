/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Linear.LinearFunctor

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

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]

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

attribute [local simp] map_zsmul comp_zsmul zsmul_comp
  commShiftIso_zero commShiftIso_add
  shiftFunctorAdd'_eq_shiftFunctorAdd
  commShiftIso_comp_hom_app

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

@[simps!]
noncomputable def mapTriangleInvRotateIso [F.Additive] :
    F.mapTriangle ⋙ Pretriangulated.invRotate D ≅
      Pretriangulated.invRotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : ℤ)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)) (by aesop_cat)

@[simps!]
def mapTriangleCompIso : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

end Additive

variable [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]

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

noncomputable def mapZeroObject : F.obj 0 ≅ 0 := by
  apply IsZero.isoZero
  apply Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ (contractible_distinguished (0 : C)))
  dsimp
  infer_instance

instance : PreservesZeroMorphisms F := by
  have h : 𝟙 (F.obj 0) = 0 := by
    rw [← IsZero.iff_id_eq_zero]
    apply Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ (contractible_distinguished (0 : C)))
    dsimp
    infer_instance
  refine' ⟨fun X Y => _⟩
  have : (0 : X ⟶ Y) = 0 ≫ 𝟙 0 ≫ 0 := by simp
  rw [this, F.map_comp, F.map_comp, F.map_id, h, zero_comp, comp_zero]

noncomputable instance : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) => PreservesLimitPair.ofIsoProdComparison F X₁ X₃
    exact ⟨fun {K} => preservesLimitOfIsoDiagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) ⟶
      binaryProductTriangle (F.obj X₁) (F.obj X₃) :=
    { hom₁ := 𝟙 _
      hom₂ := prodComparison F X₁ X₃
      hom₃ := 𝟙 _
      comm₁ := by
        dsimp
        ext
        · simp only [assoc, prodComparison_fst, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
            ← F.map_comp, F.map_id]
        · simp only [assoc, prodComparison_snd, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
            ← F.map_comp, F.map_zero]
      comm₂ := by simp
      comm₃ := by simp }
  exact isIso₂_of_isIso₁₃ φ (F.map_distinguished _ (binaryProductTriangle_distinguished X₁ X₃))
    (binaryProductTriangle_distinguished _ _)
    (by dsimp ; infer_instance) (by dsimp ; infer_instance)

instance : F.Additive := F.additive_of_preserves_binary_products

end IsTriangulated

lemma map_distinguished_iff [F.IsTriangulated] [Full F] [Faithful F] (T : Triangle C) :
    (F.mapTriangle.obj T ∈ distTriang D) ↔ T ∈ distTriang C := by
  constructor
  · intro hT
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
    refine' isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso _)
    exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem) (Iso.refl _) (Iso.refl _)
      (by simp)
  · exact F.map_distinguished T

def mapTriangleIso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] : F₁.mapTriangle ≅ F₂.mapTriangle :=
  NatIso.ofComponents (fun T =>
    Triangle.isoMk _ _ (e.app _) (e.app _) (e.app _) (by simp) (by simp) (by
      dsimp
      simp only [assoc, NatTrans.CommShift.comm_app e.hom (1 : ℤ) T.obj₁,
        NatTrans.naturality_assoc])) (by aesop_cat)

lemma isTriangulated_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] [F₁.IsTriangulated] : F₂.IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (F₁.map_distinguished T hT) _ ((mapTriangleIso e).app T).symm

lemma isTriangulated_iff_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] : F₁.IsTriangulated ↔ F₂.IsTriangulated := by
  constructor
  · intro
    exact isTriangulated_of_iso e
  · intro
    have : NatTrans.CommShift e.symm.hom ℤ := by
      dsimp
      infer_instance
    exact isTriangulated_of_iso e.symm

instance (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
    [G.IsTriangulated] : (F ⋙ G).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (G.map_distinguished _ (F.map_distinguished T hT)) _
      ((mapTriangleCompIso F G).app T)

lemma isTriangulated_iff_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [NatTrans.CommShift e.hom ℤ]
    [G.IsTriangulated] [Full G] [Faithful G] :
    F.IsTriangulated ↔ H.IsTriangulated := by
  rw [← isTriangulated_iff_of_iso e]
  constructor
  · intro
    infer_instance
  · intro
    constructor
    intro T hT
    rw [← G.map_distinguished_iff]
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
      ((mapTriangleCompIso F G).symm.app T)

end Functor

section

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ]

lemma IsTriangulated.of_fully_faithful_triangulated_functor
    [F.IsTriangulated] [Full F] [Faithful F] [IsTriangulated D] :
    IsTriangulated C where
  octahedron_axiom {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃} comm
    {v₁₂ w₁₂} h₁₂ {v₂₃ w₂₃} h₂₃ {v₁₃ w₁₃} h₁₃ := by
    have comm' : F.map u₁₂ ≫ F.map u₂₃ = F.map u₁₃ := by rw [← comm, F.map_comp]
    have H := Triangulated.someOctahedron comm' (F.map_distinguished _ h₁₂)
      (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃)
    exact
      ⟨{
        m₁ := F.preimage H.m₁
        m₃ := F.preimage H.m₃
        comm₁ := F.map_injective (by simpa using H.comm₁)
        comm₂ := F.map_injective (by
          rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₁)]
          simpa using H.comm₂)
        comm₃ := F.map_injective (by simpa using H.comm₃)
        comm₄ := F.map_injective (by
          rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₂)]
          simpa using H.comm₄)
        mem := by
          rw [← F.map_distinguished_iff]
          simpa using H.mem }⟩

end

end CategoryTheory
