import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.CommShift

universe u v

namespace CategoryTheory

open Limits Category Functor

namespace Triangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

open Pretriangulated

abbrev IsTriangleMorphism (T T' : Triangle C) (u : T.obj₁ ⟶ T'.obj₁) (v : T.obj₂ ⟶ T'.obj₂)
    (w : T.obj₃ ⟶ T'.obj₃) :=
  (T.mor₁ ≫ v = u ≫ T'.mor₁) ∧ (T.mor₂ ≫ w = v ≫ T'.mor₂) ∧
  (T.mor₃ ≫ (shiftFunctor C 1).map u = w ≫ T'.mor₃)

lemma NineGrid' {T_X T_Y : Triangle C} (dT_X : T_X ∈ distinguishedTriangles)
    (dT_Y : T_Y ∈ distinguishedTriangles) (u₁ : T_X.obj₁ ⟶ T_Y.obj₁) (u₂ : T_X.obj₂ ⟶ T_Y.obj₂)
    (comm : T_X.mor₁ ≫ u₂ = u₁ ≫ T_Y.mor₁) {Z₂ : C} (v₂ : T_Y.obj₂ ⟶ Z₂) (w₂ : Z₂ ⟶ T_X.obj₂⟦1⟧)
    (dT₂ : Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles) :
    ∃ (Z₁ Z₃ : C) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦1⟧) (v₁ : T_Y.obj₁ ⟶ Z₁)
    (w₁ : Z₁ ⟶ T_X.obj₁⟦1⟧) (u₃ : T_X.obj₃ ⟶ T_Y.obj₃) (v₃ : T_Y.obj₃ ⟶ Z₃)
    (w₃ : Z₃ ⟶ T_X.obj₃⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism T_X T_Y u₁ u₂ u₃ ∧
    IsTriangleMorphism T_Y (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ T_X.mor₁⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ T_X.mor₂⟦1⟧' = g ≫ w₃ ∧
    w₃ ≫ T_X.mor₃⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨Z₁, v₁, w₁, dT₁⟩ := distinguished_cocone_triangle u₁
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T_X.mor₁ ≫ u₂)
  set oct₁ := someOctahedron (u₁₂ := T_X.mor₁) (u₂₃ := u₂) (u₁₃ := T_X.mor₁ ≫ u₂) rfl dT_X
    dT₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := u₁) (u₂₃ := T_Y.mor₁) (u₁₃ := T_X.mor₁ ≫ u₂)
    comm.symm dT₁ dT_Y dTdiag
  obtain ⟨Z₃, g, h, dT_Z⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT_Z
  existsi Z₁, Z₃, (oct₂.m₁ ≫ oct₁.m₃), g, h, v₁, w₁, oct₁.m₁ ≫ oct₂.m₃, oct₃.m₁, oct₃.m₃
  constructor
  . exact dT_Z
  · constructor
    · exact dT₁
    · constructor
      · have := inv_rot_of_distTriang _ oct₃.mem
        refine isomorphic_distinguished _ this _ (Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_)
        · have := (shiftFunctorCompIsoId C 1 (-1)
              (by simp only [Int.reduceNeg, add_right_neg])).app T_X.obj₃
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj] at this
          exact this.symm
        · exact Iso.refl _
        · exact Iso.refl _
        · simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Triangle.invRotate_obj₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₁, Int.reduceNeg,
          Triangle.mk_obj₃, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_mor₁,
          Preadditive.neg_comp, Functor.map_neg, Functor.map_comp, assoc, neg_neg]
          rw [← cancel_epi ((shiftFunctorCompIsoId C 1 (-1) (by simp only [Int.reduceNeg,
            add_right_neg])).hom.app T_X.obj₃)]
          rw [← cancel_mono ((shiftFunctorCompIsoId C 1 (-1) (by simp only [Int.reduceNeg,
            add_right_neg])).inv.app T_Y.obj₃)]
          rw [assoc]; conv_lhs => erw [← shift_shift_neg']
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc,
            assoc, Iso.hom_inv_id_app, comp_id]
          simp only [Int.reduceNeg, Functor.map_comp]
        · simp only [Triangle.mk_obj₂, Triangle.invRotate_obj₃, Triangle.mk_obj₃,
          Triangle.mk_mor₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₂, Triangle.mk_obj₁,
          Triangle.invRotate_mor₂, Triangle.mk_mor₁, id_comp]
        · simp only [Triangle.mk_obj₃, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₁,
           Triangle.mk_mor₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_obj₃,
           Triangle.mk_obj₂, Iso.refl_hom, Triangle.invRotate_mor₃, Triangle.mk_mor₂, id_comp]
          rw [shift_shiftFunctorCompIsoId_inv_app]
      · constructor
        · constructor
          · exact comm
          · constructor
            · rw [← assoc, oct₁.comm₁, assoc, oct₂.comm₃]
            · conv_rhs => rw [assoc, ← oct₂.comm₄, ← assoc, oct₁.comm₂]
        · constructor
          · constructor
            · simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₁]
              conv_rhs => rw [← assoc, oct₂.comm₁, assoc, oct₁.comm₃]
            · constructor
              · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
                Triangle.mk_mor₁, Triangle.mk_mor₂]
                conv_lhs => congr; rw [← oct₂.comm₃]
                rw [assoc, oct₃.comm₁, ← assoc, oct₁.comm₃]
              · exact oct₃.comm₂.symm
          · constructor
            · simp only [Triangle.mk_obj₁, Triangle.shiftFunctor_obj, Int.negOnePow_one,
              Functor.comp_obj, Triangle.mk_obj₂, Triangle.mk_mor₁, assoc, Units.neg_smul, one_smul,
              Preadditive.comp_neg]
              rw [← oct₁.comm₄, ← assoc, oct₂.comm₂]
            · constructor
              · rw [oct₃.comm₃]; simp only [Triangle.mk_mor₃]
              · conv_rhs => congr; rw [← oct₂.comm₂]
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Functor.map_comp]
                conv_lhs => congr; rfl; rw [← oct₁.comm₂]
                have := oct₃.comm₄
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Preadditive.comp_neg] at this
                rw [← assoc, this]
                simp only [Functor.map_comp, Preadditive.neg_comp, assoc, neg_neg]

/-- Proposition 1.1.11 of of [BBD].
-/
lemma NineGrid {X₁ X₂ Y₁ Y₂ : C} (u₁ : X₁ ⟶ Y₁) (u₂ : X₂ ⟶ Y₂) (f_X : X₁ ⟶ X₂) (f_Y : Y₁ ⟶ Y₂)
    (comm : f_X ≫ u₂ = u₁ ≫ f_Y) :
    ∃ (X₃ Y₃ Z₁ Z₂ Z₃ : C) (g_X : X₂ ⟶ X₃) (h_X : X₃ ⟶ X₁⟦1⟧) (g_Y : Y₂ ⟶ Y₃)
    (h_Y : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦(1 : ℤ)⟧) (u₃ : X₃ ⟶ Y₃)
    (v₁ : Y₁ ⟶ Z₁) (v₂ : Y₂ ⟶ Z₂) (v₃ : Y₃ ⟶ Z₃) (w₁ : Z₁ ⟶ X₁⟦(1 : ℤ)⟧) (w₂ : Z₂ ⟶ X₂⟦(1 : ℤ)⟧)
    (w₃ : Z₃ ⟶ X₃⟦(1 : ℤ)⟧),
    Triangle.mk f_X g_X h_X ∈ distinguishedTriangles ∧
    Triangle.mk f_Y g_Y h_Y ∈ distinguishedTriangles ∧
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism (Triangle.mk f_X g_X h_X) (Triangle.mk f_Y g_Y h_Y) u₁ u₂ u₃ ∧
    IsTriangleMorphism (Triangle.mk f_Y g_Y h_Y) (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ f_X⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ g_X⟦1⟧' = g ≫ w₃ ∧ w₃ ≫ h_X⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨X₃, g_X, h_X, dT_X⟩ := Pretriangulated.distinguished_cocone_triangle f_X
  obtain ⟨Y₃, g_Y, h_Y, dT_Y⟩ := Pretriangulated.distinguished_cocone_triangle f_Y
  obtain ⟨Z₂, v₂, w₂, dT₂⟩ := Pretriangulated.distinguished_cocone_triangle u₂
  obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, dT_Z, dT₁, dT₃, comm_XY, comm_YZ, comm₁, comm₂,
    comm₃⟩ := NineGrid' dT_X dT_Y u₁ u₂ comm v₂ w₂ dT₂
  existsi X₃, Y₃, Z₁, Z₂, Z₃, g_X, h_X, g_Y, h_Y, f, g, h, u₃, v₁, v₂, v₃, w₁, w₂, w₃
  exact ⟨dT_X, dT_Y, dT_Z, dT₁, dT₂, dT₃, comm_XY, comm_YZ, comm₁, comm₂, comm₃⟩

end Triangulated

namespace Pretriangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable instance : (Triangle.π₁ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, Functor.comp_map, Triangle.π₁_map, Triangle.shiftFunctor_map_hom₁,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₁_map, Triangle.shiftFunctorAdd'_hom_app_hom₁, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

noncomputable instance : (Triangle.π₂ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, Functor.comp_map, Triangle.π₂_map, Triangle.shiftFunctor_map_hom₂,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₂_map, Triangle.shiftFunctorAdd'_hom_app_hom₂, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

noncomputable instance : (Triangle.π₃ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, Functor.comp_map, Triangle.π₃_map, Triangle.shiftFunctor_map_hom₃,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₃_map, Triangle.shiftFunctorAdd'_hom_app_hom₃, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

end Pretriangulated

end CategoryTheory
