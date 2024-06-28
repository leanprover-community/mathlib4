import Mathlib.CategoryTheory.Triangulated.Triangulated

universe u v

namespace CategoryTheory

open Limits Category

namespace Triangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

open Pretriangulated

def IsTriangleMorphism (T T' : Triangle C) (u : T.obj₁ ⟶ T'.obj₁) (v : T.obj₂ ⟶ T'.obj₂)
    (w : T.obj₃ ⟶ T'.obj₃) :=
  (T.mor₁ ≫ v = u ≫ T'.mor₁) ∧ (T.mor₂ ≫ w = v ≫ T'.mor₂) ∧
  (T.mor₃ ≫ (shiftFunctor C 1).map u = w ≫ T'.mor₃)

lemma NineGrid {T_X T_Y : Triangle C} (dT_X : T_X ∈ distinguishedTriangles)
    (dT_Y : T_Y ∈ distinguishedTriangles) (u₁ : T_X.obj₁ ⟶ T_Y.obj₁) (u₂ : T_X.obj₂ ⟶ T_Y.obj₂)
    (comm : T_X.mor₁ ≫ u₂ = u₁ ≫ T_Y.mor₁) {Z₂ : C} (v₂ : T_Y.obj₂ ⟶ Z₂) (w₂ : Z₂ ⟶ T_X.obj₂⟦1⟧)
    (dT₂ : Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles) :
    ∃ (Z₁ Z₃ : C) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦1⟧) (v₁ : T_Y.obj₁ ⟶ Z₁)
    (w₁ : Z₁ ⟶ T_X.obj₁⟦1⟧) (u₃ : T_X.obj₃ ⟶ T_Y.obj₃) (v₃ : T_Y.obj₃ ⟶ Z₃)
    (w₃ : Z₃ ⟶ T_X.obj₃⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism T_X T_Y u₁ u₂ u₃ := by
  obtain ⟨Z₁, v₁, w₁, dT₁⟩ := distinguished_cocone_triangle u₁
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T_X.mor₁ ≫ u₂)
  set oct₁ := someOctahedron (u₁₂ := T_X.mor₁) (u₂₃ := u₂) (u₁₃ := T_X.mor₁ ≫ u₂) rfl dT_X
    dT₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := u₁) (u₂₃ := T_Y.mor₁) (u₁₃ := T_X.mor₁ ≫ u₂)
    comm.symm dT₁ dT_Y dTdiag
  obtain ⟨Z₃, g, h, dT_Z⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT_Z
  existsi Z₁, Z₃, (oct₂.m₁ ≫ oct₁.m₃), g, h, v₁, w₁, oct₁.m₁ ≫ oct₂.m₃

/-  existsi Triangle.homMk T' (Triangle.mk (oct₂.m₁ ≫ oct₁.m₃) g h) u' u oct₃.m₁
    (by simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₁]
        rw [← assoc, oct₂.comm₁, assoc, oct₁.comm₃])
    (by simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁, Triangle.mk_mor₂]
        conv_rhs => congr; rw [← oct₁.comm₃]
        rw [assoc, ← oct₃.comm₁, ← assoc, oct₂.comm₃])
    (by simp only [Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁]
        rw [oct₃.comm₂])
  existsi Triangle.homMk (Triangle.mk (oct₂.m₁ ≫ oct₁.m₃) g h) ((Triangle.shiftFunctor C 1).obj T)
    v' (-v) oct₃.m₃
    (by simp only [Triangle.mk_obj₁, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₂, Triangle.mk_mor₁, Preadditive.comp_neg, assoc, Units.neg_smul, one_smul,
      neg_inj]
        rw [← oct₁.comm₄, ← assoc, oct₂.comm₂])
    (by simp only [Triangle.mk_obj₂, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₃, Triangle.mk_mor₂, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁,
      Units.neg_smul, one_smul, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg]
        rw [oct₃.comm₃]
        simp only [Triangle.mk_mor₃])
    (by simp only [Triangle.mk_obj₃, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
      shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app, comp_id, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
        conv_rhs => congr; congr; rfl; rw [← oct₁.comm₂]
        simp only [Functor.map_comp]
        have := oct₃.comm₄
        apply_fun (fun X ↦ X ≫ (shiftFunctor C 1).map b) at this
        simp only [assoc, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Preadditive.comp_neg, Preadditive.neg_comp] at this
        rw [← this]
        conv_lhs => congr; rfl; rw [← oct₂.comm₂]
        simp only [Functor.map_comp])
  constructor
  · simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁,
    Triangle.homMk_hom₂]
  · constructor
    · simp only [Triangle.mk_obj₂, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁, Triangle.homMk_hom₂]
    · constructor
      · exact dT''
      · constructor
        · simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Triangle.homMk_hom₁, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj]
          exact dT₁
        · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁, Triangle.homMk_hom₃, Triangle.shiftFunctor_obj, Int.negOnePow_one,
          Functor.comp_obj]
          have := inv_rot_of_distTriang _ oct₃.mem
          simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
            Preadditive.neg_comp] at this
          refine isomorphic_distinguished _ this _ (Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_)
          · simp only [Triangle.mk_obj₁, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₃]
            have := (shiftFunctorCompIsoId C 1 (-1)
              (by simp only [Int.reduceNeg, add_right_neg])).app T.obj₃
            simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj] at this
            exact this.symm
          · exact Iso.refl _
          · exact Iso.refl _
          · simp only [Triangle.mk_obj₁, Triangle.invRotate_obj₂, Triangle.mk_obj₂,
            Triangle.mk_mor₁, Iso.refl_hom, comp_id, Triangle.invRotate_obj₁, Int.reduceNeg,
            Triangle.mk_obj₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_mor₁,
            Triangle.mk_mor₃, Functor.map_neg, Functor.map_comp, Preadditive.neg_comp, assoc,
            neg_neg]
            rw [← cancel_epi ((shiftFunctorCompIsoId C 1 (-1) sorry).hom.app T.obj₃)]
            rw [← cancel_mono ((shiftFunctorCompIsoId C 1 (-1) sorry).inv.app T'.obj₃)]
            rw [assoc]; conv_lhs => erw [← shift_shift_neg']
            simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc,
              assoc, Iso.hom_inv_id_app, comp_id]
            have := oct₃.comm₄
            simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
              Preadditive.comp_neg] at this
          · simp only [Triangle.mk_obj₂, Triangle.invRotate_obj₃, Triangle.mk_obj₃,
            Triangle.mk_mor₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₂, Triangle.mk_obj₁,
            Triangle.invRotate_mor₂, Triangle.mk_mor₁, id_comp]
          · simp only [Triangle.mk_obj₃, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₁,
            Triangle.mk_mor₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_obj₃,
            Triangle.mk_obj₂, Iso.refl_hom, Triangle.invRotate_mor₃, Triangle.mk_mor₂, id_comp]
            rw [shift_shiftFunctorCompIsoId_inv_app]
-/
/-
lemma NineGrid {X Y X' Y': C} (f_X : X' ⟶ X) (u' : X' ⟶ Y') (f_Y : Y' ⟶ Y) (u : X ⟶ Y)
    (comm : f_X ≫ u = u' ≫ f_Y) {Z : C} (v : Y ⟶ Z) (w : Z ⟶ X⟦1⟧)
    (hvw : Triangle.mk u v w ∈ distinguishedTriangles) :
    ∃ (X'' Y'' Z' Z'' : C) (g_X : X ⟶ X'') (h_X : X'' ⟶ X'⟦1⟧) (g_Y : Y ⟶ Y'')  (h_Y : Y'' ⟶ Y'⟦1⟧)
    (f : Z' ⟶ Z) (g : Z ⟶ Z'') (h : Z'' ⟶ Z'⟦1⟧) (v' : Y' ⟶ Z') (w' : Z' ⟶ X'⟦1⟧)
    (u'' : X'' ⟶ Y'') (v'' : Y'' ⟶ Z'') (w'' : Z'' ⟶ X''⟦1⟧),
    Triangle.mk f_X g_X h_X ∈ distinguishedTriangles ∧
    Triangle.mk f_Y g_Y h_Y ∈ distinguishedTriangles ∧
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u' v' w' ∈ distinguishedTriangles ∧
    Triangle.mk u'' v'' w'' ∈ distinguishedTriangles ∧
    IsTriangleMorphism (Triangle.mk f_X g_X h_X) (Triangle.mk f_Y g_Y h_Y) u' u u'' := by
  obtain ⟨X'', g_X, h_X, dT_X⟩ := distinguished_cocone_triangle f_X
  obtain ⟨Y'', g_Y, h_Y, dT_Y⟩ := distinguished_cocone_triangle f_Y
  obtain ⟨Z', v', w', dT'⟩ := distinguished_cocone_triangle u'
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T.mor₁ ≫ F.hom₂)
  set oct₁ := someOctahedron (u₁₂ := T.mor₁) (u₂₃ := F.hom₂) (u₁₃ := T.mor₁ ≫ F.hom₂) rfl dT
    huv₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := F.hom₁) (u₂₃ := T'.mor₁) (u₁₃ := T.mor₁ ≫ F.hom₂)
    F.comm₁.symm dT₁ dT' dTdiag
  obtain ⟨Z'', g, h, dT''⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT''
-/

lemma NineGrid' {T T' : Triangle C} (dT : T ∈ distinguishedTriangles)
    (dT' : T' ∈ distinguishedTriangles) (F : T ⟶ T') {Z : C} (u : T'.obj₂ ⟶ Z)
    (v : Z ⟶ T.obj₂⟦1⟧)  (huv₁ : u ≫ v =0)
    (huv₂ : Triangle.mk F.hom₂ u v ∈ distinguishedTriangles) :
    ∃ (Z' Z'' : C) (f : Z' ⟶ Z) (g : Z ⟶ Z'') (h : Z'' ⟶ Z'⟦1⟧)
    (G : T' ⟶ Triangle.mk f g h) (H : Triangle.mk f g h ⟶ (Triangle.shiftFunctor C 1).obj T),
    G.hom₂ = u ∧ H.hom₂ = -v ∧ Triangle.mk f g h ∈ distinguishedTriangles
    ∧ Triangle.mk F.hom₁ G.hom₁ H.hom₁ ∈ distinguishedTriangles ∧
    Triangle.mk F.hom₃ G.hom₃ H.hom₃ ∈ distinguishedTriangles:= by
  obtain ⟨Z', u', v', dT₁⟩ := distinguished_cocone_triangle F.hom₁
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T.mor₁ ≫ F.hom₂)
  set oct₁ := someOctahedron (u₁₂ := T.mor₁) (u₂₃ := F.hom₂) (u₁₃ := T.mor₁ ≫ F.hom₂) rfl dT
    huv₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := F.hom₁) (u₂₃ := T'.mor₁) (u₁₃ := T.mor₁ ≫ F.hom₂)
    F.comm₁.symm dT₁ dT' dTdiag
  obtain ⟨Z'', g, h, dT''⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT''
  existsi Z', Z'', (oct₂.m₁ ≫ oct₁.m₃), g, h
  existsi Triangle.homMk T' (Triangle.mk (oct₂.m₁ ≫ oct₁.m₃) g h) u' u oct₃.m₁
    (by simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₁]
        rw [← assoc, oct₂.comm₁, assoc, oct₁.comm₃])
    (by simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁, Triangle.mk_mor₂]
        conv_rhs => congr; rw [← oct₁.comm₃]
        rw [assoc, ← oct₃.comm₁, ← assoc, oct₂.comm₃])
    (by simp only [Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁]
        rw [oct₃.comm₂])
  existsi Triangle.homMk (Triangle.mk (oct₂.m₁ ≫ oct₁.m₃) g h) ((Triangle.shiftFunctor C 1).obj T)
    v' (-v) oct₃.m₃
    (by simp only [Triangle.mk_obj₁, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₂, Triangle.mk_mor₁, Preadditive.comp_neg, assoc, Units.neg_smul, one_smul,
      neg_inj]
        rw [← oct₁.comm₄, ← assoc, oct₂.comm₂])
    (by simp only [Triangle.mk_obj₂, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₃, Triangle.mk_mor₂, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁,
      Units.neg_smul, one_smul, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg]
        rw [oct₃.comm₃]
        simp only [Triangle.mk_mor₃])
    (by simp only [Triangle.mk_obj₃, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
      shiftFunctorComm_eq_refl, Iso.refl_hom, NatTrans.id_app, comp_id, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
        conv_rhs => congr; congr; rfl; rw [← oct₁.comm₂]
        simp only [Functor.map_comp]
        have := oct₃.comm₄
        apply_fun (fun X ↦ X ≫ (shiftFunctor C 1).map b) at this
        simp only [assoc, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Preadditive.comp_neg, Preadditive.neg_comp] at this
        rw [← this]
        conv_lhs => congr; rfl; rw [← oct₂.comm₂]
        simp only [Functor.map_comp])
  constructor
  · simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁,
    Triangle.homMk_hom₂]
  · constructor
    · simp only [Triangle.mk_obj₂, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj,
      Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_mor₁, Triangle.homMk_hom₂]
    · constructor
      · exact dT''
      · constructor
        · simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Triangle.homMk_hom₁, Triangle.shiftFunctor_obj, Int.negOnePow_one, Functor.comp_obj]
          exact dT₁
        · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
          Triangle.mk_mor₁, Triangle.homMk_hom₃, Triangle.shiftFunctor_obj, Int.negOnePow_one,
          Functor.comp_obj]
          have := inv_rot_of_distTriang _ oct₃.mem
          simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
            Preadditive.neg_comp] at this
          refine isomorphic_distinguished _ this _ (Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_)
          · simp only [Triangle.mk_obj₁, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₃]
            have := (shiftFunctorCompIsoId C 1 (-1)
              (by simp only [Int.reduceNeg, add_right_neg])).app T.obj₃
            simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj] at this
            exact this.symm
          · exact Iso.refl _
          · exact Iso.refl _
          · simp only [Triangle.mk_obj₁, Triangle.invRotate_obj₂, Triangle.mk_obj₂,
            Triangle.mk_mor₁, Iso.refl_hom, comp_id, Triangle.invRotate_obj₁, Int.reduceNeg,
            Triangle.mk_obj₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_mor₁,
            Triangle.mk_mor₃, Functor.map_neg, Functor.map_comp, Preadditive.neg_comp, assoc,
            neg_neg]
            rw [← cancel_epi ((shiftFunctorCompIsoId C 1 (-1) sorry).hom.app T.obj₃)]
            rw [← cancel_mono ((shiftFunctorCompIsoId C 1 (-1) sorry).inv.app T'.obj₃)]
            rw [assoc]; conv_lhs => erw [← shift_shift_neg']
            simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc,
              assoc, Iso.hom_inv_id_app, comp_id]
            have := oct₃.comm₄
            simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
              Preadditive.comp_neg] at this
          · simp only [Triangle.mk_obj₂, Triangle.invRotate_obj₃, Triangle.mk_obj₃,
            Triangle.mk_mor₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₂, Triangle.mk_obj₁,
            Triangle.invRotate_mor₂, Triangle.mk_mor₁, id_comp]
          · simp only [Triangle.mk_obj₃, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₁,
            Triangle.mk_mor₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_obj₃,
            Triangle.mk_obj₂, Iso.refl_hom, Triangle.invRotate_mor₃, Triangle.mk_mor₂, id_comp]
            rw [shift_shiftFunctorCompIsoId_inv_app]

end Triangulated

end CategoryTheory
