import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Triangulated.Lemmas

section MiseAJour

universe u₁ v₁ u₂ v₂ u₃ v₃

theorem CategoryTheory.Adjunction.comp_homEquiv {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]
    {D : Type u₂} [CategoryTheory.Category.{v₂, u₂} D] {F : CategoryTheory.Functor C D}
    {G : CategoryTheory.Functor D C} {E : Type u₃} [ℰ : CategoryTheory.Category.{v₃, u₃} E]
    {H : CategoryTheory.Functor D E} {I : CategoryTheory.Functor E D} (adj₁ : F ⊣ G)
    (adj₂ : H ⊣ I) : (adj₁.comp adj₂).homEquiv = fun (x : C) (x_1 : E) =>
    (adj₂.homEquiv (F.obj x) x_1).trans (adj₁.homEquiv x (I.obj x_1)) := sorry

@[simp]
theorem CategoryTheory.Adjunction.homEquiv_apply{C : Type u₁} [CategoryTheory.Category.{v₁, u₁}     C] {D : Type u₂} [CategoryTheory.Category.{v₂, u₂}     D] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C} (adj : F ⊣ G) (X : C) (Y : D) (f : F.obj X ⟶ Y) :
(adj.homEquiv X Y) f = CategoryTheory.CategoryStruct.comp (adj.unit.app X) (G.map f) := sorry

@[simp]
theorem CategoryTheory.Adjunction.homEquiv_symm_apply{C : Type u₁} [CategoryTheory.Category.{v₁, u₁}     C] {D : Type u₂} [CategoryTheory.Category.{v₂, u₂}     D] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C} (adj : F ⊣ G) (X : C) (Y : D) (g : X ⟶ G.obj Y) :
(adj.homEquiv X Y).symm g = CategoryTheory.CategoryStruct.comp (F.map g) (adj.counit.app Y) := sorry

end MiseAJour

namespace CategoryTheory

open Category Functor CategoryTheory Opposite

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} {A : Type*} [AddGroup A]
  [HasShift C A] [HasShift D A]

namespace CommShift

noncomputable def left_to_right_iso (adj : F ⊣ G) (commF : CommShift F A) (a : A) :=
  (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction)
  (Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj)).invFun (commF.iso (-a))

lemma left_to_right_iso_apply (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D) :
    (coyoneda.obj (op X)).map ((left_to_right_iso adj commF a).hom.app Y) =
    (((Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm.toIso
    ≪≫ (coyoneda.mapIso ((commF.iso (-a)).app X).op).app Y ≪≫
    ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y).toIso).hom := by
  ext f
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, coyoneda_obj_obj,
    left_to_right_iso, Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe,
    mapIso_hom, Iso.app_hom, natIsoEquiv_symm_apply_hom, natTransEquiv_symm_apply_app,
    id_obj, Equivalence.toAdjunction_unit, comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc, coyoneda_obj_map,
    Iso.trans_hom, Equiv.toIso_hom, Iso.op_hom, types_comp_apply, coyoneda_map_app,
    Quiver.Hom.unop_op]
  erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_apply]
  simp only [id_obj, comp_obj, Equivalence.toAdjunction_unit, assoc,
    Functor.comp_map, Equivalence.toAdjunction_counit, map_comp]
  slice_lhs 1 2 => erw [((shiftEquiv C a).symm.toAdjunction.comp adj).unit.naturality f]
  conv_lhs => congr; congr; congr; congr; rfl; simp
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [(commF.iso (-a)).hom.naturality f]
  simp

lemma left_to_right_iso_apply' (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D) :
    (coyoneda.obj (op X)).mapIso ((left_to_right_iso adj commF a).app Y) =
    ((Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm.toIso
    ≪≫ (coyoneda.mapIso ((commF.iso (-a)).app X).op).app Y ≪≫
    ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y).toIso := by
  ext f
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, coyoneda_obj_obj,
    left_to_right_iso, Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe,
    mapIso_hom, Iso.app_hom, natIsoEquiv_symm_apply_hom, natTransEquiv_symm_apply_app,
    id_obj, Equivalence.toAdjunction_unit, comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc, coyoneda_obj_map,
    Iso.trans_hom, Equiv.toIso_hom, Iso.op_hom, types_comp_apply, coyoneda_map_app,
    Quiver.Hom.unop_op]
  erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_apply]
  simp only [id_obj, comp_obj, Equivalence.toAdjunction_unit, assoc,
    Functor.comp_map, Equivalence.toAdjunction_counit, map_comp]
  slice_lhs 1 2 => erw [((shiftEquiv C a).symm.toAdjunction.comp adj).unit.naturality f]
  conv_lhs => congr; congr; congr; congr; rfl; simp
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [(commF.iso (-a)).hom.naturality f]
  simp

lemma left_to_right_iso_apply'' (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D) :
    (yoneda.mapIso ((left_to_right_iso adj commF a).app Y)).app (op X) =
    ((Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm.toIso ≪≫
    (yoneda.obj Y).mapIso ((commF.iso (-a)).app X).op ≪≫
    ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y).toIso := by
  ext f
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, yoneda_obj_obj,
    left_to_right_iso, Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe,
    Iso.app_hom, mapIso_hom, natIsoEquiv_symm_apply_hom, natTransEquiv_symm_apply_app,
    id_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc, FunctorToTypes.comp,
    yoneda_map_app, coyoneda_obj_obj, Iso.trans_hom, Equiv.toIso_hom, Iso.op_hom, types_comp_apply,
    coyoneda_map_app, Quiver.Hom.unop_op]
  erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_apply]
  simp only [id_obj, comp_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, map_comp, assoc, Functor.comp_map]
  slice_lhs 1 2 => erw [((shiftEquiv C a).symm.toAdjunction.comp adj).unit.naturality f]
  conv_lhs => congr; congr; congr; congr; rfl; simp
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [(commF.iso (-a)).hom.naturality f]
  simp

lemma left_to_right_iso_apply''' (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D) :
    (yoneda.map ((left_to_right_iso adj commF a).hom.app Y)).app (op X) =
    (((Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm.toIso ≪≫
    (yoneda.obj Y).mapIso ((commF.iso (-a)).app X).op ≪≫
    ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y).toIso).hom := by
  ext f
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, yoneda_obj_obj,
    left_to_right_iso, Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe,
    Iso.app_hom, mapIso_hom, natIsoEquiv_symm_apply_hom, natTransEquiv_symm_apply_app,
    id_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc, FunctorToTypes.comp,
    yoneda_map_app, coyoneda_obj_obj, Iso.trans_hom, Equiv.toIso_hom, Iso.op_hom, types_comp_apply,
    coyoneda_map_app, Quiver.Hom.unop_op]
  erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_apply]
  simp only [id_obj, comp_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, map_comp, assoc, Functor.comp_map]
  slice_lhs 1 2 => erw [((shiftEquiv C a).symm.toAdjunction.comp adj).unit.naturality f]
  conv_lhs => congr; congr; congr; congr; rfl; simp
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [(commF.iso (-a)).hom.naturality f]
  simp

noncomputable def right_to_left_iso (adj : F ⊣ G) (commG : CommShift G A) (a : A) :=
  (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
  (add_left_neg _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
  (add_left_neg _)).symm.toAdjunction adj)).toFun (commG.iso (-a))

lemma right_to_left_iso_apply (adj : F ⊣ G) (commG : CommShift G A) (a : A) (X : C) (Y : D) :
    (coyoneda.map (op ((right_to_left_iso adj commG a).hom.app X))).app Y = sorry := by
  simp
  have := ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y)
  sorry

lemma lemme1 (X : C) (Y : D) (u : F.obj X ⟶ Y⟦(0 : A)⟧) :
    ((shiftEquiv D (0 : A)).symm.toAdjunction.homEquiv (F.obj X) Y).invFun u =
    ((shiftFunctorZero' D (-0 : A) neg_zero).app (F.obj X)).hom ≫ u ≫
    ((shiftFunctorZero D A).app Y).hom := by
  simp
  conv_rhs => erw [← assoc, ← (shiftFunctorZero' D (-0 : A) neg_zero).hom.naturality u]
  rw [assoc]
  congr 1
  have heq : (shiftEquiv D (0 : A)).symm.counit.app Y =
      (CategoryTheory.shiftFunctorCompIsoId D (0 : A) (-0) (by simp)).hom.app Y := by
    change (shiftEquiv D (0 : A)).symm.counitIso.hom.app Y = _
    rw [Equivalence.symm_counitIso]
    simp
  rw [heq]
  simp [shiftFunctorCompIsoId]
  rw [shiftFunctorAdd'_add_zero' D (0 : A) (-0) (by simp) (by simp)]
  simp

noncomputable def left_to_right (adj : F ⊣ G) (commF : CommShift F A) :
    CommShift G A where
  iso := left_to_right_iso adj commF
  zero := by
    ext Y
    apply Functor.map_injective (yoneda (C := C))
    ext X u
    simp at u
    rw [left_to_right_iso_apply''']
    simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, yoneda_obj_obj,
      Equivalence.symm_functor, shiftEquiv'_inverse, comp_homEquiv, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, Equiv.coe_trans, types_comp_apply,
      Equiv.symm_trans_apply, homEquiv_counit, id_obj, map_comp, Equivalence.toAdjunction_counit,
      assoc, yoneda_obj_map, Quiver.Hom.unop_op, Function.comp_apply, homEquiv_unit,
      Equivalence.toAdjunction_unit, CommShift.isoZero_hom_app, FunctorToTypes.comp, yoneda_map_app]
    slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp]
                     erw [← (commF.iso (-0)).hom.naturality u]
                     rw [Functor.map_comp, Functor.map_comp]
    slice_lhs 2 3 => rw [← Functor.map_comp]; erw [← adj.unit.naturality (u⟦(-0 : A)⟧')]
    simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, id_obj, Functor.id_map,
      map_comp, assoc]
    slice_lhs 1 2 => erw [← (shiftEquiv C (0 : A)).symm.unit.naturality u]
    simp
    have : commF.iso (-0) = CommShift.isoZero' F A (-0) (by simp) :=
      @commShiftIso_zero' C D _ _ F A _ _ _ commF (-0) (by simp)
    rw [this]
    simp
    sorry
  add a b := by
    ext Y
    apply Functor.map_injective (yoneda (C := C))
    ext X u
    rw [CommShift.isoAdd_hom_app, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    conv_rhs => rw [left_to_right_iso_apply''']--, left_to_right_iso_apply''']
    sorry



noncomputable def right_to_left (adj : F ⊣ G) (commG : CommShift G A) :
    CommShift F A where
  iso a := (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
    (add_left_neg _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
    (add_left_neg _)).symm.toAdjunction adj)).toFun (commG.iso (-a))
  zero := by sorry
  add a b := by sorry

noncomputable def left_right_equiv (adj : F ⊣ G) : CommShift F A ≃ CommShift G A where
  toFun := left_to_right adj
  invFun := right_to_left adj
  left_inv commF := by
    ext a X
    simp [left_to_right, right_to_left]
    sorry
  right_inv := sorry

end CommShift

end Adjunction

end CategoryTheory
