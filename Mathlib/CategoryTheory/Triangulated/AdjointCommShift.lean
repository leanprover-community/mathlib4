import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Triangulated.Lemmas

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
    ((shiftEquiv D (0 : A)).symm.toAdjunction.homEquiv (F.obj X) Y).symm u =
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

lemma lemme2 (X : C) (Y : D) (u : X⟦(-0 : A)⟧ ⟶ (G.obj Y)) :
    ((shiftEquiv C (0 : A)).symm.toAdjunction.homEquiv X (G.obj Y)) u =
    ((shiftFunctorZero' C (-0 : A) neg_zero).app X).inv ≫ u ≫
    ((shiftFunctorZero C A).app (G.obj Y)).inv := by
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
    shiftEquiv'_inverse, homEquiv_unit, id_obj, comp_obj, Equivalence.toAdjunction_unit,
    Iso.app_inv]
  have heq : (shiftEquiv C (0 : A)).symm.unit =
      (shiftFunctorCompIsoId C (-0 : A) 0 (by simp)).inv := by
    change (shiftEquiv C (0 : A)).symm.unitIso.hom = _
    rw [Equivalence.symm_unitIso]
    simp
  rw [heq]
  simp only [shiftFunctorCompIsoId, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, id_obj,
    comp_obj, assoc]
  erw [(shiftFunctorZero C A).inv.naturality u]
  simp only [id_obj]
  rw [← assoc, ← assoc]; congr 1
  rw [shiftFunctorAdd'_eqToIso (C := C) (A := A) (-0) 0 0 (-0) 0 (-0) (by simp) (by simp) (by simp)
    (by simp)]
  simp only [Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, comp_obj, eqToHom_app]
  rw [shiftFunctorAdd'_add_zero]
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, NatTrans.comp_app, comp_obj, id_obj,
    rightUnitor_inv_app, whiskerLeft_app, id_comp, eqToHom_refl, comp_id]
  rw [← assoc]; congr 1
  simp only [shiftFunctorZero', Iso.trans_inv, eqToIso.inv, NatTrans.comp_app, id_obj, eqToHom_app]

lemma lemme3 (adj : F ⊣ G) (X : C) (Y : D) (u : X ⟶ G.obj (Y⟦0⟧)) :
    (adj.homEquiv X ((shiftEquiv D 0).functor.obj Y)).symm u ≫
    ((shiftFunctorZero D A).app Y).hom = (adj.homEquiv X Y).symm
    (u ≫ G.map ((shiftFunctorZero D A).app Y).hom) := by simp

lemma lemme4 (commF : CommShift F A) (X : C) (Y : D) (u : F.obj X ⟶ Y) (a : A) (ha : a = 0) :
    ((yoneda.obj Y).map ((commF.iso a).hom.app X).op)
    (((shiftFunctorZero' D a ha).app (F.obj X)).hom ≫ u) =
    F.map ((shiftFunctorZero' C a ha).app X).hom ≫ u := by
  simp only [comp_obj, yoneda_obj_obj, id_obj, Iso.app_hom, yoneda_obj_map, Quiver.Hom.unop_op]
  rw [← assoc]; congr 1
  have := Functor.commShiftIso_zero' F a ha
  change commF.iso a = _ at this
  rw [this]
  simp

lemma lemme5 (adj : F ⊣ G) (X : C) (Y : D) (u : F.obj X ⟶ Y) (a : A) (ha : a = 0) :
    (adj.homEquiv (X⟦a⟧) Y) (F.map ((shiftFunctorZero' C a ha).app X).hom ≫ u) =
    ((shiftFunctorZero' C a ha).app X).hom ≫ adj.homEquiv X Y u := by simp

lemma left_to_right_iso_apply'''' (adj : F ⊣ G) (commF : CommShift F A) (a b : A) (X : C) (Y : D) :
    (yoneda.map ((shiftFunctor C b).map ((left_to_right_iso adj commF a).hom.app Y))).app (op X) =
    sorry := by
  simp
  sorry

noncomputable def left_to_right (adj : F ⊣ G) (commF : CommShift F A) :
    CommShift G A where
  iso := left_to_right_iso adj commF
  zero := by
    ext Y
    apply Functor.map_injective (yoneda (C := C))
    ext X u
    simp at u
    rw [left_to_right_iso_apply''']
    simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor,
      comp_homEquiv, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, Equiv.coe_trans, types_comp_apply,
      Equiv.symm_trans_apply, id_obj, map_comp,
      assoc, Quiver.Hom.unop_op, Function.comp_apply,
      CommShift.isoZero_hom_app, FunctorToTypes.comp]
    erw [lemme1]; erw [lemme2]
    rw [lemme3]; rw [lemme4]; erw [lemme5]
    simp
  add a b := by
    ext Y
    apply Functor.map_injective (yoneda (C := C))
    ext X u
    rw [CommShift.isoAdd_hom_app, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    conv_lhs => rw [left_to_right_iso_apply''']
    conv_rhs => rw [left_to_right_iso_apply''']
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
