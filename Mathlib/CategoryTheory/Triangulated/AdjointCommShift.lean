import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Triangulated.Lemmas
import Mathlib.CategoryTheory.Adjunction.Opposites

namespace CategoryTheory

open Category Functor CategoryTheory Opposite

namespace Adjunction

universe u₁ u₂ v₁ v₂ u

/-variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} {A : Type*} [AddGroup A]
  [HasShift C A] [HasShift D A]-/

variable {C : Type u₁} {D : Type u₂} [Category.{v₁,u₁} C] [Category.{v₂,u₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {A : Type u} [AddGroup A]
  [HasShift C A] [HasShift D A]

namespace CommShift

noncomputable def left_to_right_iso (adj : F ⊣ G) (commF : CommShift F A) (a : A) :=
  (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction)
  (Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj)).invFun (commF.iso (-a))

lemma comp_left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D)
    (u : X ⟶ G.obj (Y⟦a⟧)) :
    u ≫ (left_to_right_iso adj commF a).hom.app Y =
    (((shiftEquiv C a).symm.toAdjunction.comp adj).homEquiv X Y) ((CommShift.iso (-a)).hom.app X ≫
    ((adj.comp (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm u) := by
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, left_to_right_iso,
    Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe, natIsoEquiv_symm_apply_hom,
    natTransEquiv_symm_apply_app, id_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc]
  erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_apply]
  simp only [id_obj, comp_obj, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_counit, map_comp, assoc, Functor.comp_map]
  slice_lhs 1 2 => erw [((shiftEquiv C a).symm.toAdjunction.comp adj).unit.naturality u]
  conv_lhs => congr; congr; congr; congr; rfl; simp
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [(commF.iso (-a)).hom.naturality u]
  simp

lemma left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a : A) (Y : D) :
    (left_to_right_iso adj commF a).hom.app Y =
    (((shiftEquiv C a).symm.toAdjunction.comp adj).homEquiv (G.obj (Y⟦a⟧)) Y)
    ((CommShift.iso (-a)).hom.app (G.obj (Y⟦a⟧)) ≫
    ((adj.comp (shiftEquiv D a).symm.toAdjunction).homEquiv (G.obj (Y⟦a⟧)) Y).symm
    (𝟙 (G.obj (Y⟦a⟧)))) := by
  sorry

/- This causes universe problems (the LHS is in v₁ and the RHS in v₂).
lemma left_to_right_iso_hom_app_apply (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D) :
    (yoneda.map ((left_to_right_iso adj commF a).hom.app Y)).app (op X) =
    (((Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction).homEquiv X Y).symm.toIso ≪≫
    (yoneda.obj Y).mapIso ((commF.iso (-a)).app X).op ≪≫
    ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y).toIso).hom := by
  ext u
  simp [comp_left_to_right_iso_hom_app]
-/

noncomputable def right_to_left_iso (adj : F ⊣ G) (commG : CommShift G A) (a : A) :=
  (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
  (add_left_neg _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
  (add_left_neg _)).symm.toAdjunction adj)).toFun (commG.iso (-a))

noncomputable def left_to_right_iso_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    (F ⋙ (shiftEquiv' D (-a) a (neg_add_self a)).symm.functor).op ≅
      ((shiftEquiv' C (-a) a (neg_add_self a)).symm.functor ⋙ F).op :=
    (left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
    adj.opAdjointOpOfAdjoint commG.op a).symm

lemma zut (adj : F ⊣ G) (commG : CommShift G A) (a : A) (X : C) (Y : D) (u : F.obj (X⟦a⟧) ⟶ Y) :
    0 = 0 := by
  set G' : OppositeShift D A ⥤ OppositeShift C A := G.op
  set F' : OppositeShift C A ⥤ OppositeShift D A := F.op
  set commG' : CommShift G' A := commG.op
  set adj' : G' ⊣ F' := adj.opAdjointOpOfAdjoint
  have := comp_left_to_right_iso_hom_app (C := OppositeShift D A)
    (D := OppositeShift C A) (F := G') (G := F') adj' commG' a _ _ u.op
  rfl

lemma right_to_left_eq_left_to_right_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    right_to_left_iso adj commG a = NatIso.removeOp (left_to_right_iso_op adj commG a) := by
  set G' : OppositeShift D A ⥤ OppositeShift C A := G.op
  set F' : OppositeShift C A ⥤ OppositeShift D A := F.op
  set commG' : CommShift G' A := commG.op
  set adj' : G' ⊣ F' := adj.opAdjointOpOfAdjoint
  have := commG'
  ext X
  apply Functor.map_injective (yoneda (C := D))
  ext Y u
  simp at u
  conv_rhs => rw [yoneda_map_app, left_to_right_iso_op]
  have := comp_left_to_right_iso_hom_app (C := OppositeShift D A)
    (D := OppositeShift C A) (F := G') (G := F') adj' commG' a

lemma right_to_left_iso_apply (adj : F ⊣ G) (commG : CommShift G A) (a : A) (X : C) (Y : D) :
    (coyoneda.map (op ((right_to_left_iso adj commG a).hom.app X))).app Y = sorry := by
  simp
  have := ((Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj).homEquiv X Y)
  sorry


noncomputable def left_to_right (adj : F ⊣ G) (commF : CommShift F A) :
    CommShift G A where
  iso := left_to_right_iso adj commF
  zero := by
    ext Y
    rw [left_to_right_iso_hom_app]
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor,
      comp_homEquiv, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, Equiv.coe_trans, types_comp_apply,
      Equiv.symm_trans_apply, id_obj, map_comp,
      assoc, Quiver.Hom.unop_op, Function.comp_apply,
      CommShift.isoZero_hom_app, FunctorToTypes.comp]
    conv_lhs => erw [shiftEquiv_homEquiv_zero'_symm_app D (0 : A) rfl _ Y]
                erw [← homEquiv_naturality_right_symm]
    simp only [shiftEquiv'_functor, yoneda_obj_obj, shiftEquiv'_inverse, id_obj,
      shiftFunctorZero'_eq_shiftFunctorZero, map_comp, assoc,
      counit_naturality, comp_obj, yoneda_obj_map, Quiver.Hom.unop_op,
      Equivalence.toAdjunction_unit, yoneda_map_app]
    change ((shiftEquiv C (0 : A)).symm.toAdjunction.homEquiv _ (G.obj Y))
      ((adj.homEquiv ((shiftFunctor C (-0)).obj _) Y)
      ((F.commShiftIso (-0)).hom.app _ ≫ _)) = _
    rw [F.commShiftIso_zero' (-0 : A) (by simp)]
    simp only [CommShift.isoZero'_hom_app, map_comp, assoc]
    rw [← assoc ((shiftFunctorZero' D (-0 : A) (by simp)).inv.app _),
      Iso.inv_hom_id_app, id_comp, ← homEquiv_naturality_left_symm, Equiv.apply_symm_apply,
      shiftEquiv_homEquiv_zero]
    simp
/-    apply Functor.map_injective (yoneda (C := C))
    ext X u
    rw [yoneda_map_app, yoneda_map_app, comp_left_to_right_iso_hom_app]
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor,
      comp_homEquiv, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, Equiv.coe_trans, types_comp_apply,
      Equiv.symm_trans_apply, id_obj, map_comp,
      assoc, Quiver.Hom.unop_op, Function.comp_apply,
      CommShift.isoZero_hom_app, FunctorToTypes.comp]
    conv_lhs => erw [shiftEquiv_homEquiv_zero'_symm_app D (0 : A) rfl (F.obj (unop X)) Y]
                erw [← homEquiv_naturality_right_symm]
    simp only [shiftEquiv'_functor, yoneda_obj_obj, shiftEquiv'_inverse, id_obj,
      shiftFunctorZero'_eq_shiftFunctorZero, map_comp, assoc,
      counit_naturality, comp_obj, yoneda_obj_map, Quiver.Hom.unop_op,
      Equivalence.toAdjunction_unit, yoneda_map_app]
    change ((shiftEquiv C (0 : A)).symm.toAdjunction.homEquiv (unop X) (G.obj Y))
      ((adj.homEquiv ((shiftFunctor C (-0)).obj (unop X)) Y)
      ((F.commShiftIso (-0)).hom.app (unop X) ≫ _)) = _
    rw [F.commShiftIso_zero' (-0 : A) (by simp)]
    simp only [CommShift.isoZero'_hom_app, map_comp, assoc]
    rw [← assoc ((shiftFunctorZero' D (-0 : A) (by simp)).inv.app (F.obj (unop X))),
      Iso.inv_hom_id_app, id_comp, ← homEquiv_naturality_left_symm, Equiv.apply_symm_apply,
      shiftEquiv_homEquiv_zero]
    simp-/
  add a b := by
    have hadd : -b + -a = -(a + b) := by simp
    ext Y
    conv_lhs => rw [left_to_right_iso_hom_app]
    have := F.commShiftIso_add' hadd
    simp [Functor.commShiftIso] at this
    rw [this, CommShift.isoAdd']
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
      shiftEquiv'_inverse, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      NatTrans.comp_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, associator_inv_app,
      id_comp, Equiv.symm_trans_apply, map_id, assoc, Equiv.trans_apply, map_comp,
      unit_naturality_assoc, CommShift.isoAdd_hom_app]
    have heq : ∀ (u : (G.obj (Y⟦a + b⟧))⟦- (a + b)⟧ ⟶ G.obj Y),
        (shiftEquiv C (a + b)).symm.toAdjunction.homEquiv (G.obj (Y⟦a + b⟧)) (G.obj Y) u =
        ((shiftEquiv' C b (-b) sorry).symm.toAdjunction.homEquiv _ ((shiftFunctor C a).obj (G.obj Y)))
      (((shiftEquiv' C a (-a) sorry).symm.toAdjunction.homEquiv
      ((shiftFunctor C (-b)).obj _) (G.obj Y)) ((shiftFunctorAdd' C (-b) (-a) (-(a + b))
      hadd).inv.app _ ≫ u)) ≫
      (shiftFunctorAdd C a b).inv.app (G.obj Y) := sorry
    erw [heq]
    conv_rhs => rw [← assoc, ← assoc]
    congr 1
    rw [adj.homEquiv_naturality_left, Iso.inv_hom_id_app_assoc]

/-    have heq' : ∀ (X : D) (u : X ⟶ Y⟦a + b⟧),
        ((shiftEquiv D (a + b)).symm.toAdjunction.homEquiv _ _).symm u =
        ((shiftEquiv D a).symm.toAdjunction.homEquiv _ _)
        ((shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app X) ≫ sorry
         := sorry-/

/-
((shiftEquiv' C b b' hb).symm.toAdjunction.homEquiv X
        ((shiftFunctor C a).obj Y)).symm (u ≫ (shiftFunctorAdd' C a b c h).hom.app Y) =
        ((shiftEquiv' C a a' ha).symm.toAdjunction.homEquiv (X⟦b'⟧) Y)
        ((shiftFunctorAdd' C b' a' c' (by rw [eq_neg_of_add_eq_zero_right hc,
        eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h,
        neg_add_rev])).inv.app X ≫
        ((shiftEquiv' C c c' hc).symm.toAdjunction.homEquiv X Y).symm u)
-/

  #exit
    conv_rhs => rw [CommShift.isoAdd_hom_app, ← assoc, ← assoc]
                rw [left_to_right_iso_hom_app, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    simp only [Equivalence.symm_inverse, comp_obj,
      Equivalence.symm_functor, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, assoc, types_comp_apply,
      Quiver.Hom.unop_op]



    have : 𝟙 (G.obj ((shiftFunctor D b).obj ((shiftFunctor D a).obj Y))) =
        𝟙 _ ≫ G.map (𝟙 _) := sorry
    rw [this]
    conv_rhs => rw [adj.homEquiv_naturality_right_symm]
    have heq : ∀ (X : C) (u : F.obj X ⟶ Y⟦a + b⟧),
        ((shiftEquiv D b).symm.toAdjunction.homEquiv (F.obj X)
        ((shiftFunctor D a).obj Y)).symm (u ≫ (shiftFunctorAdd D a b).hom.app Y) =
        ((shiftEquiv D a).symm.toAdjunction.homEquiv ((F.obj X)⟦-b⟧) Y)
        ((shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app (F.obj X) ≫
        ((shiftEquiv D (a + b)).symm.toAdjunction.homEquiv (F.obj X) Y).symm u) := by
      intro X u
      rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
      erw [shiftEquiv_add_symm_homEquiv D a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg _)
        (add_right_neg _) (add_right_neg _) rfl (F.obj X) Y u]
    erw [heq]
    erw [← (shiftEquiv D a).symm.toAdjunction.homEquiv_naturality_left]
    simp only [shiftEquiv'_functor, shiftEquiv'_inverse,
      Equivalence.symm_functor, Equivalence.symm_inverse, comp_obj, map_comp, assoc]
    rw [← assoc]
    erw [← (shiftEquiv C b).symm.toAdjunction.homEquiv_naturality_right]
    conv_rhs => rw [comp_left_to_right_iso_hom_app,
                  Adjunction.comp_homEquiv adj (shiftEquiv D a).symm.toAdjunction]
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse,
      Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, map_comp,
      Equiv.symm_trans_apply, assoc, counit_naturality, id_obj, counit_naturality_assoc,
      left_triangle_components_assoc]
    erw [(adj.homEquiv ((shiftFunctor C (-b)).obj (unop X))
      ((shiftFunctor D a).obj Y)).symm_apply_apply]
    erw [((shiftEquiv D a).symm.toAdjunction.homEquiv
      (F.obj ((shiftFunctor C (-b)).obj (unop X))) Y).symm_apply_apply]
    rw [Adjunction.comp_homEquiv]
    simp only [Equivalence.toAdjunction_counit,
      Equiv.trans_apply, comp_obj, map_comp, Equivalence.toAdjunction_unit, assoc]
    have heq' : ∀ (u : ((unop X)⟦-b⟧)⟦-a⟧ ⟶ G.obj Y),
        ((shiftEquiv C b).symm.toAdjunction.homEquiv (unop X) ((shiftFunctor C a).obj (G.obj Y)))
        (((shiftEquiv C a).symm.toAdjunction.homEquiv
        ((shiftFunctor C (-b)).obj (unop X)) (G.obj Y)) u) ≫
        (shiftFunctorAdd C a b).inv.app (G.obj Y) =
        ((shiftEquiv C (a + b)).symm.toAdjunction.homEquiv (unop X) (G.obj Y))
        ((shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).hom.app (unop X) ≫ u) := by
      intro u
      rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
      erw [shiftEquiv'_add_symm_homEquiv C a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg _)
        (add_right_neg _) (add_right_neg _) rfl (unop X) (G.obj Y) u]
    erw [heq']
    erw [← adj.homEquiv_naturality_left]
    have : ∀ (u : (F.obj (unop X))⟦-(a + b)⟧ ⟶ Y),
        F.map ((shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).hom.app (unop X)) ≫
        (CommShift.iso (-a)).hom.app ((shiftFunctor C (-b)).obj (unop X)) ≫
        (shiftFunctor D (-a)).map ((CommShift.iso (-b)).hom.app (unop X)) ≫
        (shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app (F.obj (unop X)) ≫ u =
        (F.commShiftIso (-(a + b))).hom.app (unop X) ≫ u := by
      intro u
      rw [F.commShiftIso_add' hadd]
      simp [CommShift.isoAdd']; rfl
    rw [this]
    rw [yoneda_map_app, comp_left_to_right_iso_hom_app]
    simp [Adjunction.comp_homEquiv, Functor.commShiftIso]
  /-  apply Functor.map_injective (yoneda (C := C))
    ext X u
    conv_rhs => rw [yoneda_map_app, CommShift.isoAdd_hom_app, ← assoc, ← assoc, ← assoc]
                rw [comp_left_to_right_iso_hom_app, Adjunction.comp_homEquiv]
    simp only [Equivalence.symm_inverse, comp_obj,
      Equivalence.symm_functor, Iso.trans_hom, Equiv.toIso_hom,
      mapIso_hom, Iso.op_hom, Iso.app_hom, assoc, types_comp_apply, yoneda_obj_map,
      Quiver.Hom.unop_op]
    rw [Adjunction.comp_homEquiv]
    simp only [shiftEquiv'_functor, shiftEquiv'_inverse,
      Equiv.symm_trans_apply, map_comp, assoc, counit_naturality, comp_obj,
      id_obj, Equiv.trans_apply]
    conv_rhs => rw [adj.homEquiv_naturality_right_symm]
    have heq : ∀ (u : F.obj (unop X) ⟶ Y⟦a + b⟧),
        ((shiftEquiv D b).symm.toAdjunction.homEquiv (F.obj (unop X))
        ((shiftFunctor D a).obj Y)).symm (u ≫ (shiftFunctorAdd D a b).hom.app Y) =
        ((shiftEquiv D a).symm.toAdjunction.homEquiv ((F.obj (unop X))⟦-b⟧) Y)
        ((shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app (F.obj (unop X)) ≫
        ((shiftEquiv D (a + b)).symm.toAdjunction.homEquiv (F.obj (unop X)) Y).symm u) := by
      intro u
      rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
      erw [shiftEquiv_add_symm_homEquiv D a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg _)
        (add_right_neg _) (add_right_neg _) rfl (F.obj (unop X)) Y u]
    erw [heq]
    erw [← (shiftEquiv D a).symm.toAdjunction.homEquiv_naturality_left]
    simp only [shiftEquiv'_functor, shiftEquiv'_inverse,
      Equivalence.symm_functor, Equivalence.symm_inverse, comp_obj, map_comp, assoc]
    rw [← assoc]
    erw [← (shiftEquiv C b).symm.toAdjunction.homEquiv_naturality_right]
    conv_rhs => rw [comp_left_to_right_iso_hom_app,
                  Adjunction.comp_homEquiv adj (shiftEquiv D a).symm.toAdjunction]
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse,
      Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, map_comp,
      Equiv.symm_trans_apply, assoc, counit_naturality, id_obj, counit_naturality_assoc,
      left_triangle_components_assoc]
    erw [(adj.homEquiv ((shiftFunctor C (-b)).obj (unop X))
      ((shiftFunctor D a).obj Y)).symm_apply_apply]
    erw [((shiftEquiv D a).symm.toAdjunction.homEquiv
      (F.obj ((shiftFunctor C (-b)).obj (unop X))) Y).symm_apply_apply]
    rw [Adjunction.comp_homEquiv]
    simp only [Equivalence.toAdjunction_counit,
      Equiv.trans_apply, comp_obj, map_comp, Equivalence.toAdjunction_unit, assoc]
    have heq' : ∀ (u : ((unop X)⟦-b⟧)⟦-a⟧ ⟶ G.obj Y),
        ((shiftEquiv C b).symm.toAdjunction.homEquiv (unop X) ((shiftFunctor C a).obj (G.obj Y)))
        (((shiftEquiv C a).symm.toAdjunction.homEquiv
        ((shiftFunctor C (-b)).obj (unop X)) (G.obj Y)) u) ≫
        (shiftFunctorAdd C a b).inv.app (G.obj Y) =
        ((shiftEquiv C (a + b)).symm.toAdjunction.homEquiv (unop X) (G.obj Y))
        ((shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).hom.app (unop X) ≫ u) := by
      intro u
      rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
      erw [shiftEquiv'_add_symm_homEquiv C a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg _)
        (add_right_neg _) (add_right_neg _) rfl (unop X) (G.obj Y) u]
    erw [heq']
    erw [← adj.homEquiv_naturality_left]
    have : ∀ (u : (F.obj (unop X))⟦-(a + b)⟧ ⟶ Y),
        F.map ((shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).hom.app (unop X)) ≫
        (CommShift.iso (-a)).hom.app ((shiftFunctor C (-b)).obj (unop X)) ≫
        (shiftFunctor D (-a)).map ((CommShift.iso (-b)).hom.app (unop X)) ≫
        (shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app (F.obj (unop X)) ≫ u =
        (F.commShiftIso (-(a + b))).hom.app (unop X) ≫ u := by
      intro u
      rw [F.commShiftIso_add' hadd]
      simp [CommShift.isoAdd']; rfl
    rw [this]
    rw [yoneda_map_app, comp_left_to_right_iso_hom_app]
    simp [Adjunction.comp_homEquiv, Functor.commShiftIso]-/

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
