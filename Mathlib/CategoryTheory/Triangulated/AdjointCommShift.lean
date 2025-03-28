import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Triangulated.Lemmas
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Shift.Pullback

namespace CategoryTheory

open Category Functor CategoryTheory Opposite

namespace Adjunction

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} {D : Type u₂} [Category.{v₁,u₁} C] [Category.{v₂,u₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {A : Type u} [AddGroup A]
  [HasShift C A] [HasShift D A]

namespace CommShift

noncomputable def left_to_right_iso (adj : F ⊣ G) (commF : CommShift F A) (a : A) :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction)
  (Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj)).toFun (commF.iso (-a))

lemma left_to_right_iso_eq (adj : F ⊣ G) (commF : CommShift F A) (a a' : A) (h : a + a' = 0) :
    left_to_right_iso adj commF a =
    (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a a' h).symm.toAdjunction)
    (Adjunction.comp (shiftEquiv' C a a' h).symm.toAdjunction adj)).toFun (commF.iso a') := by
  have h' : a' = -a := eq_neg_of_add_eq_zero_right h
  ext Y
  simp [left_to_right_iso]
  conv_lhs => rw [shiftEquiv'_symm_counit, shiftFunctorCompIsoId]
  conv_rhs => rw [shiftEquiv'_symm_counit, shiftFunctorCompIsoId]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj, id_obj, map_comp]
  have := shiftFunctorAdd'_symm_eqToIso (C := D) a a' 0 a (-a) 0 h (by simp) rfl h'
  apply_fun (fun e ↦ e.hom.app) at this
  simp only [comp_obj, Iso.symm_hom, eqToIso_refl, Iso.trans_refl, Iso.trans_hom, eqToIso.hom]
    at this
  rw [this]
  simp only [NatTrans.comp_app, comp_obj, eqToHom_app, map_comp, assoc]
  rw [eqToHom_map, eqToHom_map]
  slice_rhs 4 5 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map
    (G.map ((shiftFunctor D i).map (adj.counit.app ((shiftFunctor D a).obj Y))))) (w := h')]
  slice_rhs 3 4 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map
    (G.map ((commF.iso i).hom.app (G.obj ((shiftFunctor D a).obj Y))))) (w := h')]
  slice_rhs 2 3 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map (adj.unit.app
    ((shiftFunctor C i).obj (G.obj ((shiftFunctor D a).obj Y))))) (w := h')]
  conv_lhs => rw [shiftEquiv'_symm_unit, shiftFunctorCompIsoId]
  conv_rhs => rw [shiftEquiv'_symm_unit, shiftFunctorCompIsoId]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, id_obj, comp_obj, assoc,
    NatIso.cancel_natIso_inv_left]
  have := shiftFunctorAdd'_eqToIso (C := C) a' a 0 (-a) a 0 (by simp only [h', neg_add_cancel])
    (by simp) h' rfl
  apply_fun (fun e ↦ e.hom.app) at this
  simp only [comp_obj, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, eqToIso.hom] at this
  rw [this]
  simp only [NatTrans.comp_app, comp_obj, eqToHom_app, assoc, eqToHom_trans_assoc, eqToHom_refl,
    id_comp]

/-- Doc string, why the prime?-/
lemma comp_left_to_right_iso_hom_app' (adj : F ⊣ G) (commF : CommShift F A) (a a' : A)
    (h : a + a' = 0) (X : C) (Y : D) (u : X ⟶ G.obj (Y⟦a⟧)) :
    u ≫ (left_to_right_iso adj commF a).hom.app Y =
    ((shiftEquiv' C a a' h).symm.toAdjunction.homEquiv X (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C a').obj X) Y) ((CommShift.iso a').hom.app X ≫
    ((shiftEquiv' D a a' h).symm.toAdjunction.homEquiv (F.obj X) Y).symm
    ((adj.homEquiv X ((shiftFunctor D a).obj Y)).symm u))) := by
  rw [left_to_right_iso_eq adj commF a a' h]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
    shiftEquiv'_inverse, Equiv.toFun_as_coe, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    comp_unit_app, id_obj, Equivalence.toAdjunction_unit, Functor.comp_map, comp_counit_app,
    Equivalence.toAdjunction_counit, map_comp, assoc, homEquiv_symm_apply, homEquiv_apply]
  slice_lhs 1 2 => erw [(shiftEquiv' C a a' h).symm.unit.naturality u]
  simp only [id_obj, Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, comp_obj, Functor.comp_map, assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp]; erw [adj.unit.naturality]
  slice_rhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [← (CommShift.iso a').hom.naturality u]
  simp only [assoc, Functor.map_comp]
  rfl

lemma comp_left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a : A) (X : C) (Y : D)
    (u : X ⟶ G.obj (Y⟦a⟧)) :
    u ≫ (left_to_right_iso adj commF a).hom.app Y =
    ((shiftEquiv C a).symm.toAdjunction.homEquiv X (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C (-a)).obj X) Y) ((CommShift.iso (-a)).hom.app X ≫
    ((shiftEquiv D a).symm.toAdjunction.homEquiv (F.obj X) Y).symm
    ((adj.homEquiv X ((shiftFunctor D a).obj Y)).symm u))) := by
  rw [comp_left_to_right_iso_hom_app']

lemma left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a : A) (Y : D) :
    (left_to_right_iso adj commF a).hom.app Y =
    ((shiftEquiv C a).symm.toAdjunction.homEquiv _ (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C (-a)).obj _) Y) ((CommShift.iso (-a)).hom.app _ ≫
    ((shiftEquiv D a).symm.toAdjunction.homEquiv (F.obj _) Y).symm
    ((adj.homEquiv _ ((shiftFunctor D a).obj Y)).symm (𝟙 (G.obj (Y⟦a⟧)))))) := by
  conv_lhs => rw [← id_comp ((left_to_right_iso adj commF a).hom.app Y)]
  rw [comp_left_to_right_iso_hom_app]
  simp

noncomputable def right_to_left_iso (adj : F ⊣ G) (commG : CommShift G A) (a : A) :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
  (neg_add_cancel _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
  (neg_add_cancel _)).symm.toAdjunction adj)).invFun (commG.iso (-a))

noncomputable def left_to_right_iso_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    (F ⋙ (shiftEquiv' D (-a) a (neg_add_cancel a)).symm.functor).op ≅
      ((shiftEquiv' C (-a) a (neg_add_cancel a)).symm.functor ⋙ F).op :=
    (left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
    adj.opAdjointOpOfAdjoint commG.op a).symm

lemma right_to_left_eq_left_to_right_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    right_to_left_iso adj commG a = NatIso.removeOp (left_to_right_iso_op adj commG a) := by
  set G' : OppositeShift D A ⥤ OppositeShift C A := G.op
  set F' : OppositeShift C A ⥤ OppositeShift D A := F.op
  set commG' : CommShift G' A := commG.op
  set adj' : G' ⊣ F' := adj.opAdjointOpOfAdjoint
  have := commG'
  dsimp [left_to_right_iso_op, left_to_right_iso, right_to_left_iso]
  rw [← natIsoEquiv_compat_op _ _ _ _ (adj.comp (shiftEquiv' D (-a) a (by simp)).symm.toAdjunction)
    ((shiftEquiv' C (-a) a (by simp)).symm.toAdjunction.comp adj)]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
    shiftEquiv'_inverse, Functor_iso_to_iso_op, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk]
  congr 1
  rw [Adjunction.comp_op, Adjunction.comp_op]
  change _ = conjugateIsoEquiv _ _ _
  erw [shiftEquiv'_symm_toAdjunction_op, shiftEquiv'_symm_toAdjunction_op]
  rfl

lemma right_to_left_iso_eq (adj : F ⊣ G) (commG : CommShift G A) (a a' : A) (h : a + a' = 0) :
    right_to_left_iso adj commG a = (conjugateIsoEquiv (Adjunction.comp adj
    (shiftEquiv' D a' a (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction)
    (Adjunction.comp (shiftEquiv' C a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction adj)).invFun (commG.iso a') := by
  rw [right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_eq _ _ a a' h]
  ext X
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
    shiftEquiv'_functor, Equiv.toFun_as_coe, NatIso.removeOp_hom, Iso.symm_hom,
    conjugateIsoEquiv_apply_inv, NatTrans.removeOp_app, op_obj, conjugateEquiv_apply_app,
    comp_unit_app, id_obj, opAdjointOpOfAdjoint_unit_app, Equivalence.toAdjunction_unit, op_map,
    Functor.comp_map, comp_counit_app, Equivalence.toAdjunction_counit,
    opAdjointOpOfAdjoint_counit_app, map_comp, assoc, Equiv.invFun_as_coe,
    conjugateIsoEquiv_symm_apply_hom, conjugateEquiv_symm_apply_app]
  rw [opEquiv_apply, opEquiv_apply, opEquiv_symm_apply, opEquiv_symm_apply,
    unop_comp, unop_comp, unop_comp, unop_comp]
  simp only [unop_id, map_id, comp_id, map_comp, op_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    id_comp]
  rw [shiftEquiv'_symm_counit, shiftEquiv'_symm_unit]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj,
    id_obj, Iso.trans_inv, Iso.symm_inv]
  rw [oppositeShiftFunctorAdd'_inv_app, oppositeShiftFunctorZero_hom_app]
  simp only [comp_obj, id_obj]
  rw [shiftEquiv'_symm_unit]
  simp only [shiftFunctorCompIsoId, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, id_obj,
    comp_obj, map_comp, assoc]
  rw [oppositeShiftFunctorAdd'_hom_app, oppositeShiftFunctorZero_inv_app]
  simp only [id_obj, comp_obj]
  have : F.map ((shiftFunctor (OppositeShift C A) a).map (adj.unit.app X).op).unop =
    F.map ((shiftFunctor C a).map (adj.unit.app X)) := rfl
  rw [this]
  congr 1
  have : F.map ((shiftFunctor (OppositeShift C A) a).map (G.map
              (((shiftFunctorAdd' D a a' 0 h).hom.app (F.obj X)).op ≫
                  ((shiftFunctorZero D A).inv.app (F.obj X)).op).unop).op).unop =
    F.map ((shiftFunctor C a).map (G.map ((shiftFunctorZero D A).inv.app (F.obj X)))) ≫
    F.map ((shiftFunctor C a).map (G.map ((shiftFunctorAdd' D a a' 0 h).hom.app (F.obj X)))) := by
    conv_lhs => rw [← op_comp, Quiver.Hom.unop_op]
                rw [map_comp, op_comp, map_comp, unop_comp]
                erw [Quiver.Hom.unop_op, Quiver.Hom.unop_op]
    simp only [id_obj, comp_obj, map_comp]
    rfl
  rw [this]
  simp only [id_obj, comp_obj, assoc]
  rfl

/-- Doc string, why the prime?-/
lemma comp_right_to_left_iso_hom_app' (adj : F ⊣ G) (commG : CommShift G A) (a a' : A)
    (h : a + a' = 0) (X : C) (Y : D) (v : (F.obj X)⟦a⟧ ⟶ Y) :
    (right_to_left_iso adj commG a).hom.app X ≫ v = (adj.homEquiv _ _).symm
    (((shiftEquiv' C a' a (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction.homEquiv
    _ _).symm (((adj.homEquiv X _) (((shiftEquiv' D a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction.homEquiv _ _) v)) ≫
    (commG.iso a').hom.app _)) := by
  rw [right_to_left_iso_eq _ _ a a' h]
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
    shiftEquiv'_functor, Equiv.invFun_as_coe, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_symm_apply_app, comp_unit_app, id_obj, Equivalence.toAdjunction_unit,
    Functor.comp_map, map_comp, comp_counit_app, Equivalence.toAdjunction_counit, assoc,
    homEquiv_apply, homEquiv_symm_apply]
  slice_lhs 5 6 => erw [← adj.counit.naturality]
  slice_lhs 4 5 => erw [← Functor.map_comp]
                   erw [← (shiftEquiv' C a' a
                     (by simp [eq_neg_of_add_eq_zero_left h])).symm.counit.naturality]
                   rw [Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp]; erw [← Functor.map_comp]
                   erw [← (commG.iso a').hom.naturality]
                   rw [Functor.map_comp, Functor.map_comp]
  simp only [assoc]
  rfl

lemma left_to_right_iso_zero (adj : F ⊣ G) (commF : CommShift F A) :
    left_to_right_iso adj commF 0 = CommShift.isoZero G A := by
  ext Y
  rw [left_to_right_iso_hom_app]
  conv_lhs => erw [shiftEquiv_homEquiv_zero'_symm_app D (0 : A) rfl _ Y]
              erw [← homEquiv_naturality_right_symm]
  simp only [id_obj, shiftFunctorZero'_eq_shiftFunctorZero, id_comp, counit_naturality,
      comp_obj, map_comp]
  change ((shiftEquiv C (0 : A)).symm.toAdjunction.homEquiv _ (G.obj Y))
    ((adj.homEquiv ((shiftFunctor C (-0)).obj _) Y) ((F.commShiftIso (-0)).hom.app _ ≫ _)) = _
  rw [F.commShiftIso_zero' (-0 : A) (by simp)]
  simp only [CommShift.isoZero'_hom_app, map_comp, assoc]
  rw [← assoc ((shiftFunctorZero' D (-0 : A) (by simp)).inv.app _),
      Iso.inv_hom_id_app, id_comp, ← homEquiv_naturality_left_symm, Equiv.apply_symm_apply,
      shiftEquiv_homEquiv_zero]
  simp

lemma left_to_right_iso_add (adj : F ⊣ G) (commF : CommShift F A) (a b : A) :
    left_to_right_iso adj commF (a + b) = CommShift.isoAdd (left_to_right_iso adj commF a)
    (left_to_right_iso adj commF b) := by
  have hadd : -b + -a = -(a + b) := by simp
  ext Y
  conv_lhs => rw [left_to_right_iso_hom_app]
  have := F.commShiftIso_add' hadd
  simp [Functor.commShiftIso] at this
  rw [this, CommShift.isoAdd']
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
      shiftEquiv'_inverse, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      NatTrans.comp_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, associator_inv_app,
      id_comp, map_id, assoc, map_comp, unit_naturality_assoc, CommShift.isoAdd_hom_app]
  have heq : ∀ (u : (G.obj (Y⟦a + b⟧))⟦- (a + b)⟧ ⟶ G.obj Y),
        (shiftEquiv C (a + b)).symm.toAdjunction.homEquiv (G.obj (Y⟦a + b⟧)) (G.obj Y) u =
        ((shiftEquiv C b).symm.toAdjunction.homEquiv _ ((shiftFunctor C a).obj (G.obj Y)))
        (((shiftEquiv C a).symm.toAdjunction.homEquiv
        ((shiftFunctor C (-b)).obj _) (G.obj Y)) ((shiftFunctorAdd' C (-b) (-a) (-(a + b))
        hadd).inv.app _ ≫ u)) ≫
        (shiftFunctorAdd C a b).inv.app (G.obj Y) := by
    intro u
    dsimp only [shiftEquiv]
    have : u = (shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).hom.app _ ≫
          ((shiftFunctorAdd' C (-b) (-a) (-(a + b)) hadd).inv.app (G.obj ((shiftFunctor D
          (a + b)).obj Y)) ≫ u) := by simp
    conv_lhs => rw [this]
    erw [← shiftEquiv'_add_symm_homEquiv C a (-a) b (-b) (a + b) (-(a + b)) (add_neg_cancel a)
        (add_neg_cancel b) (add_neg_cancel (a + b)) rfl]
    simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
        shiftEquiv'_inverse, comp_obj, homEquiv_apply, Equivalence.toAdjunction_unit, map_comp,
        assoc, NatIso.cancel_natIso_hom_left]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  erw [heq]
  conv_rhs => rw [← assoc, ← assoc]
  congr 1
  rw [adj.homEquiv_naturality_left, Iso.inv_hom_id_app_assoc]
  have heq' : ∀ (X : D) (u : X ⟶ Y⟦a + b⟧),
        (shiftFunctorAdd' D (-b) (-a) (-(a + b)) hadd).inv.app X ≫
        ((shiftEquiv D (a + b)).symm.toAdjunction.homEquiv X Y).symm u =
        ((shiftEquiv D a).symm.toAdjunction.homEquiv _ _).symm
        (((shiftEquiv D b).symm.toAdjunction.homEquiv _ _).symm
        (u ≫ (shiftFunctorAdd D a b).hom.app Y)) := by
    intro X u
    erw [← shiftEquiv_add_symm_homEquiv D a (-a) b (-b) (a + b) (-(a + b)) (add_neg_cancel a)
        (add_neg_cancel b) (add_neg_cancel (a + b)) rfl]
    simp [shiftFunctorAdd'_eq_shiftFunctorAdd]
  erw [heq']
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
      shiftEquiv'_inverse]
  erw [← (shiftEquiv D a).symm.toAdjunction.homEquiv_naturality_left_symm]
  conv_rhs => rw [comp_left_to_right_iso_hom_app]
              erw [← (shiftEquiv C b).symm.toAdjunction.homEquiv_naturality_right]
              rw [comp_left_to_right_iso_hom_app]
  simp [homEquiv_apply, homEquiv_symm_apply]

noncomputable def left_to_right (adj : F ⊣ G) (commF : CommShift F A) :
    CommShift G A where
  iso := left_to_right_iso adj commF
  zero := left_to_right_iso_zero adj commF
  add a b := left_to_right_iso_add adj commF a b

noncomputable def right_to_left (adj : F ⊣ G) (commG : CommShift G A) :
    CommShift F A where
  iso := right_to_left_iso adj commG
  zero := by
    rw [right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_zero]
    ext Y
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
      shiftEquiv'_functor, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoZero_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    simp
  add a b := by
    rw [right_to_left_eq_left_to_right_op, right_to_left_eq_left_to_right_op,
      right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_op,
      left_to_right_iso_op, left_to_right_iso_add]
    ext Y
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
      shiftEquiv'_functor, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoAdd_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, assoc,
      CommShift.isoAdd_hom_app]
    have : ((left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
        (opAdjointOpOfAdjoint G F adj) (CommShift.op G A commG) b).inv.app
        ((shiftFunctor (OppositeShift C A) a).obj (op Y))) =
        ((left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
        (opAdjointOpOfAdjoint G F adj) (CommShift.op G A commG) b).inv.app (op (Y⟦a⟧))) := rfl
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    erw [this]
    simp only [comp_obj, Quiver.Hom.unop_op, Equivalence.symm_inverse, shiftEquiv'_functor]
    rfl

abbrev commShift_left_right_compat (adj : F ⊣ G) (commF : CommShift F A) (commG : CommShift G A)
    (a a' : A) (ha : a + a' = 0) (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) :=
  ((shiftEquiv' C a a' ha).symm.toAdjunction.comp adj).homEquiv _ _ ((commF.iso a').hom.app X ≫ u)
  = (((adj.comp (shiftEquiv' D a a' ha).symm.toAdjunction).homEquiv _ _) u) ≫
  (commG.iso a).hom.app Y

lemma left_to_right_compat (adj : F ⊣ G) (commF : CommShift F A) (a a' : A) (h : a + a' = 0)
    (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) : commShift_left_right_compat adj commF
    (left_to_right adj commF) a a' h X Y u := by
  dsimp [commShift_left_right_compat, left_to_right]
  rw [comp_left_to_right_iso_hom_app' adj commF a a' h, comp_homEquiv, comp_homEquiv]
  simp only [Equiv.trans_apply, comp_obj, map_comp, Equivalence.symm_functor, shiftEquiv'_inverse,
    Equivalence.symm_inverse, shiftEquiv'_functor, assoc, counit_naturality, id_obj,
    counit_naturality_assoc, left_triangle_components_assoc]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma right_to_left_compat (adj : F ⊣ G) (commG : CommShift G A) (a a' : A) (h : a + a' = 0)
    (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) : commShift_left_right_compat adj
    (right_to_left adj commG) commG a a' h X Y u := by
  dsimp [commShift_left_right_compat, right_to_left]
  rw [comp_right_to_left_iso_hom_app' adj commG a' a (by simp [eq_neg_of_add_eq_zero_left h]),
    comp_homEquiv, comp_homEquiv]
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, comp_obj, map_comp, assoc, Equiv.trans_apply, unit_naturality_assoc,
    right_triangle_components, comp_id]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

noncomputable def left_right_equiv (adj : F ⊣ G) : CommShift F A ≃ CommShift G A where
  toFun := left_to_right adj
  invFun := right_to_left adj
  left_inv commF := by
    ext a X
    have := left_to_right_compat adj commF (-a) a (by simp) X ((F.obj X)⟦a⟧) (𝟙 _)
    dsimp [commShift_left_right_compat] at this; erw [comp_id] at this
    rw [← Equiv.eq_symm_apply] at this
    rw [this]
    have := right_to_left_compat adj (left_to_right adj commF) (-a) a (by simp) X
      ((F.obj X)⟦a⟧) (𝟙 _)
    dsimp [commShift_left_right_compat] at this; erw [comp_id] at this
    rw [← Equiv.eq_symm_apply] at this
    exact this
  right_inv commG := by
    ext a Y
    set u := ((adj.comp (shiftEquiv' D a (-a) (by simp)).symm.toAdjunction).homEquiv _ _).symm
      (𝟙 (G.obj (Y⟦a⟧)))
    have := right_to_left_compat adj commG a (-a) (by simp) (G.obj (Y⟦a⟧)) Y u
    dsimp [commShift_left_right_compat, u] at this; erw [Equiv.apply_symm_apply] at this
    rw [id_comp] at this
    rw [← this]
    have := left_to_right_compat adj (right_to_left adj commG) a (-a) (by simp) (G.obj (Y⟦a⟧)) Y u
    dsimp [commShift_left_right_compat, u] at this; erw [Equiv.apply_symm_apply] at this
    rw [id_comp] at this
    exact this.symm

variable (A)

class adjunction_compat (adj : F ⊣ G) [CommShift F A] [CommShift G A] where
  left_right_compat : ∀ (a a' : A) (h : a + a' = 0) (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y),
    ((shiftEquiv' C a a' h).symm.toAdjunction.comp adj).homEquiv _ _
    ((CommShift.iso a').hom.app X ≫ u) =
    (((adj.comp (shiftEquiv' D a a' h).symm.toAdjunction).homEquiv _ _) u) ≫
    (CommShift.iso a).hom.app Y

variable {A}

-- Do we need `A` to be a group for the compatibility stuff?
-- Yes for some lemmas, maybe not for the definitions.
lemma adjunction_compat.right_left_compat (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [CommShift.adjunction_compat A adj]
    (a a' : A) (h : a + a' = 0) (X : C) (Y : D) (v : X ⟶ (G.obj Y)⟦a⟧) :
    (CommShift.iso a').inv.app X ≫
    (((shiftEquiv' C a a' h).symm.toAdjunction.comp adj).homEquiv _ _).symm v =
    ((adj.comp (shiftEquiv' D a a' h).symm.toAdjunction).homEquiv _ _).symm
    (v ≫ (CommShift.iso a).inv.app Y) := by
  have := adjunction_compat.left_right_compat (adj := adj) a a' h _ _ ((CommShift.iso a').inv.app X
    ≫ (((shiftEquiv' C a a' h).symm.toAdjunction.comp adj).homEquiv _ _).symm v)
  conv_lhs at this => rw [← assoc, Iso.hom_inv_id_app]; erw [id_comp]
                      rw [Equiv.apply_symm_apply]
  apply_fun (fun h ↦ h ≫ (CommShift.iso a).inv.app Y) at this
  conv_rhs at this => rw [assoc, Iso.hom_inv_id_app]; erw [comp_id]
  conv_rhs => rw [this, Equiv.symm_apply_apply]

variable (A)

def adjunction_compat_op (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [CommShift.adjunction_compat A adj] :
    @CommShift.adjunction_compat (OppositeShift D A) (OppositeShift C A) _ _ G.op F.op A _ _ _
    adj.opAdjointOpOfAdjoint (CommShift.op G A inferInstance) (CommShift.op F A inferInstance) := by
  refine @CommShift.adjunction_compat.mk (OppositeShift D A) (OppositeShift C A) _ _ G.op F.op A _ _
    _ adj.opAdjointOpOfAdjoint (CommShift.op G A inferInstance) (CommShift.op F A inferInstance) ?_
  intro a a' h Y X u
  have := adjunction_compat.right_left_compat adj a' a (by simp [eq_neg_of_add_eq_zero_left h])
    X.unop Y.unop u.unop
  rw [homEquiv_symm_apply, homEquiv_symm_apply] at this
  simp only [comp_obj, Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, op_obj, Functor.comp_map, comp_counit_app, id_obj,
    Equivalence.toAdjunction_counit, shiftEquiv'_symm_counit, map_shiftFunctorCompIsoId_hom_app,
    assoc, commShiftIso_hom_naturality_assoc, map_comp] at this
  apply_fun Quiver.Hom.op at this
  simp only [op_unop, op_comp, assoc] at this
  rw [homEquiv_apply, homEquiv_apply]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, op_obj,
    Equivalence.symm_functor, shiftEquiv'_inverse, comp_unit_app, id_obj,
    Equivalence.toAdjunction_unit, shiftEquiv'_symm_unit, opAdjointOpOfAdjoint_unit_app, opEquiv,
    Equiv.coe_fn_mk, unop_id, map_id, id_comp, Equiv.coe_fn_symm_mk, Functor.comp_map, op_map,
    assoc]
  conv_lhs => congr; rfl; congr
              change ((shiftFunctor D a).map (adj.counit.app ((unop Y)⟦a'⟧))).op; rfl
              change ((shiftFunctor D a).map
                (F.map (((NatIso.op (CommShift.iso a')).symm).hom.app Y ≫ u).unop)).op
  conv_rhs => congr; rfl; congr; rfl
              change (F.map ((shiftFunctor C a).map u.unop)).op ≫
                ((NatIso.op (CommShift.iso a)).symm).hom.app X
  simp only [oppositeShiftFunctorCompIsoId_inv_app, comp_obj, id_obj, op_obj, Iso.symm_hom,
    NatIso.op_inv, NatTrans.op_app, unop_comp, Quiver.Hom.unop_op, map_comp, op_comp,
    map_shiftFunctorCompIsoId_hom_app, assoc]
  rw [← this]
  slice_lhs 4 5 => rw [← op_comp]; erw [← (F.commShiftIso a).hom.naturality]; rw [op_comp]
  simp

variable {A}

lemma compat_right_triangle (adj : F ⊣ G) [CommShift F A] [CommShift G A] [adjunction_compat A adj]
    (a : A) (Y : D) :
    adj.unit.app ((G.obj Y)⟦a⟧) ≫ G.map ((CommShift.iso a).hom.app (G.obj Y)) ≫
    (CommShift.iso a).hom.app (F.obj (G.obj Y)) ≫ (G.map (adj.counit.app Y))⟦a⟧' = 𝟙 _ := by
  apply Faithful.map_injective (F := shiftFunctor C (-a))
  simp only [id_obj, comp_obj, map_comp, map_id]
  have := adjunction_compat.left_right_compat (-a) a (by simp) (G.obj Y) _ (𝟙 _) (adj := adj)
  rw [homEquiv_apply, homEquiv_apply] at this
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
    shiftEquiv'_inverse, comp_unit_app, id_obj, Equivalence.toAdjunction_unit,
    shiftEquiv'_symm_unit, comp_id, Functor.comp_map, assoc, map_shiftFunctorCompIsoId_inv_app,
    map_id] at this
  rw [← cancel_epi ((shiftFunctorCompIsoId C a (-a) (by simp)).hom.app (G.obj Y))] at this
  conv_lhs at this => rw [← assoc, ← assoc, Iso.hom_inv_id_app, id_comp]
  slice_lhs 1 2 => rw [this]
  simp only [comp_obj, id_obj, assoc]
  slice_lhs 5 6 => erw [Iso.inv_hom_id_app]
  erw [id_comp]
  slice_lhs 4 5 => rw [← map_comp]; erw [Iso.inv_hom_id_app, map_id]
  rw [id_comp]
  slice_lhs 1 2 => erw [← (shiftFunctorCompIsoId C a (-a) (by simp)).hom.naturality]
  slice_lhs 2 3 => erw [Iso.hom_inv_id_app]
  simp only [comp_obj, Functor.comp_map, id_comp]
  rw [← map_comp, ← map_comp]
  conv_lhs => congr; congr
              change adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)
              rw [← whiskerLeft_app G adj.unit Y, ← whiskerRight_app, ← NatTrans.comp_app]
              rw [adj.right_triangle]
  simp

lemma compat_left_triangle (adj : F ⊣ G) [CommShift F A] [CommShift G A] [adjunction_compat A adj]
    (a : A) (X : C) :
    (F.map (adj.unit.app X))⟦a⟧' ≫ (CommShift.iso a).inv.app (G.obj (F.obj X)) ≫
    F.map ((CommShift.iso a).inv.app (F.obj X)) ≫ adj.counit.app ((F.obj X)⟦a⟧) = 𝟙 _ := by
  have := @adjunction_compat_op C D _ _ F G A _ _ _ adj _ _ _
  have := @compat_right_triangle (OppositeShift D A) (OppositeShift C A) _ _ G.op F.op A _ _ _
    (opAdjointOpOfAdjoint G F adj) (CommShift.op G A inferInstance) (CommShift.op F A inferInstance)
    _ a (op X)
  apply_fun Quiver.Hom.unop at this
  simp [opEquiv] at this
  rw [unop_comp, unop_comp, unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op] at this
  simp only [assoc] at this
  exact this

noncomputable def left_right_equiv_compat_forward (adj : F ⊣ G) [CommShift F A] :
    @adjunction_compat C D _ _ F G A _ _ _ adj inferInstance
    ((left_right_equiv adj).toFun inferInstance) := by
  apply @adjunction_compat.mk C D _ _ F G A _ _ _ adj _ ((left_right_equiv adj).toFun inferInstance)
  intro a a' h X Y u
  exact left_to_right_compat adj inferInstance a a' h X Y u

def left_right_equiv_compat_backward (adj : F ⊣ G) [CommShift G A] :
    @adjunction_compat C D _ _ F G A _ _ _ adj ((left_right_equiv adj).invFun inferInstance)
    inferInstance := by
  apply @adjunction_compat.mk C D _ _ F G A _ _ _ adj
    ((left_right_equiv adj).invFun inferInstance) _
  intro a a' h X Y u
  exact right_to_left_compat adj inferInstance a a' h X Y u

end CommShift

section Pullback

open Adjunction CommShift

variable {B : Type*} [AddGroup B] (φ : B →+ A)

def adjunction_compat_pullback (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [CommShift.adjunction_compat A adj] :
    @CommShift.adjunction_compat (PullbackShift C φ) (PullbackShift D φ) _ _ F G B _ _ _
    adj (F.pullbackCommShift φ) (G.pullbackCommShift φ) := by
  refine @CommShift.adjunction_compat.mk (PullbackShift C φ) (PullbackShift D φ) _ _ F G B _ _ _
    adj (F.pullbackCommShift φ) (G.pullbackCommShift φ) ?_
  intro b b' h X Y u
  have h' : b' + b = 0 := by simp [eq_neg_of_add_eq_zero_left h]
  rw [← cancel_mono ((pullbackShiftIso C φ b (φ b) rfl).hom.app (G.obj Y)), homEquiv_apply,
    homEquiv_apply]
  simp [shiftEquiv'_symm_unit, shiftFunctorCompIsoId]
  have := adjunction_compat.left_right_compat (φ b) (φ b') (by rw [← φ.map_add, h, map_zero]) X Y
    ((pullbackShiftIso D φ b' (φ b') rfl).inv.app _ ≫ u) (adj := adj)
  rw [homEquiv_apply, homEquiv_apply] at this
  simp [shiftEquiv'_symm_unit, shiftFunctorCompIsoId] at this
  rw [pullbackShiftFunctorZero_inv_app, pullbackShiftFunctorAdd'_hom_app _ _ b' b 0 h' (φ b') (φ b)
    0 rfl rfl (by rw [map_zero]), pullbackShiftFunctorZero_inv_app, pullbackShiftFunctorAdd'_hom_app
     _ _ b' b 0 h' (φ b') (φ b) 0 rfl rfl (by rw [map_zero]), pullbackCommShift_iso_hom_app,
     pullbackCommShift_iso_hom_app]
  simp only [id_obj, comp_obj, map_comp, assoc, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, comp_id]
  slice_lhs 4 5 => rw [← map_comp]; erw [← adj.unit.naturality]; rw [Functor.id_map, map_comp]
  slice_lhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
  slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
  slice_rhs 7 8 => rw [← map_comp, (pullbackShiftIso D φ b (φ b) rfl).hom.naturality, map_comp]
  slice_rhs 6 7 => rw [← map_comp, (pullbackShiftIso D φ b (φ b) rfl).hom.naturality, map_comp]
  slice_rhs 5 6 => rw [← map_comp, Iso.inv_hom_id_app]
  simp only [id_obj, id_comp, assoc, map_id]
  exact this

end Pullback

end Adjunction

end CategoryTheory
