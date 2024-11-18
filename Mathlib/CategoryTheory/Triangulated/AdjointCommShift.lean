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
    ((shiftEquiv C a).symm.toAdjunction.homEquiv X (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C (-a)).obj X) Y) ((CommShift.iso (-a)).hom.app X ≫
    ((shiftEquiv D a).symm.toAdjunction.homEquiv (F.obj X) Y).symm
    ((adj.homEquiv X ((shiftFunctor D a).obj Y)).symm u))) := by
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, left_to_right_iso,
    Equivalence.symm_functor, shiftEquiv'_inverse, Equiv.invFun_as_coe, natIsoEquiv_symm_apply_hom,
    natTransEquiv_symm_apply_app, comp_unit_app, id_obj, Equivalence.toAdjunction_unit,
    comp_counit_app, Equivalence.toAdjunction_counit, Functor.comp_map, map_comp, assoc,
    homEquiv_symm_apply, homEquiv_apply]
  slice_lhs 1 2 => erw [(shiftEquiv C a).symm.unit.naturality u]
  simp only [id_obj, Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, comp_obj, Functor.comp_map, assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp]; erw [adj.unit.naturality (u⟦-a⟧')]
  slice_rhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [← (CommShift.iso (-a)).hom.naturality u]
  simp only [assoc, Functor.map_comp]
  rfl

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
  (Adjunction.natIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
  (add_left_neg _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
  (add_left_neg _)).symm.toAdjunction adj)).toFun (commG.iso (-a))

lemma right_to_left_iso_hom_app (adj : F ⊣ G) (commG : CommShift G A) (a : A) (X : C) :
    (right_to_left_iso adj commG a).hom.app X = (adj.homEquiv _ _).symm
    (((shiftEquiv' C (-a) a (by simp)).symm.toAdjunction.homEquiv _ _).symm (((adj.homEquiv X _)
    (((shiftEquiv' D (-a) a (by simp)).symm.toAdjunction.homEquiv _ _)
    (𝟙 ((F.obj X)⟦a⟧)))) ≫ (commG.iso (-a)).hom.app _)) := sorry

noncomputable def left_to_right_iso_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    (F ⋙ (shiftEquiv' D (-a) a (neg_add_self a)).symm.functor).op ≅
      ((shiftEquiv' C (-a) a (neg_add_self a)).symm.functor ⋙ F).op :=
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
  change _ = (natIsoEquiv _ _).symm _
  erw [shiftEquiv'_symm_toAdjunction_op, shiftEquiv'_symm_toAdjunction_op]
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
    erw [← shiftEquiv'_add_symm_homEquiv C a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg a)
        (add_right_neg b) (add_right_neg (a + b)) rfl]
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
    erw [← shiftEquiv_add_symm_homEquiv D a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg a)
        (add_right_neg b) (add_right_neg (a + b)) rfl]
    simp [shiftFunctorAdd'_eq_shiftFunctorAdd]
  erw [heq']
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
      shiftEquiv'_inverse]
  erw [← (shiftEquiv D a).symm.toAdjunction.homEquiv_naturality_left_symm]
  conv_rhs => rw [comp_left_to_right_iso_hom_app]
              erw [← (shiftEquiv C b).symm.toAdjunction.homEquiv_naturality_right]
              rw [comp_left_to_right_iso_hom_app]
  simp

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

def commShift_left_right_compat (adj : F ⊣ G) (commF : CommShift F A) (commG : CommShift G A)
    (a a' : A) (ha : a + a' = 0) (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) :=
  ((shiftEquiv' C a a' ha).symm.toAdjunction.comp adj).homEquiv _ _ ((commF.iso a').hom.app X ≫ u)
  = (((adj.comp (shiftEquiv' D a a' ha).symm.toAdjunction).homEquiv _ _) u) ≫
  (commG.iso a).hom.app Y

lemma left_to_right_compat (adj : F ⊣ G) (commF : CommShift F A) (a a' : A) (ha : a + a' = 0)
    (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) : commShift_left_right_compat adj commF
    (left_to_right adj commF) a a' ha X Y u := by
  dsimp [commShift_left_right_compat, left_to_right]
  rw [comp_left_to_right_iso_hom_app, comp_homEquiv, comp_homEquiv]
  simp only [Equiv.trans_apply, comp_obj, map_comp, Equivalence.symm_functor, shiftEquiv'_inverse,
    Equivalence.symm_inverse, shiftEquiv'_functor, assoc, counit_naturality, id_obj,
    counit_naturality_assoc, left_triangle_components_assoc]
  rw [Equiv.symm_apply_apply]

  -- erw [Equiv.apply_symm_apply]



noncomputable def left_right_equiv (adj : F ⊣ G) : CommShift F A ≃ CommShift G A where
  toFun := left_to_right adj
  invFun := right_to_left adj
  left_inv commF := by
    ext a X
    simp [left_to_right, right_to_left]
    rw [right_to_left_iso_hom_app]
    erw [left_to_right_iso_hom_app]
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
      shiftEquiv'_functor, comp_obj, map_id, comp_id, id_comp, map_comp, assoc]
    sorry
  right_inv := sorry

end CommShift

end Adjunction

end CategoryTheory
