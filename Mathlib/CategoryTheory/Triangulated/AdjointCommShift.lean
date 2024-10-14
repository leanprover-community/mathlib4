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

/-
-- unpack the composite adjunctions here, it's better for later
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
-/

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
  add a b := by
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
      /-erw [← shiftEquiv'_add_symm_homEquiv C a (-a) b (-b) (a + b) (-(a + b)) (add_right_neg a)
        (add_right_neg b) (add_right_neg (a + b)) rfl]-/ -- a bit more complicated than this...
      sorry
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
