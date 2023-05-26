import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.ConcreteCategory.Basic

namespace CategoryTheory

open Category Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

-- maybe we should define this in terms of fixed points of (co)pointed functors?
def Adjunction.is_left_fixed_point (X : C) := IsIso (adj.unit.app X)
def Adjunction.is_right_fixed_point (Y : D) := IsIso (adj.counit.app Y)

lemma Adjunction.left_fixed_point_iff_Opposite (X : C)
    : adj.is_left_fixed_point X
    ↔ (Adjunction.opAdjointOpOfAdjoint G F adj).is_right_fixed_point (op X) :=
    by simp only [is_left_fixed_point, Functor.id_obj, Functor.comp_obj,
                  is_right_fixed_point, Functor.op_obj, unop_op, homEquiv_unit,
                  opAdjointOpOfAdjoint, opEquiv, mkOfHomEquiv_counit_app,
                  Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, isIso_op_iff,
                  Equiv.symm_symm, Equiv.coe_fn_mk, Functor.map_id,
                  Equiv.symm_trans_apply, unop_id, comp_id]

lemma Adjunction.right_fixed_point_iff_Opposite (Y : D)
    : adj.is_right_fixed_point Y
    ↔ (Adjunction.opAdjointOpOfAdjoint G F adj).is_left_fixed_point (op Y) :=
    by simp only [is_right_fixed_point, Functor.comp_obj, Functor.id_obj,
                  is_left_fixed_point, Functor.op_obj, unop_op,
                  opAdjointOpOfAdjoint, opEquiv, mkOfHomEquiv_unit_app,
                  Equiv.trans_apply, Equiv.coe_fn_mk, unop_id, isIso_op_iff,
                  homEquiv_counit, Functor.map_id, id_comp, Equiv.coe_fn_symm_mk]

abbrev Adjunction.left_fixed_points := CategoryTheory.FullSubcategory adj.is_left_fixed_point
abbrev Adjunction.right_fixed_points := CategoryTheory.FullSubcategory adj.is_right_fixed_point

noncomputable
def Adjunction.fixed_points_equiv : adj.left_fixed_points ≌ adj.right_fixed_points :=
  have h1 : ∀ X, is_left_fixed_point adj X → is_right_fixed_point adj (F.obj X) := by {
    intro X h
    dsimp only [is_left_fixed_point, is_right_fixed_point] at h ⊢
    haveI := h
    haveI : IsIso (F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X))
          := by { convert IsIso.id (F.obj X);
                  exact congr_fun (congr_arg NatTrans.app adj.left_triangle) X }
    exact IsIso.of_isIso_comp_left (F.map (adj.unit.app X)) (adj.counit.app (F.obj X))
  }
  have h2 : ∀ Y, is_right_fixed_point adj Y → is_left_fixed_point adj (G.obj Y) := by {
    intro Y h
    dsimp only [is_left_fixed_point, is_right_fixed_point] at h ⊢
    haveI := h
    haveI : IsIso (adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)) := by
      convert IsIso.id (G.obj Y);
      exact congr_fun (congr_arg NatTrans.app adj.right_triangle) Y
    exact IsIso.of_isIso_comp_right (adj.unit.app (G.obj Y)) (G.map (adj.counit.app Y))
  }
  --this should be cleaned up
  @Adjunction.toEquivalence _ _ _ _ _ _
    (adj.restrictFullyFaithful' adj.is_left_fixed_point adj.is_right_fixed_point (h1 _) (h2 _))
    (by rintro ⟨X, h⟩
        dsimp only [is_left_fixed_point, Functor.id_obj, Functor.comp_obj] at h
        haveI : ReflectsIsomorphisms (fullSubcategoryInclusion adj.is_left_fixed_point) :=
          reflectsIsomorphisms_of_full_and_faithful
            (fullSubcategoryInclusion (is_left_fixed_point adj))
        simp only [Functor.id_obj, fullSubcategoryInclusion, inducedFunctor,
                   Functor.comp_obj, restrictFullyFaithful', restrictFullyFaithful,
                   FullSubcategory.lift_obj_obj, equivOfFullyFaithful, Functor.preimage,
                   FullSubcategory.lift_comp_inclusion, Iso.symm_symm_eq,
                   NatIso.ofComponents.app, Equiv.instTransSortSortSortEquivEquivEquiv_trans,
                   mkOfHomEquiv_unit_app, Equiv.trans_apply, Equiv.coe_fn_mk,
                   Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom, comp_id, id_comp,
                   homEquiv_unit, Iso.app_hom, Iso.symm_hom,
                   NatIso.ofComponents_inv_app, Equiv.coe_fn_symm_mk,
                   Full.preimage, FullSubcategory.lift]
        dsimp [is_left_fixed_point] at h; haveI := h
        exact @isIso_of_reflects_iso (FullSubcategory (is_left_fixed_point adj)) _ C _ _ _ _
                (fullSubcategoryInclusion (is_left_fixed_point adj)) IsIso.comp_isIso _)
    (by rintro ⟨Y, h⟩
        dsimp only [is_left_fixed_point, Functor.id_obj, Functor.comp_obj] at h
        haveI : ReflectsIsomorphisms (fullSubcategoryInclusion adj.is_right_fixed_point) :=
          reflectsIsomorphisms_of_full_and_faithful
            (fullSubcategoryInclusion (is_right_fixed_point adj))
        simp only [fullSubcategoryInclusion, inducedFunctor, Functor.comp_obj, Functor.id_obj, restrictFullyFaithful',
                   restrictFullyFaithful, FullSubcategory.lift_obj_obj, equivOfFullyFaithful, Functor.preimage,
                   FullSubcategory.lift_comp_inclusion, Iso.symm_symm_eq, NatIso.ofComponents.app,
                   Equiv.instTransSortSortSortEquivEquivEquiv_trans, mkOfHomEquiv_counit_app, Equiv.invFun_as_coe,
                   Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, Iso.homCongr_symm, Iso.refl_symm,
                   Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Iso.app_inv, Iso.symm_inv, NatIso.ofComponents_hom_app,
                   Iso.refl_hom, comp_id, id_comp, homEquiv_counit, Equiv.coe_fn_symm_mk,
                   Full.preimage, FullSubcategory.lift]
        dsimp [is_right_fixed_point] at h; haveI := h
        exact @isIso_of_reflects_iso (FullSubcategory (is_right_fixed_point adj)) _ _ _ _ _ _
                (fullSubcategoryInclusion (is_right_fixed_point adj)) IsIso.comp_isIso _)

end CategoryTheory
