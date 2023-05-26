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
  @Adjunction.toEquivalence _ _ _ _ _ _
    (adj.restrictFullyFaithful' adj.is_left_fixed_point adj.is_right_fixed_point
                                sorry sorry)
    sorry sorry

end CategoryTheory
