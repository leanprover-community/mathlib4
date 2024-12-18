/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie More, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
Doc doc.

-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj
lemma right_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

lemma left_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.-/
@[simps! (config := .lemmasOnly)]
def homAddEquiv_of_leftAdjoint [F.Additive] (X : C) (Y : D) :
    AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp only [Equiv.toFun_as_coe, homEquiv_apply, comp_obj, Functor.map_add,
        Preadditive.comp_add] }

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `G` is additive, then the hom set equivalence upgrades to an `AddEquiv`.-/
@[simps! (config := .lemmasOnly)]
def homAddEquiv_of_right_adjoint_additive [G.Additive] (X : C) (Y : D) :
    AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv _ _ with
    map_add' _ _ := by
      simp only [Equiv.toFun_as_coe, homEquiv_apply, Functor.map_add, Preadditive.comp_add] }

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the ncessary
universe lifting functors.-/
@[simps! (config := .lemmasOnly)]
def compPreadditiveYonedaIso_of_leftAdjoint [F.Additive] :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} ≅
    preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
    (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} := by
  refine NatIso.ofComponents (fun Y ↦ ?_) (fun _ ↦ ?_)
  · refine NatIso.ofComponents
      (fun X ↦ ((AddEquiv.ulift.trans (adj.homAddEquiv_of_leftAdjoint (unop X) Y)).trans
               AddEquiv.ulift.symm).toAddCommGrpIso.symm) (fun _ ↦ ?_)
    ext
    simp only [comp_obj, preadditiveYoneda_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
      op_obj, ModuleCat.forget₂_obj, preadditiveYonedaObj_obj_carrier,
      preadditiveYonedaObj_obj_isAddCommGroup, AddCommGrp.uliftFunctor_obj, AddCommGrp.coe_of,
      Functor.comp_map, ModuleCat.forget₂_map, preadditiveYonedaObj_obj_isModule,
      AddCommGrp.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe, Iso.symm_hom,
      AddEquiv.toAddCommGrpIso_inv, AddCommGrp.coe_comp', AddMonoidHom.coe_coe, Function.comp_apply,
      AddCommGrp.ofHom_apply, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
      preadditiveYonedaObj_map_hom_apply, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
      AddEquiv.apply_symm_apply, op_map]
    erw [adj.homEquiv_naturality_left_symm]
    rfl
  · ext
    simp only [comp_obj, preadditiveYoneda_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
      op_obj, ModuleCat.forget₂_obj, preadditiveYonedaObj_obj_carrier,
      preadditiveYonedaObj_obj_isAddCommGroup, AddCommGrp.uliftFunctor_obj, AddCommGrp.coe_of,
      Functor.comp_map, whiskeringRight_obj_map, NatTrans.comp_app, whiskerRight_app,
      AddCommGrp.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe, NatIso.ofComponents_hom_app,
      Iso.symm_hom, AddEquiv.toAddCommGrpIso_inv, AddCommGrp.coe_comp', AddMonoidHom.coe_coe,
      Function.comp_apply, AddCommGrp.ofHom_apply, AddMonoidHom.coe_comp, AddEquiv.symm_trans_apply,
      AddEquiv.symm_symm, AddEquiv.apply_symm_apply, whiskeringLeft_obj_map, whiskerLeft_app]
    erw [adj.homEquiv_naturality_right_symm]
    rfl

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `G` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the ncessary
universe lifting functors.-/
@[simps! (config := .lemmasOnly)]
def compPreadditiveYonedaIso_of_right_adjoint_additive [G.Additive] :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} ≅
    preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
    (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} := by
  refine NatIso.ofComponents (fun Y ↦ ?_) (fun _ ↦ ?_)
  · refine NatIso.ofComponents
      (fun X ↦ ((AddEquiv.ulift.trans (adj.homAddEquiv_of_right_adjoint_additive (unop X) Y)).trans
               AddEquiv.ulift.symm).toAddCommGrpIso.symm) (fun _ ↦ ?_)
    ext
    simp only [comp_obj, preadditiveYoneda_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
      op_obj, ModuleCat.forget₂_obj, preadditiveYonedaObj_obj_carrier,
      preadditiveYonedaObj_obj_isAddCommGroup, AddCommGrp.uliftFunctor_obj, AddCommGrp.coe_of,
      Functor.comp_map, ModuleCat.forget₂_map, preadditiveYonedaObj_obj_isModule,
      AddCommGrp.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe, Iso.symm_hom,
      AddEquiv.toAddCommGrpIso_inv, AddCommGrp.coe_comp', AddMonoidHom.coe_coe, Function.comp_apply,
      AddCommGrp.ofHom_apply, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
      preadditiveYonedaObj_map_hom_apply, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
      AddEquiv.apply_symm_apply, op_map]
    erw [adj.homEquiv_naturality_left_symm]
    rfl
  · ext
    simp only [comp_obj, preadditiveYoneda_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
      op_obj, ModuleCat.forget₂_obj, preadditiveYonedaObj_obj_carrier,
      preadditiveYonedaObj_obj_isAddCommGroup, AddCommGrp.uliftFunctor_obj, AddCommGrp.coe_of,
      Functor.comp_map, whiskeringRight_obj_map, NatTrans.comp_app, whiskerRight_app,
      AddCommGrp.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe, NatIso.ofComponents_hom_app,
      Iso.symm_hom, AddEquiv.toAddCommGrpIso_inv, AddCommGrp.coe_comp', AddMonoidHom.coe_coe,
      Function.comp_apply, AddCommGrp.ofHom_apply, AddMonoidHom.coe_comp, AddEquiv.symm_trans_apply,
      AddEquiv.symm_symm, AddEquiv.apply_symm_apply, whiskeringLeft_obj_map, whiskerLeft_app]
    erw [adj.homEquiv_naturality_right_symm]
    rfl

end Adjunction

end CategoryTheory
