/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie More, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Adjunctions between additive functors.

This provides some results and constructions for adjunctions between functors on
preadditive categories:
* If one of the adjoint functors is additive, so is the other.
* If one of the adjoint functors is additive, the equivalence `Adjunction.homEquiv` lifts to
an additive equivalence `Adjunction.homAddEquivOfLeftAdjoint` resp.
`Adjunction.homAddEquivOfRightAdjoint`.
* We also give a version of this additive equivalence as an isomorphism of `preadditiveYoneda`
functors (analogous to `Adjunction.compYonedaIso`), in
`Adjunction.compPreadditiveYonedaIsoOfLeftAdjoint` resp.
`Adjunction.compPreadditiveYonedaIsoOfRightAdjoint`.

-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj
lemma right_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

lemma left_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

variable [F.Additive]

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
def homAddEquiv (X : C) (Y : D) : AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]
lemma homAddEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y f = adj.homEquiv X Y f := rfl

@[simp]
lemma homAddEquiv_symm_apply (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm f = (adj.homEquiv X Y).symm f := rfl

@[simp]
lemma homAddEquiv_zero (X : C) (Y : D) : adj.homEquiv X Y 0 = 0 := by
  change adj.homAddEquiv X Y 0 = 0
  rw [map_zero]

@[simp]
lemma homAddEquiv_add (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f + f') = adj.homEquiv X Y f + adj.homEquiv X Y f' := by
  change adj.homAddEquiv X Y (f + f') = _
  simp [AddEquivClass.map_add]

@[simp]
lemma homAddEquiv_sub (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f - f') = adj.homEquiv X Y f - adj.homEquiv X Y f' := by
  change adj.homAddEquiv X Y (f - f') = _
  simp [AddEquiv.map_sub]

@[simp]
lemma homAddEquiv_neg (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (- f) = - adj.homEquiv X Y f := by
  change adj.homAddEquiv X Y (- f) = _
  simp [AddEquiv.map_neg]

@[simp]
lemma homAddEquiv_symm_zero (X : C) (Y : D) :
    (adj.homEquiv X Y).symm 0 = 0 := by
  change (adj.homAddEquiv X Y).symm 0 = 0
  rw [map_zero]

@[simp]
lemma homAddEquiv_symm_add (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f' := by
  change (adj.homAddEquiv X Y).symm (f + f') = _
  simp [AddEquivClass.map_add]

@[simp]
lemma homAddEquiv_symm_sub (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f - f') = (adj.homEquiv X Y).symm f - (adj.homEquiv X Y).symm f' := by
  change (adj.homAddEquiv X Y).symm (f - f') = _
  simp [AddEquiv.map_sub]

@[simp]
lemma homAddEquiv_symm_neg (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (- f) = - (adj.homEquiv X Y).symm f := by
  change (adj.homAddEquiv X Y).symm (- f) = _
  simp [AddEquiv.map_neg]

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the necessary
universe lifting functors.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
def compPreadditiveYonedaIso :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} ≅
      preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
        (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} := by
  refine NatIso.ofComponents (fun Y ↦ ?_) (fun _ ↦ ?_)
  · refine NatIso.ofComponents
      (fun X ↦ ((AddEquiv.ulift.trans (adj.homAddEquiv (unop X) Y)).trans
               AddEquiv.ulift.symm).toAddCommGrpIso.symm) (fun _ ↦ ?_)
    ext
    simp [homAddEquiv, adj.homEquiv_naturality_left_symm]
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

@[simp]
lemma compPreadditiveYonedaIso_hom_app_app_apply_down (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)) :
      (((adj.compPreadditiveYonedaIso.hom.app Y).app X) a).down =
        (adj.homEquiv (Opposite.unop X) Y).symm (AddEquiv.ulift a) := rfl

@[simp]
lemma compPreadditiveYonedaIso_inv_app_app_apply_down (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)) :
      (((adj.compPreadditiveYonedaIso.inv.app Y).app X) a).down =
        (adj.homEquiv (Opposite.unop X) Y) (AddEquiv.ulift a) := rfl

end Adjunction

end CategoryTheory
