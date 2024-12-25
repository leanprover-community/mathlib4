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

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
@[simps!]
def homAddEquiv [F.Additive] (X : C) (Y : D) :
    AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]
def homAddEquiv_zero [F.Additive] (X : C) (Y : D) :
    adj.homAddEquiv X Y 0 = 0 := by rw [map_zero]

@[simp]
def homAddEquiv_add [F.Additive] (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y (f + f') = adj.homAddEquiv X Y f + adj.homAddEquiv X Y f' := by
  rw [AddEquivClass.map_add]

@[simp]
def homAddEquiv_sub [F.Additive] (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y (f - f') = adj.homAddEquiv X Y f - adj.homAddEquiv X Y f' := by
  rw [AddEquiv.map_sub]

@[simp]
def homAddEquiv_neg [F.Additive] (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y (- f) = - adj.homAddEquiv X Y f := by rw [AddEquiv.map_neg]

@[simp]
def homAddEquiv_symm_zero [F.Additive] (X : C) (Y : D) :
    (adj.homAddEquiv X Y).symm 0 = 0 := by simp

@[simp]
def homAddEquiv_symm_add [F.Additive] (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm (f + f') = (adj.homAddEquiv X Y).symm f +
      (adj.homAddEquiv X Y).symm f' := by simp

@[simp]
def homAddEquiv_symm_sub [F.Additive] (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm (f - f') = (adj.homAddEquiv X Y).symm f
      - (adj.homAddEquiv X Y).symm f' := by simp

@[simp]
def homAddEquiv_symm_neg [F.Additive] (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm (- f) = - (adj.homAddEquiv X Y).symm f := by simp

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the necessary
universe lifting functors.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
@[simps!]
def compPreadditiveYonedaIsoOfLeftAdjoint [F.Additive] :
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

end Adjunction

end CategoryTheory
