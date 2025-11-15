/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Adjunctions between additive functors.

This provides some results and constructions for adjunctions between functors on
preadditive categories:
* If one of the adjoint functors is additive, so is the other.
* If one of the adjoint functors is additive, the equivalence `Adjunction.homEquiv` lifts to
  an additive equivalence `Adjunction.homAddEquiv`.
* We also give a version of this additive equivalence as an isomorphism of `preadditiveYoneda`
  functors (analogous to `Adjunction.compYonedaIso`), in `Adjunction.compPreadditiveYonedaIso`.

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
  { adj.homEquiv _ _ with
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
lemma homAddEquiv_zero (X : C) (Y : D) : adj.homEquiv X Y 0 = 0 := map_zero (adj.homAddEquiv X Y)

@[simp]
lemma homAddEquiv_add (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f + f') = adj.homEquiv X Y f + adj.homEquiv X Y f' :=
  map_add (adj.homAddEquiv X Y) _ _

@[simp]
lemma homAddEquiv_sub (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f - f') = adj.homEquiv X Y f - adj.homEquiv X Y f' :=
  map_sub (adj.homAddEquiv X Y) _ _

@[simp]
lemma homAddEquiv_neg (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (- f) = - adj.homEquiv X Y f := map_neg (adj.homAddEquiv X Y) _

@[simp]
lemma homAddEquiv_symm_zero (X : C) (Y : D) :
    (adj.homEquiv X Y).symm 0 = 0 := map_zero (adj.homAddEquiv X Y).symm

@[simp]
lemma homAddEquiv_symm_add (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f' :=
  map_add (adj.homAddEquiv X Y).symm _ _

@[simp]
lemma homAddEquiv_symm_sub (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f - f') = (adj.homEquiv X Y).symm f - (adj.homEquiv X Y).symm f' :=
  map_sub (adj.homAddEquiv X Y).symm _ _

@[simp]
lemma homAddEquiv_symm_neg (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (- f) = - (adj.homEquiv X Y).symm f :=
  map_neg (adj.homAddEquiv X Y).symm _

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the necessary
universe lifting functors.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
def compPreadditiveYonedaIso :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} ≅
      preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
        (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} :=
  NatIso.ofComponents
    (fun Y ↦ NatIso.ofComponents
      (fun X ↦ (AddEquiv.ulift.trans ((adj.homAddEquiv (unop X) Y).symm.trans
        AddEquiv.ulift.symm)).toAddCommGrpIso)
      (fun g ↦ by
        ext ⟨y⟩
        exact AddEquiv.ulift.injective (adj.homEquiv_naturality_left_symm g.unop y)))
    (fun f ↦ by
      ext _ ⟨x⟩
      exact AddEquiv.ulift.injective ((adj.homEquiv_naturality_right_symm x f)))

lemma compPreadditiveYonedaIso_hom_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)) :
      ((adj.compPreadditiveYonedaIso.hom.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y).symm (AddEquiv.ulift a)) := rfl

lemma compPreadditiveYonedaIso_inv_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)) :
      ((adj.compPreadditiveYonedaIso.inv.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y) (AddEquiv.ulift a)) := rfl

end Adjunction

end CategoryTheory
