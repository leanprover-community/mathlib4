/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Stack.Descent

/-!
# Stacks

Let `C` be a category equipped with a Grothendieck topology `J`. A stack is a pseudofunctor `S` from
`C` into the 2-category `Cat` such that
* for any object `a : C` and any pair of objects `x, y : S a`, the presheaf of morphisms between
  `x` and `y` is a sheaf with respect to the topology `J`, and
* for any object `a : C` and any sieve `R ∈ J a`, any descent datum on `R` is
  effective, i.e., it is isomorphic to the canonical descent datum associated with some object
  of `S a`.

-/

universe v u v₁ u₁

open CategoryTheory Opposite Bicategory Pseudofunctor LocallyDiscrete

namespace CategoryTheory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- For a pseudofunctor on `C`, an object `a : C`, and two objects `x y : S a`, we define
`homPreSheaf S a x y` as a functor `(Over a)ᵒᵖ ⥤ Type v₁` that sends an object `b` over `a`
(this is a morphism `b ⟶ a` in `C`) to the hom-set `(S b) x ⟶ (S b) y` in the category `S b`. -/
@[simps]
def homPreSheaf (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (a : C) (x y : S.mkCat a) :
    (Over a)ᵒᵖ ⥤ Type v₁ where
  obj b := (S.mkFunctor b.unop.hom).obj x ⟶ (S.mkFunctor b.unop.hom).obj y
  map {b c} g ϕ :=
    eqToHom (by simp) ≫ (S.mapCompCat b.unop.hom g.unop.left).hom.app x ≫
    (S.mkFunctor g.unop.left).map ϕ ≫
    (S.mapCompCat b.unop.hom g.unop.left).inv.app y ≫ eqToHom (by simp)
  map_id := by
    rintro ⟨x, _, f : x ⟶ a⟩
    ext g
    dsimp only [Functor.id_obj, Functor.const_obj_obj, unop_id, Over.id_left, Cat.comp_obj,
      mapCompCat, op_id, types_id_apply]
    rw [S.mapComp_eq_right _ (show (mkHom (𝟙 (op x))) = 𝟙 _ from rfl)]
    simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]
    rw [S.mapComp_id_right_hom, S.mapComp_id_right_inv]
    rw [LocallyDiscrete.rightUnitor_hom, LocallyDiscrete.rightUnitor_inv]
    simp only [S.map₂_eqToHom, Cat.comp_app, Cat.comp_obj, Cat.eqToHom_app, Cat.id_obj,
      Cat.rightUnitor_inv_app, eqToHom_refl, Cat.whiskerLeft_app, Category.id_comp,
      Category.comp_id, eqToHom_iso_hom_naturality, eqToHom_naturality_assoc, Category.assoc,
      eqToHom_trans_assoc]
    simp [Cat.rightUnitor_hom_app]
  map_comp := by
    rintro ⟨b, _, f : b ⟶ a⟩ ⟨c, _, g : c ⟶ a⟩ ⟨d, _, h : d ⟶ a⟩ ⟨i, _, eqi⟩ ⟨j, _, eqj⟩
    have eqi : i ≫ f = g := by simpa using eqi
    have eqj : j ≫ g = h := by simpa using eqj
    have eqi' : mkHom g.op = mkHom f.op ≫ mkHom i.op :=
      congrArg mkHom (congrArg Quiver.Hom.op (eqi.symm))
    have eqj' : mkHom h.op = mkHom g.op ≫ mkHom j.op :=
      congrArg mkHom (congrArg Quiver.Hom.op (eqj.symm))
    ext ϕ
    dsimp only [Functor.id_obj, Functor.const_obj_obj, unop_comp, Quiver.Hom.unop_op',
      Over.comp_left, Cat.comp_obj, mapCompCat, op_comp, types_comp_apply]
    rw [S.mapComp_eq_right _ (show (mkHom (i.op ≫ j.op) = mkHom i.op ≫ mkHom j.op) from rfl)]
    rw [S.mapComp_eq_left (show mkHom g.op = mkHom f.op ≫ mkHom i.op from eqi')]
    dsimp only [eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Cat.comp_app, Cat.comp_obj, Cat.id_app,
      Iso.trans_inv, Iso.refl_inv]
    simp only [Category.comp_id, Category.assoc]
    rw [Category.id_comp (X := (S.map (mkHom f.op ≫ mkHom (i.op ≫ j.op))).obj x)]
    rw [Category.id_comp (X := (S.map (mkHom i.op ≫ mkHom j.op)).obj ((S.map (mkHom f.op)).obj y))]
    rw [Category.id_comp (X := (S.map (mkHom f.op ≫ mkHom (i.op ≫ j.op))).obj y)]
    rw [S.mapComp_comp_right_app, S.mapComp_comp_right_inv]
    simp only [Cat.comp_obj, associator_inv, S.map₂_eqToHom, Cat.eqToHom_app,
      Cat.associator_hom_app, eqToHom_refl, Category.id_comp, associator_hom, Cat.comp_app,
      Cat.whiskerLeft_app, Cat.associator_inv_app, Cat.whiskerRight_app, Category.assoc,
      eqToHom_trans, NatTrans.naturality_assoc, Cat.comp_map, Iso.inv_hom_id_app_assoc,
      eqToHom_trans_assoc, eqToIso.hom, Functor.map_comp, eqToHom_map, eqToIso.inv]

open Pseudofunctor

variable {J : GrothendieckTopology C}

/-- A `Pseudofunctor` `S : LocallyDiscrete Cᵒᵖ ⥤ Cat` is a stack (with respect to a
Grothendieck topology `J` on `C`) if:
1. for any object `a : C` and any `x y : S.mkCat a`, the presheaf `S.homPreSheaf a x y` is a sheaf
  for the topology `J.over a`.
2. for any covering sieve `R ∈ J a`, any descent datum `d` relative to `R` is effective, that is,
  there exists an object `x : S a` such that `d` is isomorphic to the canonical descent datum
  associated with `x`. -/
@[stacks 026F]
structure IsStack (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) : Prop where
  is_sheaf_of_hom (a : C) (x y : S.mkCat a) :
    Presieve.IsSheaf (J.over a) (S.homPreSheaf a x y)
  is_descent_effective (a : C) (R : Sieve a) (_ : R ∈ J a) (d : S.DescentData R) :
    ∃ x : S.mkCat a, Nonempty (d ≅ DescentData.canonical S x)

end Pseudofunctor

end CategoryTheory
