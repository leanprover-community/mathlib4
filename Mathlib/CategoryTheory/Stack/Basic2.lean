import Mathlib.CategoryTheory.Stack.Descent2

universe v u v₁ u₁

open CategoryTheory Opposite Bicategory Pseudofunctor LocallyDiscrete
open ProofWidgets Mathlib.Tactic.Widget

variable {C : Type u} [Category.{v} C]

@[simps]
def homPreSheaf (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C) (x y : S.mkCat U) :
    Opposite (Over U) ⥤ Type v₁ where
  obj V := (S.mkFunctor V.unop.hom).obj x ⟶ (S.mkFunctor V.unop.hom).obj y
  map {V V'} g ϕ :=
    eqToHom (by simp) ≫ (S.mapCompCat V.unop.hom g.unop.left).hom.app x ≫
    (S.mkFunctor g.unop.left).map ϕ ≫
    (S.mapCompCat V.unop.hom g.unop.left).inv.app y ≫ eqToHom (by simp)
  map_id := by
    rintro ⟨X, _, f : X ⟶ U⟩
    ext g
    dsimp only [Functor.id_obj, Functor.const_obj_obj, unop_id, Over.id_left, Cat.comp_obj,
      mapCompCat, op_id, types_id_apply]
    rw [S.mapComp_eq_right _ (show (mkHom (𝟙 (op X))) = 𝟙 _ from rfl)]
    simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]
    rw [S.mapComp_id_right_hom, S.mapComp_id_right_inv]
    rw [LocallyDiscrete.rightUnitor_hom, LocallyDiscrete.rightUnitor_inv]
    simp only [S.map₂_eqToHom, Cat.comp_app, Cat.comp_obj, Cat.eqToHom_app, Cat.id_obj,
      Cat.rightUnitor_inv_app, eqToHom_refl, Cat.whiskerLeft_app, Category.id_comp,
      Category.comp_id, eqToHom_iso_hom_naturality, eqToHom_naturality_assoc, Category.assoc,
      eqToHom_trans_assoc]
    simp [Cat.rightUnitor_hom_app]
  map_comp := by
    rintro ⟨X, _, f : X ⟶ U⟩ ⟨Y, _, g : Y ⟶ U⟩ ⟨Z, _, h : Z ⟶ U⟩ ⟨i, _, eqi⟩ ⟨j, _, eqj⟩
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

structure IsStack (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) : Prop where
  is_sheaf_of_hom (U : C) (x y : S.mkCat U) :
    Presieve.IsSheaf (J.over U) (homPreSheaf S U x y)
  is_descent_effective (U : C) (R : Sieve U) (_ : R ∈ J.sieves U) (d : S.DescentData R) :
    ∃ x : S.mkCat U, Nonempty (d ≅ DescentData.canonical S x)
