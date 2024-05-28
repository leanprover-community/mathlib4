import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas

universe u v u' v'

open CategoryTheory Limits ProofWidgets

noncomputable section

variable (C : Type u) [Category.{v, u} C] (D : Type u') [Category.{v', u'} D] [HasFiniteProducts D]

instance functorCategoryHasFiniteProducts : HasFiniteProducts (C ⥤ D) where
  out _ := inferInstance
-- This should be an instance in mathlib, but it doesn't
-- seem to be there. TODO: add it.

-- set_option maxHeartbeats 5000000

def GroupObjectFunctorToFunctorGroupObject (G : GroupObject (C ⥤ D)) :
    C ⥤ (GroupObject D) where
  obj X := {
    X := G.X.obj X
    one := (PreservesTerminal.iso ((evaluation _ _).obj X)).inv ≫ G.one.app X
    mul := (PreservesLimitPair.iso ((evaluation _ _).obj X) G.X G.X).inv ≫ G.mul.app X
    inv := G.inv.app X
    one_mul := by
      simp only [evaluation_obj_obj, prod.leftUnitor_hom]
      rw [prod_map_comp_left_id_right, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                    PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                    ((evaluation C D).obj X) G.one (𝟙 G.X), evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.one_mul, prod.leftUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_snd]
      simp only [evaluation_obj_obj, prod.map_snd, Category.comp_id]
    mul_one := by
      simp only [evaluation_obj_obj, prod.rightUnitor_hom]
      rw [prod_map_comp_right_id_left, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) (𝟙 G.X) G.one, evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.mul_one, prod.rightUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_fst]
      simp only [evaluation_obj_obj, prod.map_fst, Category.comp_id]
    mul_assoc := by
      rw [prod_map_comp_left_id_right]
      slice_lhs 2 3 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) G.mul (𝟙 G.X), evaluation_obj_map]
      slice_lhs 3 4 => rw [← NatTrans.comp_app, G.mul_assoc]
      rw [prod_map_comp_right_id_left]
      slice_rhs 3 4 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural ((evaluation C D).obj X)
                         (𝟙 G.X) G.mul, evaluation_obj_map]
      rw [NatTrans.comp_app, ← Category.assoc, ← Category.assoc, ← PreservesLimitPair.iso_inv]
      conv_lhs => rw [← evaluation_obj_map, Category.assoc _
        (PreservesLimitPair.iso ((evaluation C D).obj X) (G.X ⨯ G.X) G.X).inv _]
      have : 𝟙 (G.X.obj X) = 𝟙 (((evaluation C D).obj X).obj G.X) := by
        simp only [evaluation_obj_obj]
      rw [this, PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X
        ((CategoryTheory.evaluation C D).obj X)]
      simp only [evaluation_obj_obj, prod.associator_hom, Pi.id_apply, PreservesLimitPair.iso_inv,
        prod.lift_map_assoc, Category.comp_id, NatTrans.comp_app, Category.assoc]
    mul_left_inv := by
      rw [← Category.assoc]
      rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map]
      conv_lhs => congr
                  erw [PreservesLimitPair.iso.inv_comp_lift (F := (evaluation C D).obj X)
                    (f := G.inv) (h := 𝟙 G.X)]
      rw [evaluation_obj_map, ← NatTrans.comp_app, G.mul_left_inv, NatTrans.comp_app]
      simp only [evaluation_obj_obj]
      rw [← Category.assoc]
      suffices h : (default : G.X ⟶ ⊤_ (C ⥤ D)).app X =
          default ≫ (PreservesTerminal.iso ((evaluation C D).obj X)).inv by
        rw [h]
      ext j
      exact PEmpty.elim j.1
  }
  map f := {
    hom := G.X.map f
    one_hom := by
      simp only
      rw [Category.assoc, ← G.one.naturality, ← Category.assoc]
      rename_i X Y
      suffices h : ((PreservesTerminal.iso ((evaluation C D).obj X)).inv ≫ (⊤_ C ⥤ D).map f) =
          (PreservesTerminal.iso ((evaluation C D).obj Y)).inv by
        rw [h]
      ext j
      exact PEmpty.elim j.1
    mul_hom := by
      simp only
      rw [Category.assoc, ← G.mul.naturality, ← Category.assoc, ← Category.assoc]
      rename_i X Y
      suffices h : ((PreservesLimitPair.iso ((evaluation C D).obj X) G.X G.X).inv ≫ (G.X ⨯ G.X).map f) =
          (prod.map (G.X.map f) (G.X.map f) ≫ (PreservesLimitPair.iso
          ((evaluation C D).obj Y) G.X G.X).inv) by
        rw [h]
      simp only [evaluation_obj_obj, PreservesLimitPair.iso_inv, IsIso.eq_comp_inv, Category.assoc,
        IsIso.inv_comp_eq]
      rw [← evaluation_map_app, ← evaluation_map_app _ _ f G.X]
      exact (prodComparison_natTrans (α := (evaluation C D).map f) (X := G.X) (Y := G.X)).symm
  }
  map_id X := by
    ext; simp only [evaluation_obj_obj, prod.leftUnitor_hom, id_eq, evaluation_obj_map,
      NatTrans.id_app, NatTrans.comp_app, eq_mpr_eq_cast, prod.rightUnitor_hom, prod.associator_hom,
      Pi.id_apply, cast_eq, evaluation_map_app, CategoryTheory.Functor.map_id, GroupObject.id_hom']
  map_comp f g := by
      ext; simp only [evaluation_obj_obj, prod.leftUnitor_hom, id_eq, evaluation_obj_map,
      NatTrans.id_app, NatTrans.comp_app, eq_mpr_eq_cast, prod.rightUnitor_hom, prod.associator_hom,
      Pi.id_apply, cast_eq, evaluation_map_app, Functor.map_comp, GroupObject.comp_hom']
