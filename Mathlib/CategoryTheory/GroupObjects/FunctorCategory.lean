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

example : IsTerminal ((Functor.const C).obj (⊤_ D)) := by
  apply IsTerminal.ofUniqueHom; swap
  · intro F
    exact
     {app := by
       intro X
       simp only [Functor.const_obj_obj]
       exact default}
  · intro F α; ext X
    simp only [Functor.const_obj_obj, id_eq]
    convert Subsingleton.elim (α.app X) default
    simp only [Functor.const_obj_obj]; exact inferInstance

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
      erw [PreservesLimitPair.iso.inv_natural (F := (evaluation C D).obj X) (f := G.one)
        (f' := 𝟙 G.X)]
      rw [Category.assoc]
      conv_lhs => congr; rfl; congr; rfl
                  erw [← NatTrans.comp_app]
                  rw [G.one_mul, prod.leftUnitor_hom]
      erw [PreservesLimitPair.iso_inv_snd]
      simp only [evaluation_obj_obj, prod.map_snd, Category.comp_id]
    mul_one := by
      simp only [evaluation_obj_obj, prod.rightUnitor_hom]
      rw [prod_map_comp_right_id_left, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      erw [PreservesLimitPair.iso.inv_natural (F := (evaluation C D).obj X) (f := 𝟙 G.X)
        (f' := G.one)]
      rw [Category.assoc]
      conv_lhs => congr; rfl; congr; rfl
                  erw [← NatTrans.comp_app]
                  rw [G.mul_one, prod.rightUnitor_hom]
      erw [PreservesLimitPair.iso_inv_fst]
      simp only [evaluation_obj_obj, prod.map_fst, Category.comp_id]
    mul_assoc := by
      rw [prod_map_comp_left_id_right]
      slice_lhs 2 3 => erw [PreservesLimitPair.iso.inv_natural (F := ((evaluation C D).obj X))
                         (f := G.mul) (f' := 𝟙 G.X)]
      slice_lhs 3 4 => erw [← NatTrans.comp_app]; rw [G.mul_assoc]
      rw [prod_map_comp_right_id_left]
      slice_rhs 3 4 => erw [PreservesLimitPair.iso.inv_natural (F := ((evaluation C D).obj X))
                         (f := 𝟙 G.X) (f' := G.mul)]
      rw [NatTrans.comp_app, ← Category.assoc, ← Category.assoc]
      conv_lhs => rw [← evaluation_obj_map, Category.assoc _
        (PreservesLimitPair.iso ((evaluation C D).obj X) (G.X ⨯ G.X) G.X).inv _]
      erw [PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X
        ((CategoryTheory.evaluation C D).obj X)]
      simp only [evaluation_obj_obj, prod.associator_hom, Pi.id_apply, prod.lift_map_assoc,
        Category.comp_id, NatTrans.comp_app, Category.assoc, evaluation_obj_map]
    mul_left_inv := by
      rw [← Category.assoc]
      erw [PreservesLimitPair.iso.inv_comp_lift (F := (evaluation C D).obj X) (f := G.inv)
        (h := 𝟙 G.X)]
      rw [evaluation_obj_map, ← NatTrans.comp_app, G.mul_left_inv, NatTrans.comp_app]
      simp only [evaluation_obj_obj]
      rw [← Category.assoc]
      congr 1
      ext j
      exact PEmpty.elim j.1
  }
  map f := {
    hom := G.X.map f
    one_hom := by
      simp only
      rw [Category.assoc, ← G.one.naturality, ← Category.assoc]
      congr 1
      ext j
      exact PEmpty.elim j.1
    mul_hom := by
      simp only
      rw [Category.assoc, ← G.mul.naturality, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [evaluation_obj_obj, PreservesLimitPair.iso_inv, IsIso.eq_comp_inv, Category.assoc,
        IsIso.inv_comp_eq]
      rw [← evaluation_map_app, ← evaluation_map_app _ _ f G.X]
      exact (prodComparison_natTrans (α := (evaluation C D).map f) (X := G.X) (Y := G.X)).symm
  }
  map_id X := by
    ext; rw [G.X.map_id]
  map_comp f g := by
    ext
    rw [G.X.map_comp]
