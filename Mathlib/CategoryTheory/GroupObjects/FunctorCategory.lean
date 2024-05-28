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
                  erw [← NatTrans.vcomp_app]
                  change (prod.map G.one (𝟙 G.X) ≫ G.mul).app X
                  rw [G.one_mul, prod.leftUnitor_hom]
      erw [PreservesLimitPair.iso_inv_snd]
      simp only [evaluation_obj_obj, prod.map_snd, Category.comp_id]
    mul_one := by
      with_panel_widgets [GoalTypePanel]
      simp only [evaluation_obj_obj, prod.rightUnitor_hom]
      rw [prod_map_comp_right_id_left, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      erw [PreservesLimitPair.iso.inv_natural (F := (evaluation C D).obj X) (f := 𝟙 G.X)
        (f' := G.one)]
      rw [Category.assoc]
      conv_lhs => congr; rfl; congr; rfl
                  erw [← NatTrans.vcomp_app]
                  change (prod.map (𝟙 G.X) G.one ≫ G.mul).app X
                  rw [G.mul_one, prod.rightUnitor_hom]
      erw [PreservesLimitPair.iso_inv_fst]
      simp only [evaluation_obj_obj, prod.map_fst, Category.comp_id]
    mul_assoc := by
      with_panel_widgets [GoalTypePanel]
      
      sorry
    mul_left_inv := sorry
  }
  map := sorry
