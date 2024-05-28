import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts


universe u v u' v'

open CategoryTheory Limits

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

    mul_one := sorry
    mul_assoc := sorry
    mul_left_inv := sorry
  }
  map := sorry
