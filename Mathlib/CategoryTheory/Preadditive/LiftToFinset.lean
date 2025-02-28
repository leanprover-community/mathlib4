import Mathlib.CategoryTheory.Limits.Constructions.Filtered
--import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

universe w v u

namespace CategoryTheory

open Limits

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {α : Type w} [HasColimitsOfShape (Discrete α) C] [HasFiniteCoproducts C]

open Classical

@[simps]
def coconeLiftToFinsetObj (f : α → C) :
    Cocone (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι := { app S :=  ∑ a : S, Sigma.π _ a ≫ Sigma.ι f a.1.as
         naturality S₁ S₂ f := Sigma.hom_ext _ _ fun ⟨b, hb⟩ => by
           simp [Preadditive.comp_sum, Sigma.ι_π_assoc, dite_comp] }

def isColimit (f : α → C) : IsColimit (coconeLiftToFinsetObj f) where
  desc s := by
    simp
    apply Sigma.desc
    intro a
    have sι := s.ι.app
    dsimp at sι
    sorry
  uniq := sorry


#check Sigma.curry_single

end

end CategoryTheory
