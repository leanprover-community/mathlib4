import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

universe w v u

namespace CategoryTheory

open Limits



variable {C : Type u} [Category.{v} C]

section SigmaPi

variable [HasZeroMorphisms C] {α : Type w} [DecidableEq α] (f : α → C) [HasCoproduct f]

noncomputable def Sigma.π (i : α) : ∐ f ⟶ f i := by
  classical exact Limits.Sigma.desc (Function.update (fun _ ↦ 0) i (𝟙 _))

@[reassoc (attr := simp)]
lemma Sigma.ι_π_eq_id (i : α) : Sigma.ι f i ≫ Sigma.π f i = 𝟙 _ := by
  simp [Sigma.π]

lemma Sigma.ι_π_of_ne {i j : α} (h : i ≠ j) : Sigma.ι f i ≫ Sigma.π f j = 0 := by
  classical
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]
theorem Sigma.ι_π (i j : α) :
    Sigma.ι f i ≫ Sigma.π f j = if h : i = j then eqToHom (congrArg f h) else 0 := by
  split_ifs with h
  · subst h
    simp
  · simp [Sigma.ι_π_of_ne f h]

end SigmaPi

noncomputable section

variable [Preadditive C]
variable {α : Type w} [HasColimitsOfShape (Discrete α) C] [HasFiniteCoproducts C]

open Classical

def myOtherCocone (f : α → C) :
    Cocone (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι :=
  { app S :=  ∑ a : S, Sigma.π _ a ≫ Sigma.ι f a.1.as
    naturality S₁ S₂ f := by {
      rcases f with ⟨⟨f⟩⟩
      change _ ⊆ _ at f
      simp only [CoproductsFromFiniteFiltered.liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
        Functor.const_obj_obj, Finset.le_eq_subset,
        CoproductsFromFiniteFiltered.liftToFinsetObj_map, Finset.univ_eq_attach,
        Functor.const_obj_map, Category.comp_id]
      ext ⟨b, hb⟩
      simp [Preadditive.comp_sum, Sigma.ι_π_assoc, dite_comp, zero_comp, Finset.sum_dite_eq]
    } }

def isColimit (f : α → C) : IsColimit (myOtherCocone f) := sorry

end

end CategoryTheory
