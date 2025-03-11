/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
/-!
# Constructing a colimit cocone over a functor lifted to finite sets on a discrete category

-/

universe w v u

namespace CategoryTheory

namespace Preadditive

open Limits


noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {α : Type w} [HasColimitsOfShape (Discrete α) C] [HasFiniteCoproducts C]

open Classical

/-- In a preadditive category `C`, we can construct a cocone over the any functor which results
from lifting a functor `Discrete α ⥤ C` to `Finset (Discrete α) ⥤ C`. -/
def coconeLiftToFinsetObj (f : α → C) :
    Cocone (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι := { app S :=  ∑ a : S, Sigma.π _ a ≫ Sigma.ι f a.1.as
         naturality S₁ S₂ f := Sigma.hom_ext _ _ fun ⟨b, hb⟩ => by
           simp [Preadditive.comp_sum, Sigma.ι_π_assoc, dite_comp] }

@[reassoc (attr := simp)]
theorem ι_coconeLiftToFinsetObj_app (f : α → C) {S : Finset (Discrete α)} {a : α} (ha : ⟨a⟩ ∈ S) :
    Sigma.ι (fun _ ↦ f _) ⟨⟨a⟩, ha⟩ ≫ (coconeLiftToFinsetObj f).ι.app S = Sigma.ι f a := by
  simp [coconeLiftToFinsetObj, Preadditive.comp_sum, Sigma.ι_π_assoc, dite_comp]

/-- The cocone constructed in `Preadditive.coconeLiftToFinsetObj` is a colimit cocone. -/
def isColimit (f : α → C) : IsColimit (coconeLiftToFinsetObj f) where
  desc s := Sigma.desc fun a =>
    (Sigma.ι (fun (x : ({ ⟨a⟩ } : Finset (Discrete α))) ↦ f x.1.as)
      ⟨⟨a⟩, Finset.mem_singleton.mpr rfl⟩) ≫ (by exact s.ι.app { ⟨a⟩ })
  uniq s m S := by
    apply Sigma.hom_ext
    intro a
    simp [← S { ⟨a⟩ }]
  fac s S := by
    apply Sigma.hom_ext
    intro ⟨⟨b⟩, hb⟩
    simp [← Cocone.w s (LE.le.hom (Finset.singleton_subset_iff.mpr hb))]

end

end Preadditive

end CategoryTheory
