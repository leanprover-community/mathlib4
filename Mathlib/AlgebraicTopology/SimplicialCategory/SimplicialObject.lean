/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.CategoryTheory.Functor.FunctorHom

/-!
# The category of simplicial objects is simplicial

In `CategoryTheory.Functor.FunctorHom`, it was shown that a category of functors
`C ⥤ D` is enriched over a suitable category `C ⥤ Type _` of functors to types.

In this file, we deduce that `SimplicialObject D` is enriched over `SSet.{v} D`
(when `D : Type u` and `[Category.{v} D]`) and that `SimplicialObject D`
is actually a simplicial category. In particular, the category of simplicial
sets is a simplicial category.

-/

universe v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

namespace SimplicialObject

open Simplicial

noncomputable instance : EnrichedCategory SSet.{v} (SimplicialObject D)  :=
  inferInstanceAs (EnrichedCategory (SimplexCategoryᵒᵖ ⥤ Type v) (SimplexCategoryᵒᵖ ⥤ D))

/-- If `K` and `L` are simplicial objects, the zero-simplicies of the simplicial
hom from `K` to `L` identifies to `K ⟶ L`. -/
def sHom₀Equiv (K L : SimplicialObject D) :
    EnrichedCategory.Hom (V := SSet.{v}) K L _[0] ≃ (K ⟶ L) where
  toFun x :=
    { app := fun Δ ↦ x.app Δ (SimplexCategory.const _ _ 0).op
      naturality := fun Δ Δ' f ↦ by rw [← x.naturality f]; rfl }
  invFun φ :=
    { app := fun Δ _ ↦ φ.app Δ
      naturality := fun {Δ Δ'} f ⟨s⟩ ↦ by
        obtain rfl := Subsingleton.elim s (SimplexCategory.const _ _ 0)
        simp only [NatTrans.naturality] }
  left_inv x := Functor.functorHom_ext (fun Δ ⟨s⟩ ↦ by
    obtain rfl := Subsingleton.elim s (SimplexCategory.const _ _ 0)
    rfl)
  right_inv _ := rfl

noncomputable instance : SimplicialCategory (SimplicialObject D) where
  homEquiv K L :=
    (sHom₀Equiv K L).symm.trans (SSet.unitHomEquiv (EnrichedCategory.Hom K L)).symm

noncomputable instance : SimplicialCategory SSet.{v} :=
  inferInstanceAs (SimplicialCategory (SimplicialObject (Type v)))

end SimplicialObject

end CategoryTheory
