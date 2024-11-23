/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn, Amelia Livingston
-/

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms

/-!
# The category of abelian groups satisfies Grothendieck's axiom AB5

-/

universe u

open CategoryTheory Limits

instance {J C : Type*} [Category J] [Category C] [HasColimitsOfShape J C] [Preadditive C] :
    (colim (J := J) (C := C)).Additive where

variable {J : Type u} [SmallCategory J] [IsFiltered J]

noncomputable instance :
    (colim (J := J) (C := AddCommGrp.{u})).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS ↦ by
    replace hS := fun j => hS.map ((evaluation _ _).obj j)
    simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
    intro x (hx : _ = _)
    dsimp at hx
    rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
    erw [← comp_apply, colimit.ι_map, comp_apply,
      ← map_zero (by exact colimit.ι S.X₃ j : (S.X₃).obj j →+ ↑(colimit S.X₃))] at hx
    rcases Concrete.colimit_exists_of_rep_eq.{u, u, u} S.X₃ _ _ hx
      with ⟨k, e₁, e₂, hk : _ = S.X₃.map e₂ 0⟩
    rw [map_zero, ← comp_apply, ← NatTrans.naturality, comp_apply] at hk
    rcases hS k hk with ⟨t, ht⟩
    use colimit.ι S.X₁ k t
    erw [← comp_apply, colimit.ι_map, comp_apply, ht]
    exact colimit.w_apply S.X₂ e₁ y)

noncomputable instance :
    PreservesFiniteLimits <| colim (J := J) (C := AddCommGrp.{u}) := by
  apply Functor.preservesFiniteLimits_of_preservesHomology

instance : HasFilteredColimits (AddCommGrp.{u}) where
  HasColimitsOfShape := inferInstance

noncomputable instance : AB5 (AddCommGrp.{u}) where
  preservesFiniteLimits := fun _ => inferInstance
