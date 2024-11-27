/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
/-!

# Grothendieck axioms for the category of sheaves for the extensive topology
-/

namespace CategoryTheory

open CategoryTheory Limits Sheaf GrothendieckTopology Opposite extensiveTopology

section

variable {A C J : Type*} [Category A] [Category C] [Category J] [FinitaryExtensive C]
    [IsFiltered J] [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasSheafify (extensiveTopology C) A] [Abelian A] [HasFiniteLimits A]

instance : HasExactColimitsOfShape J (Sheaf (extensiveTopology C) A) := by
  apply ( config := { allowSynthFailures := true } ) hasExactColimitsOfShape_of_preservesMono
  constructor
  intro X Y f hf
  rw [NatTrans.mono_iff_mono_app] at hf
  have : ∀ k, Mono (f.app k).val := fun _ ↦ inferInstanceAs (Mono ((sheafToPresheaf _ _).map _))
  simp_rw [NatTrans.mono_iff_mono_app] at this
  sorry

variable (A) in
abbrev extensiveTopology.ev (S : C) : Sheaf (extensiveTopology C) A ⥤ A :=
  (sheafSections (extensiveTopology C) A).obj (op S)

instance [HasLimitsOfShape J A]
  [HasWeakSheafify (extensiveTopology C) A] (S : C) : PreservesLimitsOfShape J (ev A S) := by
  have : (sheafToPresheaf (extensiveTopology C) A).IsRightAdjoint :=
    (sheafificationAdjunction _ _).isRightAdjoint
  change PreservesLimitsOfShape _ ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj _)
  infer_instance

instance (S : C) : PreservesFilteredColimits (ev A S) where
  preserves_filtered_colimits J _ _ := {
    preservesColimit := fun {K} ↦ {
      preserves := fun {c} hc ↦ by
        refine ⟨?_⟩
        sorry } }

end

-- section

-- variable {A C : Type*} [Category A] [Category C] [FinitaryExtensive C]
--     [HasFilteredColimits A] [AB5 A]

-- instance : AB5 (Sheaf (extensiveTopology C) A) := by sorry

-- end

end CategoryTheory
