/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
/-!

# Grothendieck axioms for the category of sheaves for the extensive topology
-/

namespace CategoryTheory

open CategoryTheory Limits Sheaf GrothendieckTopology Opposite extensiveTopology

variable {A C J : Type*} [Category A] [Category C] [Category J] [FinitaryExtensive C]
    [HasColimitsOfShape J A] [ABOfShape J A]

variable (A) in
abbrev extensiveTopology.ev (S : C) : Sheaf (extensiveTopology C) A ⥤ A :=
  (sheafSections (extensiveTopology C) A).obj (op S)

instance [HasLimitsOfShape J A]
  [HasWeakSheafify (extensiveTopology C) A] (S : C) : PreservesLimitsOfShape J (ev A S) := by
  have : (sheafToPresheaf (extensiveTopology C) A).IsRightAdjoint :=
    (sheafificationAdjunction _ _).isRightAdjoint
  change PreservesLimitsOfShape _ ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj _)
  infer_instance

instance (S : C) : PreservesColimits (ev A S) := sorry

end CategoryTheory
