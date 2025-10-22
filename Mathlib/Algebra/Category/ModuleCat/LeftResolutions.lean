/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.LeftResolutions.Basic

/-!
# Functorial projective resolutions of modules

The fact that a `R`-module `M` can be functorially written as a quotient of a
projective `R`-module is expressed as the definition `ModuleCat.projectiveResolutions`.
Using the construction in the file `Algebra.Homology.LeftResolutions.Basic`,
we may obtain a functor `(projectiveResolutions R).chainComplexFunctor` which
sends `M : ModuleCat R` to a projective resolution.

-/

universe u

variable (R : Type u) [Ring R]

namespace ModuleCat

open CategoryTheory Abelian

instance (X : Type u) : Projective ((free R).obj X) where
  factors {M N} f p hp := by
    rw [epi_iff_surjective] at hp
    obtain ⟨s, hs⟩ := hp.hasRightInverse
    exact ⟨freeDesc (fun x ↦ s (f (freeMk x))), by cat_disch⟩

/-- A `R`-module `M` can be functorially written as a quotient of a
projective `R`-module. -/
noncomputable def projectiveResolutions :
    LeftResolutions
      (ObjectProperty.ι (isProjective (ModuleCat.{u} R))) where
  F := ObjectProperty.lift _ (forget _ ⋙ free R) (by dsimp; infer_instance)
  π := (adj R).counit

end ModuleCat
