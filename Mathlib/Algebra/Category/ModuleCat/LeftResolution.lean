
/-!
# Functorial projective resolutions of modules

The fact that an `R`-module `M` can be functorially written as a quotient of a
projective `R`-module is expressed as the definition `ModuleCat.projectiveResolution`.
Using the construction in the file `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`,
we may obtain a functor `(projectiveResolution R).chainComplexFunctor` which
sends `M : ModuleCat R` to a projective resolution.

-/

@[expose] public section

universe u

variable (R : Type u) [Ring R]

namespace ModuleCat

open CategoryTheory Abelian

instance (X : Type u) : Projective ((free R).obj X) where
  factors {M N} f p hp := by
    rw [epi_iff_surjective] at hp
    obtain ⟨s, hs⟩ := hp.hasRightInverse
    exact ⟨freeDesc (fun x ↦ s (f (freeMk x))), by cat_disch⟩

/-- An `R`-module `M` can be functorially written as a quotient of a
projective `R`-module. -/
noncomputable def projectiveResolution :
    LeftResolution (ObjectProperty.ι (isProjective (ModuleCat.{u} R))) where
  F := ObjectProperty.lift _ (forget _ ⋙ free R) (by dsimp; infer_instance)
  π := (adj R).counit

end ModuleCat
