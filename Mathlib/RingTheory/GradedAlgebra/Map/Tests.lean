import Mathlib
import Mathlib.RingTheory.GradedAlgebra.Map.DecompositionMap_SetLike

section ModuleDecomposition
/- Sanity check:  decomposition for modules should not be automatic -/
universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
variable (f : ι₁ → ι₂)
variable {R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] (ℳ : ι₁ → Submodule R M)
variable [DirectSum.Decomposition ℳ]
#check (inferInstance : (DirectSum.Decomposition (Decomposition.map f ℳ)))
end ModuleDecomposition

#min_imports
