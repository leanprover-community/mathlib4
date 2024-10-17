/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong
-/
import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Process.Filtration

/-!
# Family of kernels consistent with respect to a filtration
-/

open ProbabilityTheory

namespace MeasureTheory.Filtration
variable {X P E : Type*} {mX : MeasurableSpace X} {mE : MeasurableSpace E} [PartialOrder P]

/-- A family of kernels `γ` on `X` indexed by a partial order `P` is consistent under conditioning
if `γ p₂ ∘ₖ γ p₁ = γ p₁` whenever `p₁ ≤ p₂`. -/
def IsConsistentKernel (mXs : Filtration P mX) (γ : ∀ p, Kernel[mXs p] X X) : Prop :=
  ∀ ⦃p₁ p₂⦄, p₁ ≤ p₂ → (γ p₂).comap id (mXs.le p₂) ∘ₖ γ p₁ = γ p₁

end MeasureTheory.Filtration
