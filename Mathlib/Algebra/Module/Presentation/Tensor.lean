/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Free
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Presentation of the tensor product of two modules

-/

universe w₁₀ w₁₁ w₂₀ w₂₁ u v₁ v₂

namespace Module

open TensorProduct

variable {A : Type u} [CommRing A] {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂]

namespace Relations

variable (relations₁ : Relations.{w₁₀, w₁₁} A) (relations₂ : Relations.{w₂₀, w₂₁} A)

@[simps]
noncomputable def tensor :
    Relations A where
  G := relations₁.G × relations₂.G
  R := Sum (relations₁.R × relations₂.G) (relations₁.G × relations₂.R)
  relation r := match r with
    | .inl ⟨r₁, g₂⟩ => Finsupp.embDomain (Function.Embedding.sectl relations₁.G g₂)
        (relations₁.relation r₁)
    | .inr ⟨g₁, r₂⟩ => Finsupp.embDomain (Function.Embedding.sectr g₁ relations₂.G)
        (relations₂.relation r₂)

namespace Solution

variable {relations₁ relations₂} (solution₁ : relations₁.Solution M₁)
  (solution₂ : relations₂.Solution M₂)

noncomputable def tensor : (relations₁.tensor relations₂).Solution (M₁ ⊗[A] M₂) where
  var := fun ⟨g₁, g₂⟩ => solution₁.var g₁ ⊗ₜ solution₂.var g₂
  linearCombination_var_relation := by
    rintro (⟨r₁, g₂⟩ | ⟨g₁, r₂⟩)
    · dsimp
      rw [Finsupp.linearCombination_embDomain]
      exact (solution₁.postcomp (curry (TensorProduct.comm A M₂ M₁).toLinearMap
        (solution₂.var g₂))).linearCombination_var_relation r₁
    · dsimp
      rw [Finsupp.linearCombination_embDomain]
      exact (solution₂.postcomp (curry .id (solution₁.var g₁))).linearCombination_var_relation r₂

end Solution

end Relations

namespace Presentation

variable (pres₁ : Presentation.{w₁₀, w₁₁} A M₁) (pres₂ : Presentation.{w₂₀, w₂₁} A M₂)

@[simps!]
noncomputable def tensor : Presentation A (M₁ ⊗[A] M₂) where
  toSolution := pres₁.toSolution.tensor pres₂.toSolution
  toIsPresentation := sorry

end Presentation

end Module
