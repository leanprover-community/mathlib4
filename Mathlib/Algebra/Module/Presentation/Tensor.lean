/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Presentation of the tensor product of two modules

Given presentations of two `A`-modules `M₁` and `M₂`, we obtain a presentation of `M₁ ⊗[A] M₂`.

-/

universe w w₁₀ w₁₁ w₂₀ w₂₁ u v₁ v₂

namespace Module

open TensorProduct

variable {A : Type u} [CommRing A] {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂]

namespace Relations

variable (relations₁ : Relations.{w₁₀, w₁₁} A) (relations₂ : Relations.{w₂₀, w₂₁} A)

/-- The tensor product of systems of linear equations. -/
@[simps]
noncomputable def tensor :
    Relations A where
  G := relations₁.G × relations₂.G
  R := Sum (relations₁.R × relations₂.G) (relations₁.G × relations₂.R)
  relation
    | .inl ⟨r₁, g₂⟩ => Finsupp.embDomain (Function.Embedding.sectL relations₁.G g₂)
        (relations₁.relation r₁)
    | .inr ⟨g₁, r₂⟩ => Finsupp.embDomain (Function.Embedding.sectR g₁ relations₂.G)
        (relations₂.relation r₂)

namespace Solution

variable {relations₁ relations₂} (solution₁ : relations₁.Solution M₁)
  (solution₂ : relations₂.Solution M₂)

/-- Given solutions in `M₁` and `M₂` to systems of linear equations, this is the obvious
solution to the tensor product of these systems in `M₁ ⊗[A] M₂`. -/
@[simps]
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

variable {solution₁ solution₂} (h₁ : solution₁.IsPresentation) (h₂ : solution₂.IsPresentation)

/-- The tensor product of two modules admits a presentation by generators and relations. -/
noncomputable def isPresentationCoreTensor :
    Solution.IsPresentationCore.{w} (solution₁.tensor solution₂) where
  desc s := uncurry _ _ _ _ (h₁.desc
    { var := fun g₁ ↦ h₂.desc
        { var := fun g₂ ↦ s.var ⟨g₁, g₂⟩
          linearCombination_var_relation := fun r₂ ↦ by
            erw [← Finsupp.linearCombination_embDomain A
              (Function.Embedding.sectR g₁ relations₂.G)]
            exact s.linearCombination_var_relation (.inr ⟨g₁, r₂⟩) }
      linearCombination_var_relation := fun r₁ ↦ h₂.postcomp_injective (by
        ext g₂
        dsimp
        erw [Finsupp.apply_linearCombination A (LinearMap.applyₗ (solution₂.var g₂))]
        have := s.linearCombination_var_relation (.inl ⟨r₁, g₂⟩)
        erw [Finsupp.linearCombination_embDomain] at this
        convert this
        ext g₁
        simp) })
  postcomp_desc _ := by aesop
  postcomp_injective h := curry_injective (h₁.postcomp_injective (by
    ext g₁ : 2
    refine h₂.postcomp_injective ?_
    ext g₂
    exact congr_var h ⟨g₁, g₂⟩))

include h₁ h₂ in
lemma IsPresentation.tensor : (solution₁.tensor solution₂).IsPresentation :=
  (isPresentationCoreTensor h₁ h₂).isPresentation

end Solution

end Relations

namespace Presentation

variable (pres₁ : Presentation.{w₁₀, w₁₁} A M₁) (pres₂ : Presentation.{w₂₀, w₂₁} A M₂)

/-- The presentation of the `A`-module `M₁ ⊗[A] M₂` that is deduced from
a presentation of `M₁` and a presentation of `M₂`. -/
@[simps!]
noncomputable def tensor : Presentation A (M₁ ⊗[A] M₂) where
  G := _
  R := _
  relation := _
  toSolution := pres₁.toSolution.tensor pres₂.toSolution
  toIsPresentation := pres₁.toIsPresentation.tensor pres₂.toIsPresentation

end Presentation

end Module
