/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.OfProdDomain
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Implicit function theorem — curried bivariate

In this specialization of the implicit function theorem, to an equation involving a curried
bivariate function, we make assumptions on each of the partial derivatives individually.
Consequently it requires import of results depending on the mean value theorem, and is sequestered
to its own file apart from `Implicit.lean`.

We consider the common case of bivariate `f`, the second of whose partial derivatives is invertible.
Where further conditions are satisfied we may obtain `ψ` such that for `(v₁, v₂)` in a neighbourhood
of `(u₁, u₂)` we have `f v₁ v₂ = f u₁ u₂ ↔ ψ v₁ = v₂`. For uncurried `f` this functionality was
implemented by `HasStrictFDerivAt.implicitFunOfProdDomain` in `Implicit.lean`. For curried `f` it is
implemented by `implicitFunOfBivariate` here.
-/

@[expose] public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {u₁ : E₁} {u₂ : E₂}
  {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} {f₂ : E₁ → E₂ → E₂ →L[𝕜] F}
  (df₁ : ∀ᶠ v in 𝓝 (u₁, u₂), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
  (df₂ : ∀ᶠ v in 𝓝 (u₁, u₂), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
  (cf₁ : ContinuousAt ↿f₁ (u₁, u₂)) (cf₂ : ContinuousAt ↿f₂ (u₁, u₂))
  (if₂ : (f₂ u₁ u₂).IsInvertible)

/-- Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `(u₁, u₂)`. -/
noncomputable def implicitFunctionOfBivariate : E₁ → E₂ :=
  HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) <| by simpa using if₂

theorem image_implicitFunctionOfBivariate :
    ∀ᶠ x in 𝓝 u₁, f x (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂ x) = f u₁ u₂ := by
  simpa using HasStrictFDerivAt.image_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) <| by simpa using if₂

theorem image_eq_iff_implicitFunctionOfBivariate :
    ∀ᶠ v in 𝓝 (u₁, u₂),
      ↿f v = f u₁ u₂ ↔ implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂ v.1 = v.2 := by
  simpa using HasStrictFDerivAt.image_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) <| by simpa using if₂

theorem hasStrictFDerivAt_implicitFunctionOfBivariate :
    HasStrictFDerivAt (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂)
      (-(f₂ u₁ u₂).inverse ∘L f₁ u₁ u₂) u₁ := by
  simpa using HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) <| by simpa using if₂

theorem tendsto_implicitFunctionOfBivariate :
    Tendsto (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂) (𝓝 u₁) (𝓝 u₂) := by
  simpa using HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) <| by simpa using if₂

end
