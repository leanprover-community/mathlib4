/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Implicit function theorem: curried bivariate case

In this specialization of the implicit function theorem, to an equation involving a curried
bivariate function, we make assumptions on each of the partial derivatives individually.
Consequently it requires import of results depending on the mean value theorem, and is sequestered
to its own file apart from `Implicit.lean`.

We consider the common case of bivariate `f`, the second of whose partial derivatives is invertible.
Where further conditions are satisfied we may obtain `ψ` such that for `(y₁, y₂)` in a neighbourhood
of `(x₁, x₂)` we have `f y₁ y₂ = f x₁ x₂ ↔ ψ y₁ = y₂`. For uncurried `f` this functionality was
implemented by `HasStrictFDerivAt.implicitFunOfProdDomain` in `Implicit.lean`. For curried `f` it is
implemented by `implicitFunOfBivariate` here.
-/

open Filter
open scoped Topology

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂] [CompleteSpace E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {x₁ : E₁} {x₂ : E₂} {f : E₁ → E₂ → F}
  {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} (cf₁ : ContinuousAt ↿f₁ (x₁, x₂))
  (df₁ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f · y.2) (f₁ y.1 y.2) y.1)
  {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousAt ↿f₂ (x₁, x₂))
  (df₂ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f y.1 ·) (f₂ y.1 y.2) y.2)
  {f₂x : E₂ ≃L[𝕜] F} (hf₂x : f₂ x₁ x₂ = f₂x)

/-- Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `(x₁, x₂)`. -/
noncomputable def implicitFunOfBivariate : E₁ → E₂ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.implicitFunOfProdDomain

theorem hasStrictFDerivAt_implicitFunOfBivariate :
    HasStrictFDerivAt (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x) (-f₂x.symm ∘L f₁ x₁ x₂) x₁ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂
    |>.hasStrictFDerivAt_implicitFunOfProdDomain

theorem image_eq_iff_implicitFunOfBivariate :
    ∀ᶠ y in 𝓝 (x₁, x₂), ↿f y = f x₁ x₂ ↔ implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x y.1 = y.2 :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.image_eq_iff_implicitFunOfProdDomain

theorem tendsto_implicitFunOfBivariate :
    Tendsto (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x) (𝓝 x₁) (𝓝 x₂) :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.tendsto_implicitFunOfProdDomain

theorem image_implicitFunOfBivariate :
    ∀ᶠ u in 𝓝 x₁, f u (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x u) = f x₁ x₂ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.image_implicitFunOfProdDomain
