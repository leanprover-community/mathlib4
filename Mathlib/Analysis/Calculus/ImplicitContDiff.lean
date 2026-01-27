/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.OfProdDomain
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Implicit function theorem

In this file, we apply the generalised implicit function theorem to the more familiar case and show
that the implicit function preserves the smoothness class of the implicit equation.

Let `E₁`, `E₂`, and `F` be real or complex Banach spaces. Let `f : E₁ × E₂ → F` be a function that
is $C^n$ at a point `(u₁, u₂) : E₁ × E₂`, where `n ≥ 1`. Let `f'` be the derivative of `f` at
`(u₁, u₂)`. If the map `y ↦ f' (0, y)` is a Banach space isomorphism, then there exists a function
`ψ : E₁ → E₂` such that `ψ u₁ = u₂`, and `f (x, ψ x) = f (u₁, u₂)` holds for all `x` in a
neighbourhood of `u₁`. Furthermore, `ψ` is $C^n$ at `u₁`.

## TODO
* Faà di Bruno.

## Tags

implicit function, inverse function
-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace ImplicitFunctionData

/-- The implicit function defined by a $C^n$ implicit equation is $C^n$. This applies to the general
form of the implicit function theorem. -/
theorem contDiff_implicitFunction {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : WithTop ℕ∞}
    (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (hn : n ≠ 0) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction, Function.uncurry_curry, toOpenPartialHomeomorph,
    ← HasStrictFDerivAt.localInverse_def]
  exact (hl.prodMk hr).to_localInverse (φ.hasStrictFDerivAt |>.hasFDerivAt) hn

end ImplicitFunctionData

open scoped Topology

namespace ContDiffAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {n : WithTop ℕ∞}

/-- Implicit function `ψ` defined by `f (x, ψ x) = f u`. -/
noncomputable def implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
theorem image_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, cdf.implicitFunction pn if₂ x) = f u :=
  (cdf.hasStrictFDerivAt pn).image_implicitFunctionOfProdDomain if₂

theorem eventually_implicitFunction_apply_eq
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ cdf.implicitFunction pn if₂ v.1 = v.2 :=
  (cdf.hasStrictFDerivAt pn).image_eq_iff_implicitFunctionOfProdDomain if₂

/-- If the implicit equation `f` is $C^n$ at `(u₁, u₂)`, then its implicit function `ψ` around `u₁`
is also $C^n$ at `u₁`. -/
theorem contDiffAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ContDiffAt 𝕜 n (cdf.implicitFunction pn if₂) u.1 := by
  have := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
    |>.contDiff_implicitFunction cdf contDiffAt_fst pn
  unfold implicitFunction HasStrictFDerivAt.implicitFunctionOfProdDomain
  fun_prop

theorem hasStrictFDerivAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (cdf.implicitFunction pn if₂)
      (-(fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (fderiv 𝕜 f u ∘L .inl 𝕜 E₁ E₂)) u.1 :=
  (cdf.hasStrictFDerivAt pn).hasStrictFDerivAt_implicitFunctionOfProdDomain if₂

end ContDiffAt

/-- A predicate stating the sufficient conditions on an implicit equation `f : E₁ × E₂ → F` that
will lead to a $C^n$ implicit function `ψ : E₁ → E₂`. -/
@[deprecated "ContDiffAt.implicitFunction does not require this" (since := "2026-01-27")]
structure IsContDiffImplicitAt (n : WithTop ℕ∞) (f : E₁ × E₂ → F) (f' : E₁ × E₂ →L[𝕜] F)
    (u : E₁ × E₂) : Prop where
  hasFDerivAt : HasFDerivAt f f' u
  contDiffAt : ContDiffAt 𝕜 n f u
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))
  ne_zero : n ≠ 0

namespace IsContDiffImplicitAt

@[deprecated (since := "2026-01-27")]
alias implicitFunction := ContDiffAt.implicitFunction

@[deprecated (since := "2026-01-27")]
alias apply_implicitFunction := ContDiffAt.image_implicitFunction

@[deprecated (since := "2026-01-27")]
alias eventually_implicitFunction_apply_eq := ContDiffAt.eventually_implicitFunction_apply_eq

@[deprecated (since := "2026-01-27")]
alias contDiffAt_implicitFunction := ContDiffAt.contDiffAt_implicitFunction

end IsContDiffImplicitAt

end
