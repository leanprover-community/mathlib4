/-
Copyright (c) 2026 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.Implicit

/-!
# Implicit function theorem

We consider the common case of bivariate `f`, the second of whose partial derivatives is invertible.
Then we may apply the general theorem to obtain `ψ` such that for `(v₁, v₂)` in a neighbourhood of
`(u₁, u₂)` we have `f (v₁, v₂) = f (u₁, u₂) ↔ ψ v₁ = v₂`.

## Tags

implicit function, inverse function
-/

@[expose] public section ProdDomain

/-!
### Case of a product space domain

Given strictly differentiable `f : E₁ × E₂ → F`, the second of whose partial derivatives is known to
be invertible, we may construct an `ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁` with `f` as its `leftFun`
and `Prod.fst : E₁ × E₂ → E₁` as its `rightFun`. We may then extract `ψ : E₁ → E₂` with the desired
properties. This functionality is wrapped by `HasStrictFDerivAt.implicitFunctionOfProdDomain`. A
formula for the first derivative of `ψ` is immediately derived.
-/

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

/-- Given `HasStrictFDerivAt f f' u` with `f' : E₁ × E₂ →L[𝕜] F` decomposing into `f₁ : E₁ →L[𝕜] F`
and `f₂ : E₂ →L[𝕜] F`, the latter invertible, we prove that the kernels of `f'` and
`ContinuousLinearMap.fst 𝕜 E₁ E₂` are complementary and construct an object of type
`ImplicitFunctionData` thereby permitting use of the general machinery provided above. -/
def implicitFunctionDataOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f' ∘L .inr _ _ _).range ≤ f'.range := LinearMap.range_comp_le_range _ _
    rwa [LinearMap.range_eq_top.mpr if₂.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      obtain ⟨y, hy⟩ := if₂.surjective (f' v)
      use v - (0, y), (0, y)
      aesop

/-- Implicit function `ψ : E₁ → E₂` associated with the (uncurried) bivariate function
`f : E₁ × E₂ → F` at `u`. -/
noncomputable def implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  fun x => ((dfu.implicitFunctionDataOfProdDomain if₂).implicitFunction (f u) x).2

theorem hasStrictFDerivAt_implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (dfu.implicitFunctionOfProdDomain if₂)
      (-(f' ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f' ∘L .inl 𝕜 E₁ E₂)) u.1 := by
  have : f' ∘L (.prod (.id _ _) (-(f' ∘L .inr _ _ _).inverse ∘L (f' ∘L .inl _ _ _))) = 0 := by
    ext x
    rw [f'.comp_apply, ← f'.comp_inl_add_comp_inr]
    simp [map_neg, if₂]
  exact ((dfu.implicitFunctionDataOfProdDomain if₂).hasStrictFDerivAt_implicitFunction _
    (ContinuousLinearMap.fst_comp_prod _ _) this).snd

theorem image_eq_iff_implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ dfu.implicitFunctionOfProdDomain if₂ v.1 = v.2 := by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction] with y h h'
  exact Iff.trans h ⟨congrArg _, by aesop⟩

theorem tendsto_implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    Tendsto (dfu.implicitFunctionOfProdDomain if₂) (𝓝 u.1) (𝓝 u.2) := by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂).continuousAt.tendsto
  rwa [(dfu.image_eq_iff_implicitFunctionOfProdDomain if₂).self_of_nhds.mp rfl] at this

theorem image_implicitFunctionOfProdDomain {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (dfu : HasStrictFDerivAt f f' u) (if₂ : (f' ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, dfu.implicitFunctionOfProdDomain if₂ x) = f u := by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂
  set ψ := dfu.implicitFunctionOfProdDomain if₂
  suffices ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.image_eq_iff_implicitFunctionOfProdDomain if₂

end HasStrictFDerivAt

end ProdDomain
