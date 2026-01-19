/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Implicit
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
* Local uniqueness of the implicit function
* Derivative of the implicit function

## Tags

implicit function, inverse function
-/

@[expose] public section

variable {𝕜 E₁ E₂ F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

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

/-- Implicit function `ψ` defined by `f (x, ψ x) = f u`. -/
noncomputable def implicitFunction {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : WithTop ℕ∞}
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
theorem image_implicitFunction {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : WithTop ℕ∞}
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, cdf.implicitFunction pn if₂ x) = f u :=
  (cdf.hasStrictFDerivAt pn).image_implicitFunctionOfProdDomain if₂

theorem eventually_implicitFunction_apply_eq {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : WithTop ℕ∞}
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ cdf.implicitFunction pn if₂ v.1 = v.2 :=
  (cdf.hasStrictFDerivAt pn).image_eq_iff_implicitFunctionOfProdDomain if₂

/-- If the implicit equation `f` is $C^n$ at `(u₁, u₂)`, then its implicit function `ψ` around `u₁`
is also $C^n$ at `u₁`. -/
theorem contDiffAt_implicitFunction {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : WithTop ℕ∞}
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ContDiffAt 𝕜 n (cdf.implicitFunction pn if₂) u.1 := by
  have := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
            |>.contDiff_implicitFunction cdf contDiffAt_fst pn
  unfold implicitFunction HasStrictFDerivAt.implicitFunctionOfProdDomain
  fun_prop

end ContDiffAt

end

@[expose] public section

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

open Filter

open scoped Topology

/-- A predicate stating the sufficient conditions on an implicit equation `f : E × F → G` that will
lead to a $C^n$ implicit function `φ : E → F`. -/
@[deprecated "ContDiffAt.implicitFunction does not require this" (since := "2026-01-19")]
structure IsContDiffImplicitAt (n : WithTop ℕ∞) (f : E × F → G) (f' : E × F →L[𝕜] G) (a : E × F) :
    Prop where
  hasFDerivAt : HasFDerivAt f f' a
  contDiffAt : ContDiffAt 𝕜 n f a
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E F))
  ne_zero : n ≠ 0

namespace IsContDiffImplicitAt

variable
  {n : WithTop ℕ∞} {f : E × F → G} {f' : E × F →L[𝕜] G} {a : E × F}

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
@[deprecated IsContDiffImplicitAt.ne_zero (since := "2025-12-22")]
theorem one_le (h : IsContDiffImplicitAt n f f' a) : 1 ≤ n := by
  rw [ENat.one_le_iff_ne_zero_withTop]
  exact h.ne_zero

/-- We record the parameters of our specific case in order to apply the general implicit function
theorem. -/
def implicitFunctionData (h : IsContDiffImplicitAt n f f' a) :
    ImplicitFunctionData 𝕜 (E × F) E G where
  leftFun := Prod.fst
  leftDeriv := ContinuousLinearMap.fst 𝕜 E F
  rightFun := f
  rightDeriv := f'
  pt := a
  hasStrictFDerivAt_leftFun := by fun_prop
  hasStrictFDerivAt_rightFun := h.contDiffAt.hasStrictFDerivAt' h.hasFDerivAt h.ne_zero
  range_leftDeriv := LinearMap.range_eq_top_of_surjective _ fun x ↦ ⟨(x, 0), rfl⟩
  range_rightDeriv := by
    apply top_unique
    rw [← LinearMap.range_eq_top_of_surjective _ h.bijective.surjective]
    exact LinearMap.range_comp_le_range _ _
  isCompl_ker := by
    apply IsCompl.of_eq
    · ext ⟨x, y⟩
      rw [Submodule.mem_inf, Submodule.mem_bot, LinearMap.mem_ker, ContinuousLinearMap.coe_fst,
        LinearMap.coe_fst, LinearMap.mem_ker, Prod.ext_iff, ← h.bijective.injective.eq_iff]
      simp +contextual [Prod.mk_zero_zero]
    · ext x
      simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
      obtain ⟨y, hy⟩ := h.bijective.surjective (f' x)
      exact ⟨(0, y), by simp, x - (0, y), by simp [map_sub, ← hy], by abel⟩

@[simp]
lemma implicitFunctionData_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.pt = a := rfl

@[simp]
lemma implicitFunctionData_leftFun_apply {h : IsContDiffImplicitAt n f f' a} {xy : E × F} :
    h.implicitFunctionData.leftFun xy = xy.1 := rfl

@[deprecated "use simp" (since := "2026-01-08")]
lemma implicitFunctionData_leftFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.leftFun h.implicitFunctionData.pt = a.1 := by
  simp

@[simp]
lemma implicitFunctionData_rightFun_apply {h : IsContDiffImplicitAt n f f' a} {xy : E × F} :
    h.implicitFunctionData.rightFun xy = f xy := rfl

@[deprecated "use simp" (since := "2026-01-08")]
lemma implicitFunctionData_rightFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.rightFun h.implicitFunctionData.pt = f a := by
  simp

/-- The implicit function provided by the general theorem, from which we construct the more useful
form `IsContDiffImplicitAt.implicitFunction`. -/
noncomputable def implicitFunctionAux (h : IsContDiffImplicitAt n f f' a) : E → G → E × F :=
  h.implicitFunctionData.implicitFunction

lemma implicitFunctionAux_fst (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), (h.implicitFunctionAux p.1 p.2).1 = p.1 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.fst

lemma comp_implicitFunctionAux_eq_snd (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), f (h.implicitFunctionAux p.1 p.2) = p.2 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.snd

/-- Implicit function `φ` defined by `f (x, φ x) = f a`. -/
@[deprecated ContDiffAt.implicitFunction (since := "2026-01-19")]
noncomputable def implicitFunction (h : IsContDiffImplicitAt n f f' a) : E → F :=
  fun x ↦ (h.implicitFunctionAux x (f a)).2

lemma implicitFunction_def (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunction = fun x ↦ (h.implicitFunctionData.implicitFunction.uncurry (x, f a)).2 :=
  rfl

@[simp]
lemma implicitFunction_apply (h : IsContDiffImplicitAt n f f' a) (x : E) :
    h.implicitFunction x = (h.implicitFunctionData.implicitFunction x (f a)).2 := rfl

@[deprecated ContDiffAt.image_implicitFunction (since := "2026-01-19")]
lemma apply_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ x in 𝓝 a.1, f (x, h.implicitFunction x) = f a := by
  have := h.comp_implicitFunctionAux_eq_snd
  have hfst := h.implicitFunctionAux_fst
  rw [nhds_prod_eq, eventually_swap_iff] at this hfst
  apply this.curry.self_of_nhds.mp
  apply hfst.curry.self_of_nhds.mono
  simp_rw [Prod.swap_prod_mk]
  intro x h1 h2
  rw [← h2]
  congr 1
  ext
  · rw [h1]
  · rfl

@[deprecated ContDiffAt.eventually_implicitFunction_apply_eq (since := "2026-01-19")]
theorem eventually_implicitFunction_apply_eq (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ xy in 𝓝 a, f xy = f a → h.implicitFunction xy.1 = xy.2 := by
  refine h.implicitFunctionData.implicitFunction_apply_image.mono fun xy h₁ h₂ ↦ ?_
  simp_all

@[deprecated ContDiffAt.contDiffAt_implicitFunction (since := "2026-01-19")]
theorem contDiffAt_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ContDiffAt 𝕜 n h.implicitFunction a.1 := by
  have := h.implicitFunctionData.contDiff_implicitFunction contDiffAt_fst h.contDiffAt h.ne_zero
  rw [implicitFunction_def]
  fun_prop

end IsContDiffImplicitAt

end
