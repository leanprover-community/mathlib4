/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Implicit function theorem

In this file, we apply the generalised implicit function theorem to the more familiar case and show
that the implicit function preserves the smoothness class of the implicit equation.

Let `E`, `F`, and `G` be real or complex Banach spaces. Let `f : E × F → G` be a function that is
$C^n$ at a point `(a, b) : E × F`, where `n ≥ 1`. Let `f'` be the derivative of `f` at `(a, b)`. If
the range of `f'` is all of `G`, and the kernel of `f'` is the subspace `E × {0}` in `E × F`, then
there exists a function `φ : E → F` such that `φ a = b`, and `f x (φ x) = f a b` holds for all `x`
in a neighbourhood of `a`. Furthermore, `φ` is $C^n$ at `a`.

## TODO
* Local uniqueness of the implicit function
* Derivative of the implicit function

## Tags

implicit function, inverse function
-/

namespace ImplicitFunctionData

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {φ : ImplicitFunctionData 𝕜 E F G} {n : WithTop ℕ∞}

/-- The implicit function defined by a $C^n$ implicit equation is $C^n$. This applies to the general
form of the implicit function theorem. -/
theorem contDiff_implicitFunction (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt)
    (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (hn : 1 ≤ n) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction, Function.uncurry_curry, toOpenPartialHomeomorph,
    ← HasStrictFDerivAt.localInverse_def]
  exact (hl.prodMk hr).to_localInverse (φ.hasStrictFDerivAt |>.hasFDerivAt) hn

end ImplicitFunctionData

open Filter

open LinearMap (ker range)

open scoped Topology

/-- A predicate stating the sufficient conditions on an implicit equation `f : E × F → F` that will
lead to a $C^n$ implicit function `φ : E → F`. -/
structure IsContDiffImplicitAt {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (n : WithTop ℕ∞) (f : E × F → G) (f' : E × F →L[𝕜] G) (a : E × F) : Prop where
  hasFDerivAt : HasFDerivAt f f' a
  contDiffAt : ContDiffAt 𝕜 n f a
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E F))
  one_le : 1 ≤ n

namespace IsContDiffImplicitAt

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {n : WithTop ℕ∞} {f : E × F → G} {f' : E × F →L[𝕜] G} {a : E × F}

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
  hasStrictFDerivAt_rightFun := h.contDiffAt.hasStrictFDerivAt' h.hasFDerivAt h.one_le
  range_leftDeriv := LinearMap.range_eq_top_of_surjective _ fun x ↦ ⟨(x, 0), rfl⟩
  range_rightDeriv := by
    apply top_unique
    rw [← LinearMap.range_eq_top_of_surjective _ h.bijective.surjective]
    exact LinearMap.range_comp_le_range _ _
  isCompl_ker := by
    apply IsCompl.of_eq
    · ext x
      rw [Submodule.mem_inf, Submodule.mem_bot, LinearMap.mem_ker, ContinuousLinearMap.coe_fst',
        LinearMap.mem_ker]
      refine ⟨fun ⟨h1, h2⟩ => ?_, by rintro rfl; exact ⟨rfl, map_zero _⟩⟩
      rw [Prod.ext_iff]; refine ⟨h1, h.bijective.injective ?_⟩
      change f' (0, x.2) = f' (0, 0)
      rw [show (0, x.2) = x by ext; exacts [h1.symm, rfl], h2]; exact (map_zero _).symm
    · ext x; simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
      obtain ⟨y, hy⟩ := h.bijective.surjective (f' x)
      exact ⟨(0, y), by simp, x - (0, y), by simp [map_sub, ← hy], by abel⟩

@[simp]
lemma implicitFunctionData_leftFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.leftFun h.implicitFunctionData.pt = a.1 := rfl

@[simp]
lemma implicitFunctionData_rightFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.rightFun h.implicitFunctionData.pt = f a := rfl

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
noncomputable def implicitFunction (h : IsContDiffImplicitAt n f f' a) : E → F :=
  fun x ↦ (h.implicitFunctionAux x (f a)).2

lemma implicitFunction_def (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunction = fun x ↦ (h.implicitFunctionData.implicitFunction.uncurry (x, (f a))).2 :=
  rfl

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
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

/-- If the implicit equation `f` is $C^n$ at `(x, y)`, then its implicit function `φ` around `x` is
also $C^n$ at `x`. -/
theorem contDiffAt_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ContDiffAt 𝕜 n h.implicitFunction a.1 := by
  have := h.implicitFunctionData.contDiff_implicitFunction contDiffAt_fst h.contDiffAt h.one_le
  rw [implicitFunction_def]
  fun_prop

end IsContDiffImplicitAt
