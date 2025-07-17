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

Let `E` and `F` be real or complex Banach spaces. Let `f : E × F → F` be a function that is $C^n$ at
a point `(a, b) : E × F`, where `n ≥ 1`. Let `f'` be the derivative of `f` at `(a, b)`. If the range
of `f'` is all of `F`, and the kernel of `f'` is the subspace `E × {0}` in `E × F`, then there
exists a function `φ : E → F` such that `φ a = b`, and `f x (φ x) = f a b` holds for all `x` in a
neighbourhood of `a`. Furthoremore, `φ` is $C^n$ at `a`.

## TODO
* Local uniqueness of the implicit function
* Derivative of the implicit function

## Tags

implicit function, inverse function
-/

section
-- move somewhere
variable {α β γ δ : Type*} {ι : Sort*}
variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

theorem Filter.eventually_prod_iff_exists_mem {p : α × β → Prop} :
    (∀ᶠ x in f ×ˢ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s, ∀ y ∈ t, p ⟨x, y⟩ := by
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨st, hst, h⟩ ↦ ?_, fun ⟨s, hs, t, ht, h⟩ ↦ ?_⟩
  · have ⟨s, hs, t, ht, hp⟩ := Filter.mem_prod_iff.mp hst
    exact ⟨s, hs, t, ht, fun x hx y hy ↦ h _ <| hp ⟨hx, hy⟩⟩
  · exact ⟨s ×ˢ t, Filter.prod_mem_prod hs ht, fun ⟨x, y⟩ ⟨hx, hy⟩ ↦ h x hx y hy⟩

end

namespace ImplicitFunctionData
-- goes in the general theory

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G) {n : WithTop ℕ∞}

theorem contDiff_implicitFunction (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt)
    (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (hn : 1 ≤ n) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction, Function.uncurry_curry, toPartialHomeomorph,
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
    (n : WithTop ℕ∞) (f : E × F → F) (f' : E × F →L[𝕜] F) (a : E × F) : Prop where
  hasFDerivAt : HasFDerivAt f f' a
  contDiffAt : ContDiffAt 𝕜 n f a
  range_eq_top : range f' = ⊤
  ker_eq_left : ker f' = range (LinearMap.inl 𝕜 E F)
  one_le : 1 ≤ n

namespace IsContDiffImplicitAt

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {n : WithTop ℕ∞} {f : E × F → F} {f' : E × F →L[𝕜] F} {a : E × F}

def implicitFunctionData (h : IsContDiffImplicitAt n f f' a) :
    ImplicitFunctionData 𝕜 (E × F) E F where
  leftFun := Prod.fst
  leftDeriv := ContinuousLinearMap.fst 𝕜 E F
  rightFun := f
  rightDeriv := f'
  pt := a
  left_has_deriv := by fun_prop
  right_has_deriv := h.contDiffAt.hasStrictFDerivAt' h.hasFDerivAt h.one_le
  left_range := LinearMap.range_eq_top_of_surjective _ fun x ↦ ⟨(x, 0), rfl⟩
  right_range := h.range_eq_top
  isCompl_ker := by
    have : LinearMap.ker (ContinuousLinearMap.fst 𝕜 E F) = LinearMap.ker (LinearMap.fst 𝕜 E F) :=
      rfl
    rw [isCompl_comm, this, LinearMap.ker_fst, h.ker_eq_left]
    exact LinearMap.isCompl_range_inl_inr

@[simp]
lemma implicitFunctionData_prodFun (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.prodFun h.implicitFunctionData.pt = (a.1, f a) := rfl

noncomputable def implicitFunctionAux (h : IsContDiffImplicitAt n f f' a) : E → F → E × F :=
  h.implicitFunctionData.implicitFunction

lemma implicitFunctionAux_fst (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), (h.implicitFunctionAux p.1 p.2).1 = p.1 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.fst

-- lemma for `implicitFunctionAux_snd` but only at `(x, f a)`

lemma rightFun_implicitFunctionAux (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), f (h.implicitFunctionAux p.1 p.2) = p.2 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.snd

/-- Implicit function `y` defined by `f (x, y x) = f a`. -/
noncomputable def implicitFunction (h : IsContDiffImplicitAt n f f' a) : E → F :=
  fun x ↦ (h.implicitFunctionAux x (f a)).2

lemma implicitFunction_def (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunction = fun x ↦ (h.implicitFunctionData.implicitFunction.uncurry (x, (f a))).2 :=
  rfl

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
lemma apply_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ x in 𝓝 a.1, f (x, h.implicitFunction x) = f a := by
  have := h.rightFun_implicitFunctionAux
  have hfst := h.implicitFunctionAux_fst
  rw [nhds_prod_eq, eventually_swap_iff] at this hfst
  replace := this.curry.self_of_nhds
  replace hfst := hfst.curry.self_of_nhds
  apply this.mp
  apply hfst.mono
  intro x
  simp_rw [Prod.swap_prod_mk]
  intro h1 h2
  rw [← h2]
  congr 1
  ext
  · rw [h1]
  · rfl

/-- If `f` is $C^n$ at `(x, y)`, then its implicit function around `x` is also $C^n$ at `x`. -/
theorem contDiff_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ContDiffAt 𝕜 n h.implicitFunction a.1 := by
  have := h.implicitFunctionData.contDiff_implicitFunction contDiffAt_fst h.contDiffAt h.one_le
  rw [implicitFunction_def]
  fun_prop

end IsContDiffImplicitAt
