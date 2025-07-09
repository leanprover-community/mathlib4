/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

open scoped Topology

open Filter

open ContinuousLinearMap (fst snd smulRight ker_prod)

open ContinuousLinearEquiv (ofBijective)

open LinearMap (ker range)

namespace ImplicitFunctionData

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

variable {f : E × F → F} {f' : E × F →L[𝕜] F} {a : E × F}

/-- Function `y : E → F` defined implicitly by `f (x, y) = z`.

Note: For the smoothness theorem for integral curves, `f = 0` is the integral equation. The
derivative of `f` wrt the curve is invertible (`hf'`) and independent of `x` (`hf''`). -/
def implicitFunctionDataOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ImplicitFunctionData 𝕜 (E × F) E F where
  leftFun := Prod.fst
  leftDeriv := ContinuousLinearMap.fst 𝕜 E F
  rightFun := f
  rightDeriv := f'
  pt := a
  left_has_deriv := by fun_prop
  right_has_deriv := hf
  left_range := LinearMap.range_eq_top_of_surjective _ fun x ↦ ⟨(x, 0), rfl⟩
  right_range := hf'
  isCompl_ker := by
    have : LinearMap.ker (ContinuousLinearMap.fst 𝕜 E F) = LinearMap.ker (LinearMap.fst 𝕜 E F) :=
      rfl
    rw [isCompl_comm, this, LinearMap.ker_fst, hf'']
    exact LinearMap.isCompl_range_inl_inr

@[simp]
lemma implicitFunctionDataOfProd_prodFun (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    (implicitFunctionDataOfProd hf hf' hf'').prodFun (implicitFunctionDataOfProd hf hf' hf'').pt =
      (a.1, f a) := rfl

-- /-- A partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
-- to vertical subspaces. -/
-- def implicitToPartialHomeomorphOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
--     (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : PartialHomeomorph (E × F) (E × F) :=
--   (implicitFunctionDataOfProd hf hf' hf'').toPartialHomeomorph

def implicitFunctionOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : E → F → E × F :=
  (implicitFunctionDataOfProd hf hf' hf'').implicitFunction

/-- Implicit function `y` defined by `f (x, y x) = f a`. -/
def implicitFunctionOfProd' (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : E → F :=
  fun x ↦ (implicitFunctionOfProd hf hf' hf'' x (f a)).2

lemma implicitFunctionOfProd_fst (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ p in 𝓝 (a.1, f a), (implicitFunctionOfProd hf hf' hf'' p.1 p.2).1 = p.1 := by
  exact (implicitFunctionDataOfProd hf hf' hf'').prod_map_implicitFunction.mono
    fun _ ↦ congr_arg Prod.fst

-- lemma for `implicitFunctionOfProd_snd` but only at `(x, f a)`

lemma rightFun_implicitFunctionOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ p in 𝓝 (a.1, f a), f (implicitFunctionOfProd hf hf' hf'' p.1 p.2) = p.2 :=
  (implicitFunctionDataOfProd hf hf' hf'').prod_map_implicitFunction.mono
    fun _ ↦ congr_arg Prod.snd

section

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

/-- `implicitFunctionOfProd' .. : E → F` is indeed the (local) implicit function to `f`. -/
lemma rightFun_implicitFunctionOfProd' (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ x in 𝓝 a.1, f (x, implicitFunctionOfProd' hf hf' hf'' x) = f a := by
  have := rightFun_implicitFunctionOfProd hf hf' hf''
  have hfst := implicitFunctionOfProd_fst hf hf' hf''
  rw [nhds_prod_eq, eventually_swap_iff] at this hfst
  replace := this.curry.self_of_nhds
  replace hfst := hfst.curry.self_of_nhds
  apply this.mp
  apply hfst.mono
  intro x
  simp_rw [Prod.swap_prod_mk]
  intro h h'
  rw [← h', implicitFunctionOfProd']
  congr 1
  ext
  · rw [h]
  · rfl

/-- If `f` is $C^n$ at `(x, y)`, then its implicit function around `x` is also $C^n$ at `x`. -/
theorem contDiff_implicitFunctionOfProd' (h : ContDiffAt 𝕜 n f a) (hf : HasFDerivAt f f' a)
    (hf' : range f' = ⊤) (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) (hn : 1 ≤ n) :
    ContDiffAt 𝕜 n (implicitFunctionOfProd' (h.hasStrictFDerivAt' hf hn) hf' hf'') a.1 := by
  have := implicitFunctionDataOfProd (h.hasStrictFDerivAt' hf hn) hf' hf''
    |>.contDiff_implicitFunction contDiffAt_fst h hn
  rw [← implicitFunctionOfProd, implicitFunctionDataOfProd_prodFun] at this
  -- make a lemma
  have heq : implicitFunctionOfProd' (h.hasStrictFDerivAt' hf hn) hf' hf'' = fun x ↦
      ((implicitFunctionOfProd (h.hasStrictFDerivAt' hf hn) hf' hf'').uncurry (x, (f a))).2 := rfl
  rw [heq]
  fun_prop

end ImplicitFunctionData

end
