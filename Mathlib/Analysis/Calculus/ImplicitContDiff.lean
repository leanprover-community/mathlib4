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

-- /-- A partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
-- to vertical subspaces. -/
-- def implicitToPartialHomeomorphOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
--     (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : PartialHomeomorph (E × F) (E × F) :=
--   (implicitFunctionDataOfProd hf hf' hf'').toPartialHomeomorph

-- lemma implicitFunctionDataOfProd_leftFun_apply (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
--     (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) (p : E × F) :


def implicitFunctionOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : E → F → E × F :=
  (implicitFunctionDataOfProd hf hf' hf'').implicitFunction

/-- Implicit function `y` defined by `f (x, y x) = x`. -/
def implicitFunctionOfProd' (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) : E → F :=
  fun x ↦ (implicitFunctionOfProd hf hf' hf'' x a.2).2

lemma implicitFunctionOfProd_fst (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ p in 𝓝 (a.1, f a), (implicitFunctionOfProd hf hf' hf'' p.1 p.2).1 = p.1 := by
  exact (implicitFunctionDataOfProd hf hf' hf'').prod_map_implicitFunction.mono
    fun _ ↦ congr_arg Prod.fst

lemma rightFun_implicitFunctionOfProd (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ p in 𝓝 (a.1, f a), f (implicitFunctionOfProd hf hf' hf'' p.1 p.2) = p.2 :=
  (implicitFunctionDataOfProd hf hf' hf'').prod_map_implicitFunction.mono
    fun _ ↦ congr_arg Prod.snd

lemma rightFun_implicitFunctionOfProd' (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hf'' : ker f' = range (LinearMap.inl 𝕜 E F)) :
    ∀ᶠ x in 𝓝 a.1, f (x, implicitFunctionOfProd' hf hf' hf'' x) = a.2 := by
  have := rightFun_implicitFunctionOfProd hf hf' hf''
  rw [eventually_iff_exists_mem] at this
  obtain ⟨u, hu, h⟩ := this
  sorry

end ImplicitFunctionData

end
