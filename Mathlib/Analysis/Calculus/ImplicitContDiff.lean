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

end ImplicitFunctionData

end
