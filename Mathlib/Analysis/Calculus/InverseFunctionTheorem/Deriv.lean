/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, 1D case

In this file we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `ContinuousLinearEquiv.unitsEquivAut` to translate `HasStrictDerivAt f f' a` and
`f' ≠ 0` into `HasStrictFDerivAt f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (f : 𝕜 → 𝕜)

noncomputable section
namespace HasStrictDerivAt

variable (f' a : 𝕜) (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)

/-- A function that is inverse to `f` near `a`. -/
@[reducible]
def localInverse : 𝕜 → 𝕜 :=
  (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _
#align has_strict_deriv_at.local_inverse HasStrictDerivAt.localInverse

variable {f f' a}

theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv
#align has_strict_deriv_at.map_nhds_eq HasStrictDerivAt.map_nhds_eq

theorem to_localInverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_localInverse
#align has_strict_deriv_at.to_local_inverse HasStrictDerivAt.to_localInverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg
#align has_strict_deriv_at.to_local_left_inverse HasStrictDerivAt.to_local_left_inverse

end HasStrictDerivAt

variable {f}

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_deriv {f' : 𝕜 → 𝕜}
    (hf : ∀ x, HasStrictDerivAt f (f' x) x) (h0 : ∀ x, f' x ≠ 0) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge
#align open_map_of_strict_deriv open_map_of_strict_deriv
