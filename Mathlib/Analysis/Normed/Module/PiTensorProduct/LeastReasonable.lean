/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.Normed.Module.Dual

/-!

# WIP material on tensor norms

Arguably, `injectiveSeminorm` should be re-defined in Mathlib.

In this file, we collect some results a possible alternative.

For `x : ⨂ Eᵢ`, we define `leastCrossnorm x` as the norm of the
multilinear map that sends a family `fᵢ : StrongDual Eᵢ` to `‖(⨂ fᵢ) x‖`. If the
`Eᵢ` are normed spaces over `ℝ` or `ℂ`, this is the "smallest reasonable
crossnorm", also known as the "injective tensor norm".

## Main definitions

* `PiTensorProduct.leastCrossnorm`: For `x : ⨂ Eᵢ`, `leastCrossnorm x` is the
  norm of the multilinear map that sends a family `fᵢ : StrongDual Eᵢ` to `‖(⨂ fᵢ) x‖`.
  (Commonly called "injective norm". Name should be changed if existing `injectiveSeminorm`
  does get removed).

## Main results

* `PiTensorProduct.le_leastCrossnorm`: `‖dualDistribL (⨂ fᵢ) x‖` lower-bounds
  `(leastCrossnorm x) * (∏ ‖fᵢ‖)`.
* `PiTensorProduct.leastCrossnorm_le_bound`: If `‖dualDistribL (⨂ fᵢ) x‖ ≤ M * (∏ ‖fᵢ‖))`
  for all families `fᵢ : StrongDual Eᵢ`, then `M` upper-bounds `leastCrossnorm x`.

## Implementation notes

In the definition of `leastCrossnorm`, we let the multilinear map take values
values in `(⨂[𝕜] _ : ι, 𝕜)`. Only later do we define an isometric equivalence
`(⨂[𝕜] _ : ι, 𝕜) ≃ₗᵢ 𝕜`.

## TODO

* Get feedback.
* Show that the `leastCrossnorm` (and hence the `projectiveSeminorm`) are norms, assuming
  `∀ i, SeparatingDual Eᵢ`.
* Show the eponymous "injectivity property": Given submodules `pᵢ ⊆ Eᵢ` and `x : ⨂ pᵢ`, it holds
  that `leastCrossnorm x = leastCrossnorm mapIncl x`. (This may require additional assumptions on
  the normed spaces, such as the applicability of Hahn-Banach).
-/

section LeastReasonable

variable (𝕜) in
open ContinuousLinearMap in
/-- Map `x : ⨂ Eᵢ` to the multilinear map that sends a family `fᵢ : StrongDual Eᵢ` of dual
vectors to `(⨂ₜ fᵢ) x`.

Here, we take the result to live in `(⨂[𝕜] _ : ι, 𝕜)`. We'll define an isometric equivalence
`(⨂[𝕜] _ : ι, 𝕜) ≃ₗᵢ 𝕜` below. For now, it's easier to work with the tensor product of the ring. -/
noncomputable def toMultilinearMapDualTmul :
    (⨂[𝕜] i, E i) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ StrongDual 𝕜 (E i)) (⨂[𝕜] _ : ι, 𝕜) :=
  ((compContinuousMultilinearMapL ..).flip (mapLMultilinear 𝕜 E (fun _ : ι ↦ 𝕜))).comp (apply 𝕜 _)

@[simp]
theorem toMultilinearMapDualTmul_apply_apply (x : (⨂[𝕜] i, E i)) (f : Π i, StrongDual 𝕜 (E i)) :
    toMultilinearMapDualTmul 𝕜 x f = mapL f x
  := rfl

/-- On a tensor product of Banach spaces, this is the least of the reasonable crossnorms -/
noncomputable def leastCrossnorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := Seminorm.comp
    (normSeminorm 𝕜 (ContinuousMultilinearMap ..)) (toMultilinearMapDualTmul 𝕜).toLinearMap

@[simp]
theorem leastCrossnorm_apply (x : (⨂[𝕜] i, E i)) :
    leastCrossnorm x = ‖toMultilinearMapDualTmul 𝕜 x‖
  := rfl

theorem leastCrossnorm_le_projectiveSeminorm (x : (⨂[𝕜] i, E i)) : leastCrossnorm x ≤ ‖x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg x) fun m ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, toMultilinearMapDualTmul_apply_apply]
  grw [ContinuousLinearMap.le_opNorm, mul_comm, mapL_opNorm]

theorem leastCrossnorm_tprod_le (m : Π i, E i) : leastCrossnorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
  grw [leastCrossnorm_le_projectiveSeminorm]
  exact projectiveSeminorm_tprod_le m

theorem norm_mapL_le_leastCrossnorm (x : (⨂[𝕜] i, E i)) (f : Π i, StrongDual 𝕜 (E i)) :
    ‖mapL f x‖ ≤ (leastCrossnorm x) * (∏ i, ‖f i‖) := by
  rw [leastCrossnorm_apply, ← toMultilinearMapDualTmul_apply_apply]
  grw [ContinuousMultilinearMap.le_opNorm]

section map

variable (f : Π i, E i →L[𝕜] E' i)

open ContinuousLinearMap in
theorem leastCrossnorm_mapL_apply_le (x : (⨂[𝕜] i, E i)) :
    leastCrossnorm (mapL f x) ≤ (∏ i, ‖f i‖) * leastCrossnorm x := by
  rw [leastCrossnorm_apply]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  grw [toMultilinearMapDualTmul_apply_apply, ← comp_apply, ← mapL_comp, norm_mapL_le_leastCrossnorm]
  conv_rhs => rw [mul_assoc, mul_comm, mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ opNorm_comp_le (m i) (f i))

end map

end LeastReasonable

section leastCrossnorm_dualDistribL

theorem le_leastCrossnorm (f : Π i, StrongDual 𝕜 (E i)) (x : (⨂[𝕜] i, E i)) :
    ‖dualDistribL (⨂ₜ[𝕜] i, f i) x‖ ≤ (leastCrossnorm x) * (∏ i, ‖f i‖) := by
  grw [← norm_mapL_le_leastCrossnorm]
  simp

theorem ratio_le_leastCrossnorm (f : Π i, StrongDual 𝕜 (E i)) (x : (⨂[𝕜] i, E i)) :
    (‖dualDistribL (⨂ₜ[𝕜] i, f i) x‖ / ∏ i, ‖f i‖) ≤ leastCrossnorm x :=
  div_le_of_le_mul₀ (by positivity) (by simp) (le_leastCrossnorm f x)

theorem leastCrossnorm_le_bound (x : (⨂[𝕜] i, E i)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ (f : Π i, StrongDual 𝕜 (E i)),
      ‖dualDistribL (⨂ₜ[𝕜] i, f i) x‖ ≤ M * (∏ i, ‖f i‖)) : leastCrossnorm x ≤ M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hMp
  simpa using hM

end leastCrossnorm_dualDistribL

end PiTensorProduct
