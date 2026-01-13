/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Define the least reasonable crossnorm

For `x : ⨂ Eᵢ`, we define `leastCrossnorm x` as the norm of the multilinear map
that sends a family `fᵢ : StrongDual Eᵢ` to `(⨂ fᵢ) x`. If the `Eᵢ` are normed
spaces over `ℝ` or `ℂ`, this is the "least reasonable crossnorm".

Terminology: The "least reasonable crossnorm" is often called the "injective
norm". In contrast, Mathlib currently uses "injective seminorm" to refer to an
alternative construction of the projective seminorm.

This is WIP.

See also:

[Diestel2008] Diestel, Fourie, Swart, The metric theory of tensor products.
https://www.ams.org/bookstore/pspdf/mbk-52-prev.pdf

## Main definitions

* `PiTensorProduct.leastCrossnorm`: For `x : ⨂ Eᵢ`, `leastCrossnorm x` is the
  norm of the multilinear map that sends a family `fᵢ : StrongDual Eᵢ` to `(⨂ fᵢ) x`.
* `PiTensorProduct.dualDistribL`: A continuous version of `PiTensorProduct.dualDistrib`.

## Main results

* `PiTensorProduct.le_leastCrossnorm`: `‖dualDistribL (⨂ fᵢ) x‖` lower-bounds
  `(leastCrossnorm x) * (∏ ‖fᵢ‖)`.
* `PiTensorProduct.leastCrossnorm_le_bound`: If `‖dualDistribL (⨂ fᵢ) x‖ ≤ M * (∏ ‖fᵢ‖))`
  for all families `fᵢ : StrongDual Eᵢ`, then `leastCrossnorm x ≤ M`.
* `PiTensorProduct.projectiveSeminorm_tprod_eq_of_dual_vectors`: the projective
  seminorm satisfies the multiplicativity property `‖⨂ mᵢ‖ = ∏ ‖mᵢ‖` if, for
  each `mᵢ`, there is an `fᵢ` in the dual unit ball such that `‖fᵢ mᵢ‖ = ‖mᵢ‖`.
  [This fits into ProjectiveSeminorm.lean; included here pending comments on the
  proposed refactoring of that file.]

## Implementation notes

In the definition of `leastCrossnorm`, we let the multilinear map take values
values in `(⨂[𝕜] _ : ι, 𝕜)`. Only later do we define an isometric equivalence
`(⨂[𝕜] _ : ι, 𝕜) ≃ₗᵢ 𝕜`.

## TODO

* Mainly: Get feedback.
* Show that the `leastCrossnorm` (and hence the `projectiveSeminorm`) are norms, assuming
  `∀ i, SeparatingDual Eᵢ`.
* Show the eponymous "injectivity property": Given submodules `pᵢ ⊆ Eᵢ` and `x : ⨂ pᵢ`, then
  `leastCrossnorm x = leastCrossnorm mapIncl x`.
* Generalize `projectiveSeminorm_tprod_of_dual_vectors` to the case where the `fᵢ` are replaced by
  a net of vectors in the dual unit ball, such that the norm of the evaluation on `mᵢ` converges to
  `‖mᵢ‖`.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]

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

/-
# Below is a collection of related results.
-/

/-
## Sufficient conditions for multiplicativity of the projective seminorm
-/

section projectiveSeminorm_tprod

theorem projectiveSeminorm_tprod_eq_of_dual_vectors {f : Π i, StrongDual 𝕜 (E i)}
    (m : Π i, E i) (hf₁ : ∀ i, ‖f i‖ ≤ 1) (hf₂ : ∀ i, ‖f i (m i)‖ = ‖m i‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  apply eq_of_le_of_ge (projectiveSeminorm_tprod_le m)
  haveI := nonempty_subtype.mpr (nonempty_lifts (⨂ₜ[𝕜] i, m i))
  apply le_ciInf (fun x ↦ ?_)
  have hx := congr_arg (norm ∘ dualDistrib (⨂ₜ[𝕜] i, f i)) ((mem_lifts_iff _ _).mp x.prop)
  simp only [Function.comp_apply, dualDistrib_apply, ContinuousLinearMap.coe_coe, hf₂, norm_prod,
     map_list_sum, List.map_map] at hx
  grw [← hx, List.le_sum_of_subadditive norm norm_zero.le norm_add_le, List.map_map]
  apply List.sum_le_sum (fun _ _ ↦ ?_)
  simp only [Function.comp_apply, map_smul, dualDistrib_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, norm_mul, norm_prod]
  gcongr
  grw [ContinuousLinearMap.le_opNorm, hf₁, one_mul]

end projectiveSeminorm_tprod

section RCLike

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem projectiveSeminorm_tprod (m : Π i, E i)
    : projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  choose g hg₁ hg₂ using fun i ↦ exists_dual_vector'' 𝕜 (m i)
  exact projectiveSeminorm_tprod_eq_of_dual_vectors m hg₁ (by simp [hg₂])

end RCLike

/-
## Isometric version of `constantBaseRingIsometry`
-/

section constantBaseRingIsometry

section RingTheory

variable {ι R' R : Type*} {A : ι → Type*}
variable [CommSemiring R'] [CommSemiring R] [∀ i, Semiring (A i)]
variable [Algebra R' R]
variable [∀ i, Algebra R (A i)]

/-
The following definitonal equality is used in `PiTensorProduct.algebraMap_apply`, but does not seem
to be registered as a `simp` lemma.

Adding this to RingTheory/PiTensorProduct.lean would mirror the idiom used for the pair
`Pi.algebraMap_def`, `Pi.algebraMap_apply`.
-/
theorem algebraMap_def (r : R') : algebraMap R' (⨂[R] i, A i) r = r • (⨂ₜ[R] _ : ι, 1)
  := rfl

end RingTheory

section mulL

def mulL : 𝕜 → StrongDual 𝕜 𝕜 := fun a ↦
  LinearMap.mkContinuous (LinearMap.mul 𝕜 𝕜 a) ‖a‖ (by simp)

@[simp]
theorem mulL_apply {a b : 𝕜} : (mulL a) b = a * b := by rfl

@[simp]
theorem opNorm_mulL_eq {a : 𝕜} : ‖mulL a‖ = ‖a‖ := by
  apply le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (by simp))
  simpa using (mulL a).ratio_le_opNorm 1

end mulL

theorem projectiveSeminorm_tprod_field (m : ι → 𝕜) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_eq_of_dual_vectors m (f := fun _ ↦ mulL (1 : 𝕜)) (by simp) (by simp)

variable (ι 𝕜) in
noncomputable def constantBaseRingIsometry : (⨂[𝕜] _ : ι, 𝕜) ≃ₗᵢ[𝕜] 𝕜 :=
  { (constantBaseRingEquiv ι 𝕜).toLinearEquiv with
    norm_map' x := by
      have h_symm_iso (r : 𝕜) : ‖r‖ = ‖(constantBaseRingEquiv ι 𝕜).toLinearEquiv.symm r‖ := by
        simp [algebraMap_def, norm_smul, projectiveSeminorm_tprod_field]
      simpa using h_symm_iso ((constantBaseRingEquiv ι 𝕜).toLinearEquiv x) }

@[simp]
theorem constantBaseRingIsometry_apply (m : ι → 𝕜) :
    constantBaseRingIsometry ι 𝕜 (⨂ₜ[𝕜] i , m i) = ∏ i, m i := by
  simp [constantBaseRingIsometry]

end constantBaseRingIsometry

/-
## Continuous version of `dualDistrib`
-/

section dualDistribL

variable (f : Π i, E i →L[𝕜] E' i)

noncomputable def piTensorHomMapL :
    (⨂[𝕜] i, E i →L[𝕜] E' i) →L[𝕜] (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  (liftIsometry 𝕜 _ _) (mapLMultilinear 𝕜 E E')

@[simp]
theorem piTensorHomMapL_tprod_tprod (f : Π i, E i →L[𝕜] E' i) (x : Π i, E i) :
    piTensorHomMapL (tprod 𝕜 f) (tprod 𝕜 x) = tprodL 𝕜 fun i ↦ f i (x i) := by
  simp [piTensorHomMapL, liftAux_tprod]

theorem piTensorHomMapL_tprod_eq_mapL (f : Π i, E i →L[𝕜] E' i) :
    piTensorHomMapL (tprod 𝕜 f) = mapL f := by
  simp [piTensorHomMapL, mapLMultilinear]  -- TBD: Refine API for `piTensorHomMapL`

theorem opNorm_piTensorHomMapL_le : ‖piTensorHomMapL (𝕜:=𝕜) (E:=E) (E':=E')‖ ≤ 1 := by
  simp only [piTensorHomMapL, LinearIsometryEquiv.norm_map]
  apply MultilinearMap.mkContinuous_norm_le _ zero_le_one

noncomputable def dualDistribL : (⨂[𝕜] i, StrongDual 𝕜 (E i)) →L[𝕜] StrongDual 𝕜 (⨂[𝕜] i, E i) :=
  (ContinuousLinearMap.compL 𝕜 _ _ 𝕜 (constantBaseRingIsometry ι 𝕜)).comp piTensorHomMapL

/-- Warning: *Not* an analogue of `dualDistrib_apply`! See `dualDistrib_apply_apply`. -/
@[simp]
theorem dualDistribL_apply (f : Π i, StrongDual 𝕜 (E i)) (x : (⨂[𝕜] i, E i)) :
    dualDistribL (⨂ₜ[𝕜] i, f i) x = (constantBaseRingIsometry ι 𝕜) (mapL f x) := by
  simp [dualDistribL, piTensorHomMapL_tprod_eq_mapL]

/-- Corresponds to `dualDistrib_apply`. See also `dualDistribL_apply` -/
theorem dualDistribL_apply_apply (f : Π i, StrongDual 𝕜 (E i)) (g : Π i, E i) :
    dualDistribL (⨂ₜ[𝕜] i, f i) (⨂ₜ[𝕜] i, g i) = ∏ i, f i (g i) := by
  simp

end dualDistribL


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
