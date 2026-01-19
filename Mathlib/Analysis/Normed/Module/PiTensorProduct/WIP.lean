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

In this file, we collect some results about the current definition and a possible
alternative.

In particular, for `x : ⨂ Eᵢ`, we define `leastCrossnorm x` as the norm of the
multilinear map that sends a family `fᵢ : StrongDual Eᵢ` to `‖(⨂ fᵢ) x‖`. If the
`Eᵢ` are normed spaces over `ℝ` or `ℂ`, this is the "smallest reasonable
crossnorm".

## Main definitions

* `PiTensorProduct.injectiveSeminorm`: A "dual" definition of the projective seminorm.
  (That's the name currently used in Mathlib for the definition. Arguably, the
  definition should be removed or renamed).
* `PiTensorProduct.leastCrossnorm`: For `x : ⨂ Eᵢ`, `leastCrossnorm x` is the
  norm of the multilinear map that sends a family `fᵢ : StrongDual Eᵢ` to `‖(⨂ fᵢ) x‖`.
  (Commonly called "injective norm". Name should be changed if existing `injectiveSeminorm`
  does get removed).
* `PiTensorProduct.dualDistribL`: A continuous version of `PiTensorProduct.dualDistrib`.

## Main results

* `projectiveSeminorm_tprod`. For normed spaces over `ℝ, ℂ`, the projective seminorm is
  multiplicative w.r.t. tensor products: `‖⨂ m i‖ = ∏ ‖m i‖`.
* `PiTensorProduct.injectiveSeminorm_eq_projectiveSeminorm`: The dual definition
   agrees with the primal definition
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


@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]

/-
In this section, we give sufficient conditions for the multiplicativity property
`‖⨂ m i‖ = ∏ ‖m i‖` to hold for the projective seminorm. This address a TBD item
in ProjectiveSeminorm.lean.
-/
section projectiveSeminorm_tprod

open Filter NormedSpace ContinuousLinearMap

theorem projectiveSeminorm_tprod_eq_of_bidual_iso
    (m : Π i, E i) (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  have g (i : ι) :
      { g : ℕ → StrongDual 𝕜 _ // Tendsto (fun n ↦ ‖g n (m i)‖ / ‖g n‖) atTop (nhds ‖m i‖) } := by
    choose u _ _ _ hu using (IsLUB.exists_seq_monotone_tendsto
      (isLUB_opNorm (inclusionInDoubleDual 𝕜 _ (m i))) ⟨0, ⟨0, by simp⟩⟩)
    simp only [dual_def, Set.mem_range] at hu
    choose g hg using hu
    exact ⟨g, by simp_all⟩
  apply le_ciInf (fun p ↦ le_of_tendsto_of_tendsto
    (tendsto_finset_prod _ (fun i _ ↦ (g i).prop)) tendsto_const_nhds ?_)
  filter_upwards with n
  have hp := congr_arg (fun x ↦ ‖dualDistrib (⨂ₜ[𝕜] i, (g i).val n) x‖ / (∏ i, ‖(g i).val n‖))
    ((mem_lifts_iff _ _).mp p.prop)
  simp only [dualDistrib_apply, coe_coe, norm_prod] at hp
  rw [Finset.prod_div_distrib, ← hp, map_list_sum, List.map_map]
  refine if hz : ∏ i, ‖(g i).val n‖ = 0 then (by simp_all [projectiveSeminormAux_nonneg]) else ?_
  grw [div_le_iff₀' (by positivity), List.le_sum_of_subadditive norm norm_zero.le norm_add_le,
    List.map_map, projectiveSeminormAux, ← List.sum_map_mul_left]
  apply List.sum_le_sum (fun q hq ↦ ?_)
  simp only [Function.comp_apply, map_smul, dualDistrib_apply, coe_coe, smul_eq_mul, norm_mul,
    norm_prod, mul_left_comm, ← Finset.prod_mul_distrib]
  gcongr with i
  apply le_opNorm

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

@[simp]
theorem projectiveSeminorm_tprod (m : Π i, E i) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_eq_of_bidual_iso m
    (fun i ↦ show ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (m i)‖ = ‖m i‖ by simp)

end RCLike

end projectiveSeminorm_tprod


/-
Here, we restate the definition of `injectiveSeminorm` found so far in Mathlib and prove that it
is extensinally equal to `projectiveSeminorm`.
-/
section dualCharacterization

theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = ‖x‖ := rfl

theorem norm_tprodL_le : ‖tprodL 𝕜 (E := E)‖ ≤ 1 :=
  ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun m ↦ by simp [projectiveSeminorm_tprod_le]


variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`. -/
@[simps!]
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuous
    ((LinearMap.flip lift.toLinearMap x) ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear)
    (projectiveSeminorm x)
    (fun _ ↦ by
      simp [projectiveSeminorm_apply, mul_comm, norm_eval_le_projectiveSeminorm])
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMap F x‖ ≤ projectiveSeminorm x := by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (apply_nonneg _ _)

/-- The injective seminorm on `⨂[𝕜] i, Eᵢ`. Morally, it sends `x` in `⨂[𝕜] i, Eᵢ` to the
`sup` of the operator norms of the `PiTensorProduct.toDualContinuousMultilinearMap F x`, for all
normed vector spaces `F`. In fact, we only take in the same universe as `⨂[𝕜] i, Eᵢ`, and then
prove in `PiTensorProduct.norm_eval_le_injectiveSeminorm` that this gives the same result.
-/
noncomputable irreducible_def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}

lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G)} := by
  use projectiveSeminorm
  simp only [mem_upperBounds, Set.mem_setOf_eq, forall_exists_index]
  intro p G _ _ hp x
  simp [hp, toDualContinuousMultilinearMap_le_projectiveSeminorm]

lemma projectiveSeminorn_mem_dualSeminorms : projectiveSeminorm ∈ {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G)} := by
  use (⨂[𝕜] i, E i), inferInstance, inferInstance
  ext x
  refine le_antisymm ?_ (toDualContinuousMultilinearMap_le_projectiveSeminorm x)
  have := ContinuousLinearMap.le_opNorm ((toDualContinuousMultilinearMap _) x) (tprodL 𝕜)
  grw [norm_tprodL_le, mul_one] at this
  simpa

theorem injectiveSeminorm_eq_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) = projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine le_antisymm (csSup_le ⟨_, projectiveSeminorn_mem_dualSeminorms⟩ fun p ⟨G, _, _, h⟩ x ↦ ?_)
    (le_csSup_of_le dualSeminorms_bounded projectiveSeminorn_mem_dualSeminorms (le_refl _))
  simp [h, toDualContinuousMultilinearMap_le_projectiveSeminorm]

-- This used to be a long proof; now somewhat redundant.
theorem norm_eval_le_injectiveSeminorm (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x := by
    simp [projectiveSeminorm_apply, injectiveSeminorm_eq_projectiveSeminorm,
      norm_eval_le_projectiveSeminorm]

theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G)}, p.1 x := by
  simpa only [injectiveSeminorm, Set.coe_setOf, Set.mem_setOf_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

end dualCharacterization

/-
Here, we formalize the "least of the reasonable crossnorms", i.e. the norm
that is commonly called the "injective norm".
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
The following definitional equality is used in `PiTensorProduct.algebraMap_apply`, but does not seem
to be registered as a `simp` lemma.

Adding this to RingTheory/PiTensorProduct.lean would mirror the idiom used for the pair
`Pi.algebraMap_def`, `Pi.algebraMap_apply`.
-/
theorem algebraMap_def (r : R') : algebraMap R' (⨂[R] i, A i) r = r • (⨂ₜ[R] _ : ι, 1)
  := rfl

end RingTheory

theorem projectiveSeminorm_tprod_field (m : ι → 𝕜) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_eq_of_bidual_iso m
    fun i ↦ (by
      apply le_antisymm
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
        rw [NormedSpace.dual_def, mul_comm]
        apply ContinuousLinearMap.le_opNorm
      · simpa using ((NormedSpace.inclusionInDoubleDual 𝕜 𝕜) (m i)).ratio_le_opNorm 1)

variable (ι 𝕜) in
/-- Isometric version of `PiTensorProduct.constantBaseRingEquiv`. -/
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

/-- Continuous version of `PiTensorProduct.piTensorHomMap`. -/
noncomputable def piTensorHomMapL :
    (⨂[𝕜] i, E i →L[𝕜] E' i) →L[𝕜] (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  (liftIsometry 𝕜 _ _) (mapLMultilinear 𝕜 E E')

@[simp]
theorem piTensorHomMapL_tprod_tprod (f : Π i, E i →L[𝕜] E' i) (x : Π i, E i) :
    piTensorHomMapL (tprod 𝕜 f) (tprod 𝕜 x) = tprodL 𝕜 fun i ↦ f i (x i) := by
  simp [piTensorHomMapL, liftAux_tprod]

theorem piTensorHomMapL_tprod_eq_mapL (f : Π i, E i →L[𝕜] E' i) :
    piTensorHomMapL (tprod 𝕜 f) = mapL f := by
  simp [piTensorHomMapL, mapLMultilinear]

theorem opNorm_piTensorHomMapL_le : ‖piTensorHomMapL (𝕜 := 𝕜) (E := E) (E' := E')‖ ≤ 1 := by
  simp only [piTensorHomMapL, LinearIsometryEquiv.norm_map]
  apply MultilinearMap.mkContinuous_norm_le _ zero_le_one

/-- Continuous version of `PiTensorProduct.dualDistrib`. -/
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
