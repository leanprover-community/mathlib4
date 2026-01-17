/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

/-!
# An alternative characterization of the projective seminorm.

Nothing builds on this file. It could be removed.

## Main definitions

* `PiTensorProduct.injectiveSeminorm`: A "dual" definition of the projective seminorm.

## Main results

* `PiTensorProduct.injectiveSeminorm_eq_projectiveSeminorm`: The dual definition
   agrees with the primal definition
-/

set_option linter.privateModule false

open scoped TensorProduct

namespace PiTensorProduct

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι] {𝕜 : Type u𝕜}
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)]
variable [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

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

end PiTensorProduct
