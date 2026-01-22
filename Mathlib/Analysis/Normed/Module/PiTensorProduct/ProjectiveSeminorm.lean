/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.liftEquiv`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous multilinear map from `E = Πᵢ Eᵢ`
  to `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.mapL`: The continuous linear map from `⨂[𝕜] i, Eᵢ` to `⨂[𝕜] i, E'ᵢ`
  induced by a family of continuous linear maps `Eᵢ →L[𝕜] E'ᵢ`.
* `PiTensorProduct.mapLMultilinear`: The continuous multilinear map from
  `Πᵢ (Eᵢ →L[𝕜] E'ᵢ)` to `(⨂[𝕜] i, Eᵢ) →L[𝕜] (⨂[𝕜] i, E'ᵢ)` sending a family
  `f` to `PiTensorProduct.mapL f`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.mapLMultilinear_opNorm` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO

* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι] {𝕜 : Type u𝕜}
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)]

section NormedField

variable [NormedField 𝕜]

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`. -/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
  fun p ↦ (p.toList.map (fun p ↦ ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 ≤ projectiveSeminormAux p := by
  refine List.sum_nonneg fun a ↦ ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  rw [← h]
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))

theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp [projectiveSeminormAux]

theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) ↦ (a * y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

variable [∀ i, NormedSpace 𝕜 (E i)]

theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.val)) :=
  ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

noncomputable instance : Norm (⨂[𝕜] i, E i) :=
  ⟨fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val)⟩

theorem norm_def (x : ⨂[𝕜] i, E i) :
    ‖x‖ = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val) := rfl

theorem projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0 :=
  le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.val))

theorem projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x+y‖ ≤ ‖x‖ + ‖y‖ :=
  le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

theorem projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p ↦ ?_
  rw [← projectiveSeminormAux_smul]
  exact ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`. -/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := .ofSMulLE
    _ projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) := ⟨projectiveSeminorm_smul_le⟩

theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    ‖(⨂ₜ[𝕜] i, m i)‖ ≤ ∏ i, ‖m i‖ := by
  convert ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨FreeAddMonoid.of ((1 : 𝕜), m), ?_⟩
  · simp [projectiveSeminormAux]
  · simp [mem_lifts_iff]

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * ‖x‖ := by
  rw [norm_def, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ ↦ ?_
  simp_rw [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  refine le_trans (norm_multiset_sum_le _) ?_
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simp only [smul_eq_mul, List.forall₂_map_right_iff, Function.comp_apply,
    List.forall₂_map_left_iff, map_smul, lift.tprod, List.forall₂_same, Prod.forall]
  intro a m _
  rw [norm_smul, ← mul_assoc, mul_comm ‖f‖ _, mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

end NontriviallyNormedField

end PiTensorProduct
