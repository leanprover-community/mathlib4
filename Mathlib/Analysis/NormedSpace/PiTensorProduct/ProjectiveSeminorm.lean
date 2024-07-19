/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a nontrivially normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
`E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.

## TODO
* If the base field is `ℝ` or `ℂ` (or more generally if the injection of `Eᵢ` into its bidual is
an isometry for every `i`), then we have `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`.

* The functoriality.

-/

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

namespace PiTensorProduct

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`.
-/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
  List.sum ∘ (List.map (fun p ↦ ‖p.1‖ * ∏ i, ‖p.2 i‖))

theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 ≤ projectiveSeminormAux p := by
  simp only [projectiveSeminormAux, Function.comp_apply]
  refine List.sum_nonneg ?_
  intro a
  simp only [Multiset.map_coe, Multiset.mem_coe, List.mem_map, Prod.exists, forall_exists_index,
    and_imp]
  intro x m _ h
  rw [← h]
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))

theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp only [projectiveSeminormAux, Function.comp_apply, Multiset.map_coe, Multiset.sum_coe]
  erw [List.map_append]
  rw [List.sum_append]
  rfl

theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (List.map (fun (y : 𝕜 × Π i, E i) ↦ (a * y.1, y.2)) p) =
    ‖a‖ * projectiveSeminormAux p := by
  simp only [projectiveSeminormAux, Function.comp_apply, Multiset.map_coe, List.map_map,
    Multiset.sum_coe]
  rw [← smul_eq_mul, List.smul_sum, ← List.comp_map]
  congr 2
  ext x
  simp only [Function.comp_apply, norm_mul, smul_eq_mul]
  rw [mul_assoc]

theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) := by
  existsi 0
  rw [mem_lowerBounds]
  simp only [Set.mem_range, Subtype.exists, exists_prop, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact fun p _ ↦ projectiveSeminormAux_nonneg p

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.
-/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := by
  refine Seminorm.ofSMulLE (fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) ?_ ?_ ?_
  · refine le_antisymm ?_ ?_
    · refine ciInf_le_of_le (bddBelow_projectiveSemiNormAux (0 : ⨂[𝕜] i, E i)) ⟨0, lifts_zero⟩ ?_
      simp only [projectiveSeminormAux, Function.comp_apply]
      rw [List.sum_eq_zero]
      intro _
      simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
      intro _ _ hxm
      rw [← FreeAddMonoid.ofList_nil] at hxm
      exfalso
      exact List.not_mem_nil _ hxm
    · letI : Nonempty (lifts 0) := ⟨0, lifts_zero (R := 𝕜) (s := E)⟩
      exact le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.1)
  · intro x y
    letI := nonempty_subtype.mpr (nonempty_lifts x); letI := nonempty_subtype.mpr (nonempty_lifts y)
    exact le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
      ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))
  · intro a x
    letI := nonempty_subtype.mpr (nonempty_lifts x)
    rw [Real.mul_iInf_of_nonneg (norm_nonneg _)]
    refine le_ciInf ?_
    intro p
    rw [← projectiveSeminormAux_smul]
    exact ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
      ⟨(List.map (fun y ↦ (a * y.1, y.2)) p.1), lifts_smul p.2 a⟩ (le_refl _)

theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1) := rfl

theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
  rw [projectiveSeminorm_apply]
  convert ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨[((1 : 𝕜), m)] ,?_⟩
  · simp only [projectiveSeminormAux, Function.comp_apply, List.map_cons, norm_one, one_mul,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  · rw [mem_lifts_iff, List.map_singleton, List.sum_singleton, one_smul]

theorem norm_eval_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) (G : Type*) [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖lift f.toMultilinearMap x‖ ≤ projectiveSeminorm x * ‖f‖ := by
  letI := nonempty_subtype.mpr (nonempty_lifts x)
  rw [projectiveSeminorm_apply, Real.iInf_mul_of_nonneg (norm_nonneg _), projectiveSeminormAux]
  refine le_ciInf ?_
  intro ⟨p, hp⟩
  rw [mem_lifts_iff] at hp
  conv_lhs => rw [← hp, ← List.sum_map_hom, ← Multiset.sum_coe]
  refine le_trans (norm_multiset_sum_le _) ?_
  simp only [tprodCoeff_eq_smul_tprod, Multiset.map_coe, List.map_map, Multiset.sum_coe,
    Function.comp_apply]
  rw [mul_comm, ← smul_eq_mul, List.smul_sum]
  refine List.Forall₂.sum_le_sum ?_
  simp only [smul_eq_mul, List.map_map, List.forall₂_map_right_iff, Function.comp_apply,
    List.forall₂_map_left_iff, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
    List.forall₂_same, Prod.forall]
  intro a m _
  rw [norm_smul, ← mul_assoc, mul_comm ‖f‖ _, mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

end PiTensorProduct
