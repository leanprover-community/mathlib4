/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.LinearAlgebra.Isomorphisms

deprecated_module
  "https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/injectiveSeminorm/with/568798633"
  (since := "2026-01-19")

/-!
# Injective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a nontrivially normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"injective seminorm". It is chosen to satisfy the following property: for every
normed `𝕜`-vector space `F`, the linear equivalence
`MultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, Eᵢ) →ₗ[𝕜] F`
expressing the universal property of the tensor product induces an isometric linear equivalence
`ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, Eᵢ) →L[𝕜] F`.

The idea is the following: Every normed `𝕜`-vector space `F` defines a linear map
from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] F`, which sends `x` to the map
`f ↦ f.lift x`. Thanks to `PiTensorProduct.norm_eval_le_projectiveSeminorm`, this map lands in
`ContinuousMultilinearMap 𝕜 E F →L[𝕜] F`. As this last space has a natural operator (semi)norm,
we get an induced seminorm on `⨂[𝕜] i, Eᵢ`, which, by
`PiTensorProduct.norm_eval_le_projectiveSeminorm`, is bounded above by the projective seminorm
`PiTensorProduct.projectiveSeminorm`. We then take the `sup` of these seminorms as `F` varies;
as this family of seminorms is bounded, its `sup` has good properties.

In fact, we cannot take the `sup` over all normed spaces `F` because of set-theoretical issues,
so we only take spaces `F` in the same universe as `⨂[𝕜] i, Eᵢ`. We prove in
`norm_eval_le_injectiveSeminorm` that this gives the same result, because every multilinear map
from `E = Πᵢ Eᵢ` to `F` factors though a normed vector space in the same universe as
`⨂[𝕜] i, Eᵢ`.

We then prove the universal property and the functoriality of `⨂[𝕜] i, Eᵢ` as a normed vector
space.

## Main definitions

* `PiTensorProduct.toDualContinuousMultilinearMap`: The `𝕜`-linear map from
  `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending `x` to the map
  `f ↦ f x`.
* `PiTensorProduct.injectiveSeminorm`: The injective seminorm on `⨂[𝕜] i, Eᵢ`.
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

* `PiTensorProduct.norm_eval_le_injectiveSeminorm`: The main property of the injective seminorm
  on `⨂[𝕜] i, Eᵢ`: for every `x` in `⨂[𝕜] i, Eᵢ` and every continuous multilinear map `f` from
`E = Πᵢ Eᵢ` to a normed space `F`, we have `‖f.lift x‖ ≤ ‖f‖ * injectiveSeminorm x `.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.mapLMultilinear_opNorm` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO

* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm. This uses the construction of a basis of the `PiTensorProduct`, hence
  depends on PR https://github.com/leanprover-community/mathlib4/pull/11156.
  It should probably go in a separate file.

* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

@[expose] public section

universe uι u𝕜 uE uF

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

namespace PiTensorProduct

variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`.
-/
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuous
    ((LinearMap.flip (lift (R := 𝕜) (s := E) (E := F)).toLinearMap x) ∘ₗ
    ContinuousMultilinearMap.toMultilinearMapLinear)
    (projectiveSeminorm x)
    (fun _ ↦ by simp only [LinearMap.coe_comp, Function.comp_apply,
                  ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.flip_apply,
                  LinearEquiv.coe_coe, mul_comm]
                exact norm_eval_le_projectiveSeminorm _ _)
  map_add' x y := by
    ext _
    simp only [map_add, LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.add_apply,
      LinearMap.flip_apply, LinearEquiv.coe_coe, ContinuousLinearMap.add_apply]
  map_smul' a x := by
    ext _
    simp only [map_smul, LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, LinearEquiv.coe_coe, RingHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply]

theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMap F x‖ ≤ projectiveSeminorm x := by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (apply_nonneg _ _)

/-- The injective seminorm on `⨂[𝕜] i, Eᵢ`. Morally, it sends `x` in `⨂[𝕜] i, Eᵢ` to the
`sup` of the operator norms of the `PiTensorProduct.toDualContinuousMultilinearMap F x`, for all
normed vector spaces `F`. In fact, we only take in the same universe as `⨂[𝕜] i, Eᵢ`, and then
prove in `PiTensorProduct.norm_eval_le_injectiveSeminorm` that this gives the same result.
-/
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-01-19")]
noncomputable irreducible_def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2026-01-19")]
lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))} := by
  existsi projectiveSeminorm
  rw [mem_upperBounds]
  simp only [Set.mem_setOf_eq, forall_exists_index]
  intro p G _ _ hp
  rw [hp]
  intro x
  simp only [Seminorm.comp_apply, coe_normSeminorm]
  exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

set_option linter.deprecated false in
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-01-19")]
theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}, p.1 x := by
  simpa only [injectiveSeminorm, Set.coe_setOf, Set.mem_setOf_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2026-01-19")]
lemma projectiveSeminorn_mem_dualSeminorms : projectiveSeminorm ∈ {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G)} := by
  use (⨂[𝕜] i, E i), inferInstance, inferInstance
  ext x
  refine le_antisymm ?_ (toDualContinuousMultilinearMap_le_projectiveSeminorm x)
  have hn : ‖tprodL 𝕜 (E := E)‖ ≤ 1 := ContinuousMultilinearMap.opNorm_le_bound
    zero_le_one fun m ↦ by simp [projectiveSeminorm_tprod_le]
  have := ContinuousLinearMap.le_opNorm ((toDualContinuousMultilinearMap _) x) (tprodL 𝕜)
  grw [hn, mul_one] at this
  simpa

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2026-01-19")]
theorem injectiveSeminorm_eq_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) = projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine le_antisymm (csSup_le ⟨_, projectiveSeminorn_mem_dualSeminorms⟩ fun p ⟨G, _, _, h⟩ x ↦ ?_)
    (le_csSup_of_le dualSeminorms_bounded projectiveSeminorn_mem_dualSeminorms (le_refl _))
  simp [h, toDualContinuousMultilinearMap_le_projectiveSeminorm]

set_option linter.deprecated false in
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-01-19")]
theorem norm_eval_le_injectiveSeminorm (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x := by
    rw [injectiveSeminorm_eq_projectiveSeminorm]
    change ‖(lift f.toMultilinearMap) x‖ ≤ ‖f‖ * ‖x‖
    apply norm_eval_le_projectiveSeminorm

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2026-01-19")]
theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) ≤ projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_setOf_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(max (max uE uι) u𝕜) + 1} x) 0,
      norm_zero]
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    obtain ⟨G, _, _, h⟩ := hp
    rw [h]; intro x; simp only [Seminorm.comp_apply, coe_normSeminorm]
    exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

set_option linter.deprecated false in
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-01-19")]
theorem injectiveSeminorm_tprod_le (m : Π (i : ι), E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ :=
  le_trans (injectiveSeminorm_le_projectiveSeminorm _) (projectiveSeminorm_tprod_le m)

end seminorm

end PiTensorProduct
