/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

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

* `PiTensorProduct.dualDistribL`: A continuous version of `PiTensorProduct.dualDistrib`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.mapLMultilinear_opNorm` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

* `projectiveSeminorm_tprod`. For normed spaces over `ℝ, ℂ`, the projective seminorm is
  multiplicative w.r.t. tensor products: `‖⨂ m i‖ = ∏ ‖m i‖`.

* `PiTensorProduct.projectiveSeminorm_of_bidual_iso`. TBD.

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
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simp only [smul_eq_mul, List.forall₂_map_right_iff, Function.comp_apply,
    List.forall₂_map_left_iff, map_smul, lift.tprod, List.forall₂_same, Prod.forall]
  intro a m _
  rw [norm_smul, ← mul_assoc, mul_comm ‖f‖ _, mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F)

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`. -/
@[simps]
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
  left_inv f := by ext; simp
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    ext; simp

/-- For a normed space `F`, we have constructed with `PiTensorProduct.liftEquiv` the canonical
linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
(induced by `PiTensorProduct.lift`). Here we upgrade this equivalence to an isometric linear
equivalence; in particular, it is a continuous linear equivalence. -/
noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  { liftEquiv 𝕜 E F with
    norm_map' f := by
      refine le_antisymm ?_ ?_
      · simp only [liftEquiv, lift_symm, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
        apply LinearMap.mkContinuous_norm_le _ (norm_nonneg f)
      · conv_lhs => rw [← (liftEquiv 𝕜 E F).symm_apply_apply f, liftEquiv_symm_apply]
        exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _ }

variable {𝕜 E F}

@[simp]
theorem liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x := by
  simp [liftIsometry]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
@[simps!]
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext; simp

@[simp]
theorem liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
    (liftIsometry 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  rfl

@[simp]
theorem liftIsometry_tprodL :
    liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext; simp

@[simp]
theorem opNorm_tprodL_eq_id :
    ‖tprodL (𝕜 := 𝕜) (E := E)‖ = ‖ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i)‖ :=
  LinearIsometryEquiv.norm_map _ _

section map

variable {E' E'' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

/--
Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.
-/
noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  liftIsometry 𝕜 E _ <| (tprodL 𝕜).compContinuousLinearMap f

@[simp]
theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
  ext; simp [mapL]

@[simp]
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`. -/
@[simp]
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) ↦ (p i).subtypeL

theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id

theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
    mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

-- We redeclare `ι` here, and later dependent arguments,
-- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
open Function in
private theorem mapL_add_smul_aux {ι : Type uι}
    {E : ι → Type uE} [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
    {E' : ι → Type u_1} [(i : ι) → SeminormedAddCommGroup (E' i)] [(i : ι) → NormedSpace 𝕜 (E' i)]
    (f : (i : ι) → E i →L[𝕜] E' i) [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
    (fun j ↦ (update f i u j).toLinearMap) =
      update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
  grind

open Function in
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext x
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

open Function in
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext x
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]

theorem mapL_opNorm : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
  conv_lhs => apply LinearIsometryEquiv.norm_map
  grw [ContinuousMultilinearMap.norm_compContinuousLinearMap_le,
    opNorm_tprodL_eq_id, ContinuousLinearMap.norm_id_le, one_mul]

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family. -/
@[simps!]
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
    ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f ↦ by rw [one_mul]; exact mapL_opNorm f)

variable {𝕜 E E'}

/-
#  WIP new material below.
--------------------------
-/

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

end map

/-
## Characterize the projective seminorm as an operator norm
-/
section dualCharacterization

/- Implementation note.

In the definition below, `ContinuousLinearMap.flip (liftIsometry 𝕜 E F)` also works.
But then the coercion to `ContinuousLinearMap` goes via `LinearIsometricEquiv` and
there's currently no analogue for `LinearIsometry.norm_toContinuousLinearMap_le`
for isometric equivalences. Should this be added? See
`norm_toContinuousLinearEquiv_toContinuousLinearMap_le` at bottom of file.  -/
variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`. -/
noncomputable def toDualContinuousMultilinearMapL :
    (⨂[𝕜] i, E i) →L[𝕜] ContinuousMultilinearMap 𝕜 E F →L[𝕜] F :=
  (liftIsometry 𝕜 E F).toLinearIsometry.toContinuousLinearMap.flip

@[simp]
theorem toDualContinuousMultilinearMapL_apply_apply
    (x : ⨂[𝕜] i, E i) (f : ContinuousMultilinearMap 𝕜 E F) :
    toDualContinuousMultilinearMapL F x f = liftIsometry 𝕜 E F f x := rfl

-- Analogue of `toDualContinuousMultilinearMap_le_projectiveSeminorm`
theorem norm_toDualContinuousMultilinearMapL_apply_le (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMapL F x‖ ≤ ‖x‖ := by
  grw [toDualContinuousMultilinearMapL, ContinuousLinearMap.le_opNorm,
    ContinuousLinearMap.opNorm_flip, LinearIsometry.norm_toContinuousLinearMap_le, one_mul]

/-- The projective seminorm of `x` is the maximum over operator norms
`‖toDualContinuousMultilinearMapL G x‖`, where `G` ranges over normed spaces
with universe level `(max uι u𝕜 uE)`.

(This characterizes the projective seminorm in terms of the previous Mathlib
definition of `injectiveSeminor`). -/
theorem projectiveSeminorm_dual_characterization (x : ⨂[𝕜] i, E i) : IsGreatest
    { p | ∃ (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
      p = ‖toDualContinuousMultilinearMapL G x‖ } ‖x‖ := by
  refine .intro ?_ (by simp_all [mem_upperBounds, norm_toDualContinuousMultilinearMapL_apply_le])
  simp only [Set.mem_setOf_eq]
  use (⨂[𝕜] i, E i), inferInstance, inferInstance
  refine le_antisymm ?_ (norm_toDualContinuousMultilinearMapL_apply_le x)
  have := ((toDualContinuousMultilinearMapL _) x).le_opNorm (tprodL 𝕜)
  grw [opNorm_tprodL_eq_id, ContinuousLinearMap.norm_id_le, mul_one] at this
  simpa

open NormedSpace in
/-- If `x` imbeds isometrically into the bidual, the projective seminorm is equal
to the operator norm `‖toDualContinuousMultilinearMapL 𝕜 x‖`. -/
theorem opNorm_eq_projectiveSeminorm_of_bidual_iso (x : ⨂[𝕜] i, E i)
    (h_iso : ‖inclusionInDoubleDual 𝕜 _ x‖ = ‖x‖) :
    ‖toDualContinuousMultilinearMapL 𝕜 x‖ = ‖x‖ := by
  refine le_antisymm (norm_toDualContinuousMultilinearMapL_apply_le x) ?_
  choose g lim using ContinuousLinearMap.exists_norming_sequence (inclusionInDoubleDual 𝕜 _ x)
  simp only [dual_def, h_iso] at lim
  refine le_of_tendsto' lim fun n ↦ ?_
  grw [← ContinuousLinearMap.ratio_le_opNorm _ ((liftIsometry 𝕜 E 𝕜).symm (g n))]
  simp only [LinearIsometryEquiv.norm_map, toDualContinuousMultilinearMapL_apply_apply,
    LinearIsometryEquiv.apply_symm_apply, le_refl]

end dualCharacterization

/-
## Sufficient conditions for the projective seminorm to factorize on product tensors
-/
section projectiveSeminorm_tprod

open Filter NormedSpace ContinuousLinearMap

/-- The projective seminorm is multiplicative w.r.t. tensor products: `‖⨂ m i‖ = ∏ ‖m i‖`
assuming that all `mᵢ` embed isometrically into the bidual.

TBD: Can assumptions be weakened further? Is this unconditionally true?
TBD: How does that relate to the norm of factorizing multilinear maps? -/
theorem projectiveSeminorm_tprod_of_bidual_iso
    (m : Π i, E i) (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ := by
  refine le_antisymm (projectiveSeminorm_tprod_le m) ?_
  choose g lim using fun i ↦ exists_norming_sequence (inclusionInDoubleDual 𝕜 _ (m i))
  simp only [dual_def, h_bidual] at lim
  refine le_ciInf (fun p ↦ le_of_tendsto' (tendsto_finset_prod _ (fun i _ ↦ lim i)) fun n ↦ ?_)
  have hp := congr_arg (fun x ↦ ‖dualDistrib (⨂ₜ[𝕜] i, g i n) x‖ / (∏ i, ‖g i n‖))
    ((mem_lifts_iff _ _).mp p.prop)
  simp only [dualDistrib_apply, coe_coe, norm_prod] at hp
  rw [Finset.prod_div_distrib, ← hp, map_list_sum, List.map_map]
  by_cases hz : ∏ i, ‖g i n‖ = 0
  · simp_all [projectiveSeminormAux_nonneg]
  · grw [div_le_iff₀' (by positivity), List.le_sum_of_subadditive norm norm_zero.le norm_add_le,
      List.map_map, projectiveSeminormAux, ← List.sum_map_mul_left]
    refine List.sum_le_sum (fun q _ ↦ ?_)
    simp only [Function.comp_apply, map_smul, dualDistrib_apply, coe_coe, smul_eq_mul, norm_mul,
      norm_prod, mul_left_comm, ← Finset.prod_mul_distrib]
    gcongr with i
    exact le_opNorm _ _

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

@[simp]
theorem projectiveSeminorm_tprod (m : Π i, E i) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_of_bidual_iso m (fun i ↦ (inclusionInDoubleDualLi 𝕜).norm_map (m i))

theorem opNorm_eq_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMapL 𝕜 x‖ = ‖x‖ :=
  opNorm_eq_projectiveSeminorm_of_bidual_iso x ((inclusionInDoubleDualLi 𝕜).norm_map x)

variable {E' : ι → Type*}
variable [∀ i, NormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable (f : Π i, E i →L[𝕜] E' i)

@[simp]
theorem mapL_opNorm_eq : ‖mapL f‖ = ∏ i, ‖f i‖ := by
  apply le_antisymm (mapL_opNorm _)
  choose g lim using fun i ↦ exists_norming_sequence (f i)
  apply le_of_tendsto' (tendsto_finset_prod _ (fun i _ ↦ lim i)) fun n ↦ ?_
  grw [← ratio_le_opNorm (mapL f) (⨂ₜ[𝕜] i, g i n)]
  simp only [Finset.prod_div_distrib, mapL_apply, map_tprod, coe_coe, projectiveSeminorm_tprod,
    le_refl]

end RCLike

end projectiveSeminorm_tprod

/-
Things become more experimental below.

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

open NormedSpace in
theorem projectiveSeminorm_tprod_field (m : ι → 𝕜) : ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_of_bidual_iso m
    fun i ↦ le_antisymm
      (double_dual_bound ..)
      (by simpa using ((inclusionInDoubleDual 𝕜 𝕜) (m i)).ratio_le_opNorm 1)

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

variable {E' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable (f : Π i, E i →L[𝕜] E' i)

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

end NontriviallyNormedField

end PiTensorProduct


/-
Analogue of `LinearIsometry.norm_toContinuousLinearMap_le` in Analysis/Normed/Operator/Basic.lean.

Wanted?
-/

namespace LinearIsometry

variable {𝕜 𝕜₂ E F : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
variable [RingHomInvPair σ₁₂ σ₂₁]
variable [RingHomInvPair σ₂₁ σ₁₂]

theorem norm_toContinuousLinearEquiv_toContinuousLinearMap_le (f : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖f.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp

end LinearIsometry
