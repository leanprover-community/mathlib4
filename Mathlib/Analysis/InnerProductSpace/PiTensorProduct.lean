/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!

# Inner product space structure on `PiTensorProduct`

This file provides the inner product space structure on pi tensor products.

For an indexed family `E` of `𝕜`-inner product spaces, the inner product on `⨂[𝕜] i, E i` is the
unique sesquilinear map given by `⟪⨂ₜ[𝕜] i, a i, ⨂ₜ[𝕜] i, b i⟫ = ∏ i, ⟪a i, b i⟫` on pure tensors.

-/

@[expose] public section

namespace PiTensorProduct

open scoped InnerProductSpace TensorProduct

variable {𝕜} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

noncomputable instance instInner : Inner 𝕜 (⨂[𝕜] i, E i) where
  inner x y := ((lift <| mapMultilinear 𝕜 E _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
    (map fun _ ↦ innerₛₗ 𝕜)) x y

lemma inner_def (x y : ⨂[𝕜] i, E i) :
    ⟪x, y⟫_𝕜 = ((lift <| mapMultilinear 𝕜 E _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
      (map fun _ ↦ innerₛₗ 𝕜)) x y :=
  rfl

variable (𝕜) in
@[simp]
theorem inner_tprod (x y : Π i, E i) : ⟪⨂ₜ[𝕜] i, x i, ⨂ₜ[𝕜] i, y i⟫_𝕜 = ∏ i, ⟪x i, y i⟫_𝕜 := by
  simp [inner_def]

-- This is a helper lemma for establishing `InnerProductSpace.Core`
-- and is superceded by `_root_.inner_add_left`.
private lemma inner_add_left (x y z : ⨂[𝕜] i, E i) : ⟪x + y, z⟫_𝕜 = ⟪x, z⟫_𝕜 + ⟪y, z⟫_𝕜 := by
  simp [inner_def]

-- This is a helper lemma for establishing `InnerProductSpace.Core`
-- and is superceded by `_root_.inner_add_right`.
private lemma inner_add_right (x y z : ⨂[𝕜] i, E i) : ⟪x, y + z⟫_𝕜 = ⟪x, y⟫_𝕜 + ⟪x, z⟫_𝕜 := by
  simp [inner_def]

@[simp]
theorem inner_map_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x y : ⨂[𝕜] i, E i) :
    ⟪map (fun i ↦ (f i).toLinearMap) x, map (fun i ↦ (f i).toLinearMap) y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  x.induction_on (y.induction_on (by simp [inner_def]) (by simp_all [inner_add_right]))
    (by simp_all [inner_add_left])

theorem inner_mapIncl_mapIncl {p : Π i, Submodule 𝕜 (E i)} (x y : ⨂[𝕜] i, p i) :
    ⟪mapIncl p x, mapIncl p y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  inner_map_map (fun i ↦ (p i).subtypeₗᵢ) x y

open scoped Classical in
private theorem inner_self {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (b : Π i, OrthonormalBasis (κ i) 𝕜 (E i)) (x : ⨂[𝕜] i, E i) :
    ⟪x, x⟫_𝕜 = ∑ (s : Π i, κ i), ‖(Basis.piTensorProduct fun i ↦ (b i).toBasis).repr x s‖ ^ 2 := by
  let b' := Basis.piTensorProduct fun i ↦ (b i).toBasis
  have hx : x = ∑ s, b'.repr x s • ⨂ₜ[𝕜] i, b i (s i) := by nth_rw 1 [← b'.sum_repr x]; simp [b']
  conv_lhs => rw [hx]
  simp [inner_def, OrthonormalBasis.inner_eq_ite, Fintype.prod_boole, ← funext_iff,
    RCLike.mul_conj, b']

noncomputable instance : InnerProductSpace.Core 𝕜 (⨂[𝕜] i, E i) where
  conj_inner_symm x y := x.induction_on
      (fun _ _ ↦ y.induction_on
        (by simp_all [inner_def, mul_left_comm])
        (by simp_all [inner_add_left, inner_add_right]))
      (by simp_all [inner_def])
  add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
  smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
  definite x hx := by
    obtain ⟨p, _, hp⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
    obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hp
    suffices y = 0 by exact this ▸ map_zero _
    simp only [inner_mapIncl_mapIncl, inner_self fun i ↦ stdOrthonormalBasis 𝕜 (p i),
      RCLike.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _),
      Finset.mem_univ, sq_eq_zero_iff, norm_eq_zero, forall_const] at hx
    exact (Basis.piTensorProduct _).ext_elem_iff.mpr hx
  re_inner_nonneg x := by
    obtain ⟨p, _, hp⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
    obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hp
    rw [inner_mapIncl_mapIncl, inner_self fun i ↦ stdOrthonormalBasis 𝕜 (p i), RCLike.ofReal_re]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (⨂[𝕜] i, E i) :=
  instCore.toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (⨂[𝕜] i, E i) := .ofCore _

@[simp]
theorem norm_tprod (x : Π i, E i) : ‖⨂ₜ[𝕜] i, x i‖ = ∏ i, ‖x i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).mp
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re,
    ← RCLike.ofReal_prod, Finset.prod_pow] using congr(RCLike.re $(inner_tprod 𝕜 x x))

@[simp]
theorem nnNorm_tprod (x : Π i, E i) : ‖⨂ₜ[𝕜] i, x i‖₊ = ∏ i, ‖x i‖₊ := by simp [← NNReal.coe_inj]

@[simp]
theorem eNorm_tprod (x : Π i, E i) : ‖⨂ₜ[𝕜] i, x i‖ₑ = ∏ i, ‖x i‖ₑ := by simp [eNorm_eq_nnNorm]

theorem dist_tprod_le (x y : Π i, E i) :
    dist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖ + ∏ i, ‖y i‖ := by
  grw [dist_eq_norm, norm_sub_le]
  simp

theorem nnDist_tprod_le (x y : Π i, E i) :
    nndist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖₊ + ∏ i, ‖y i‖₊ := by
  grw [nnDist_eq_nnNorm, nnNorm_sub_le]
  simp

theorem eDist_tprod_le (x y : Π i, E i) :
    edist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖ₑ + ∏ i, ‖y i‖ₑ := by
  grw [eDist_eq_eNorm_sub, eNorm_sub_le]
  simp

section MapIsometry

variable (f : Π i, E i →ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i)

noncomputable def mapIsometry : (⨂[𝕜] i, E i) →ₗᵢ[𝕜] ⨂[𝕜] i, F i :=
  map (fun i ↦ (f i).toLinearMap) |>.isometryOfInner (inner_map_map f)

@[simp]
lemma mapIsometry_apply : mapIsometry f x = map (fun i ↦ (f i).toLinearMap) x := rfl

@[simp]
lemma toLinearMap_mapIsometry : (mapIsometry f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := rfl

@[simp]
lemma norm_map : ‖map (fun i ↦ (f i).toLinearMap) x‖ = ‖x‖ := (mapIsometry f).norm_map x

@[simp]
lemma nnNorm_map : ‖map (fun i ↦ (f i).toLinearMap) x‖₊ = ‖x‖₊ := (mapIsometry f).nnNorm_map x

@[simp]
lemma eNorm_map : ‖map (fun i ↦ (f i).toLinearMap) x‖ₑ = ‖x‖ₑ := (mapIsometry f).eNorm_map x

@[simp]
lemma mapIsometry_id : mapIsometry (fun i ↦ (.id : E i →ₗᵢ[𝕜] E i)) = .id := by ext; simp

end MapIsometry

section CongrIsometry

variable (f : Π i, E i ≃ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i)

noncomputable def congrIsometry : (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] ⨂[𝕜] i, F i :=
  congr (fun i ↦ (f i).toLinearEquiv) |>.isometryOfInner
    <| inner_map_map (fun i ↦ (f i).toLinearIsometry)

@[simp]
lemma congrIsometry_apply : congrIsometry f x = congr (fun i ↦ (f i).toLinearEquiv) x := rfl

lemma congrIsometry_symm : (congrIsometry f).symm = congrIsometry (fun i ↦ (f i).symm) := rfl

@[simp]
lemma toLinearEquiv_congrIsometry :
    (congrIsometry f).toLinearEquiv = congr (fun i ↦ (f i).toLinearEquiv) := rfl

@[simp]
lemma congrIsometry_refl : congrIsometry (fun i ↦ .refl 𝕜 (E i)) = .refl 𝕜 (⨂[𝕜] i, E i) :=
  LinearIsometryEquiv.toLinearEquiv_inj.mp <| LinearEquiv.toLinearMap_inj.mp <| by ext; simp

end CongrIsometry

end PiTensorProduct
