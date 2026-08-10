/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!

# Inner product space structure on `PiTensorProduct`

This file provides the inner product space structure on tensor products of finite families
of inner product spaces.

The inner product on `⨂[𝕜] i, E i`, where `E` is a finite indexed family of `𝕜`-inner product
spaces, is defined by `⟪⨂ₜ[𝕜] i, a i, ⨂ₜ[𝕜] i, b i⟫ = ∏ i, ⟪a i, b i⟫` for pure tensors
and extended by linearity.

## Main definitions:

## TODO:

-/

@[expose] public section

variable {ι} {𝕜 : Type*} [RCLike 𝕜] [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

open scoped TensorProduct

namespace PiTensorProduct

noncomputable instance instInner : Inner 𝕜 (⨂[𝕜] i, E i) where
  inner x y := ((lift <| mapMultilinear E _ _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
    (map fun _ ↦ innerₛₗ 𝕜)) x y

lemma inner_def (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = ((lift <| mapMultilinear E _ _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
      (map fun _ ↦ innerₛₗ 𝕜)) x y := rfl

variable (𝕜) in
@[simp] theorem inner_tprod (x y : Π i, E i) :
    inner 𝕜 (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) = ∏ i, inner 𝕜 (x i) (y i) := by
  simp [inner_def]

-- This is a helper lemma for showing that this inner product is positive definite
-- and is superceded by `_root_.inner_add_left`.
private lemma inner_add_left (x y z : ⨂[𝕜] i, E i) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z := by simp [inner_def]

-- This is a helper lemma for showing that this inner product is positive definite
-- and is superceded by `_root_.inner_add_right`.
private lemma inner_add_right (x y z : ⨂[𝕜] i, E i) :
    inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z := by simp [inner_def]

@[simp]
theorem inner_map_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 (map (fun i ↦ (f i).toLinearMap) x) (map (fun i ↦ (f i).toLinearMap) y) = inner 𝕜 x y :=
  x.induction_on
    (y.induction_on (by simp [inner_def]) (by simp_all [inner_add_right]))
    (by simp_all [inner_add_left])

theorem inner_mapIncl_mapIncl (p : Π i, Submodule 𝕜 (E i)) (x y : ⨂[𝕜] i, p i) :
    inner 𝕜 (mapIncl p x) (mapIncl p y) = inner 𝕜 x y :=
  inner_map_map (fun i ↦ (p i).subtypeₗᵢ) x y

@[simp]
theorem inner_of_isEmpty [IsEmpty ι] (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = starRingEnd 𝕜 (isEmptyEquiv ι x) * isEmptyEquiv ι y :=
  x.induction_on
    (y.induction_on (by simp_all [inner_def, mul_comm]) (by simp_all [inner_add_right, mul_add]))
    (by simp_all [inner_add_left, add_mul])

theorem inner_of_subsingleton [Subsingleton ι] (i₀ : ι) (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = inner 𝕜 (subsingletonEquiv i₀ x) (subsingletonEquiv i₀ y) :=
  x.induction_on
    (y.induction_on
      (by simp [inner_def, inner_smul_left, inner_smul_right, Fintype.prod_subsingleton _ i₀])
      (by simp_all [inner_add_right, _root_.inner_add_right]))
    (by simp_all [inner_add_left, _root_.inner_add_left])

open scoped Classical in
private theorem inner_self {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (b : Π i, OrthonormalBasis (κ i) 𝕜 (E i)) (x : ⨂[𝕜] i, E i) :
    inner 𝕜 x x = ∑ s, ‖(Basis.piTensorProduct fun i ↦ (b i).toBasis).repr x s‖ ^ 2 := by
  let b' := Basis.piTensorProduct fun i ↦ (b i).toBasis
  have hx : x = ∑ s, b'.repr x s • ⨂ₜ[𝕜] i, b i (s i) := by
    nth_rw 1 [← b'.sum_repr x]
    simp [b', Basis.piTensorProduct_apply]
  conv_lhs => rw [hx]
  have hprod (s s' : Π i, κ i) : ∏ i, ite (s i = s' i) (1 : 𝕜) 0 = ite (s = s') 1 0 := by
    rcases eq_or_ne s s' with rfl | hs
    · simp only [↓reduceIte, Finset.prod_const_one]
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
      simp only [hs, ↓reduceIte]
      exact Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_univ j, by simp [hj]⟩
  trans ∑ s, ‖b'.repr x s‖ ^ 2
  · simp [inner_def, OrthonormalBasis.inner_eq_ite, hprod, RCLike.mul_conj]
  simp_rw [map_sum, map_pow]
  congr

-- TODO: Move this to an appropriate file and generalize to CommSemiring
open Submodule in
omit [Fintype ι] in
theorem exists_finite_submodule_of_setFinite (s : Set (⨂[𝕜] i, E i)) (hs : s.Finite) :
    ∃ M : Π i, Submodule 𝕜 (E i), (∀ i, Module.Finite 𝕜 (M i)) ∧ s ⊆ (mapIncl M).range := by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨fun _ ↦ ⊥, fun _ ↦ fg_bot, Set.empty_subset _⟩
  | @insert x s hx _ ih =>
    obtain ⟨M', hM', hsM'⟩ := ih
    refine x.induction_on (fun r u ↦ ?_) fun y z hy hz ↦ ?_
    · refine ⟨fun i ↦ M' i ⊔ 𝕜 ∙ u i, fun i ↦ (hM' i).sup (fg_span_singleton _), ?_⟩
      apply Set.insert_subset
      · exact ⟨r • ⨂ₜ[𝕜] i, ⟨u i, mem_sup_right (mem_span_singleton_self _)⟩, by simp⟩
      · exact fun y hy ↦ range_mapIncl_mono (fun _ ↦ le_sup_left) (hsM' hy)
    · obtain ⟨My', hMy', hys⟩ := hy
      obtain ⟨Mz', hMz', hzs⟩ := hz
      refine ⟨fun i ↦ My' i ⊔ Mz' i, fun i ↦ (hMy' i).sup (hMz' i), ?_⟩
      refine Set.insert_subset (add_mem ?_ ?_) fun w hw ↦ ?_
      · exact range_mapIncl_mono (fun _ ↦ le_sup_left) (hys <| Set.mem_insert y s)
      · exact range_mapIncl_mono (fun _ ↦ le_sup_right) (hzs <| Set.mem_insert z s)
      · exact range_mapIncl_mono (fun _ ↦ le_sup_right) (hzs <| Set.mem_insert_of_mem z hw)

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (⨂[𝕜] i, E i) :=
  letI : InnerProductSpace.Core 𝕜 (⨂[𝕜] i, E i) :=
  { conj_inner_symm x y := x.induction_on
      (fun _ _ ↦ y.induction_on
        (by simp_all [inner_def, mul_left_comm])
        (by simp_all [inner_add_left, inner_add_right]))
      (by simp_all [inner_def])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
    definite x hx := by
      obtain ⟨M, hM, hxM⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
      let b := fun i ↦ stdOrthonormalBasis 𝕜 (M i)
      obtain ⟨y, hy⟩ := Set.singleton_subset_iff.mp hxM
      suffices y = 0 by exact hy ▸ this ▸ map_zero _
      simp only [← hy, inner_mapIncl_mapIncl, inner_self b, RCLike.ofReal_eq_zero,
        Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _), Finset.mem_univ, sq_eq_zero_iff,
        norm_eq_zero, forall_const] at hx
      apply (Basis.piTensorProduct fun i ↦ (b i).toBasis).ext_elem_iff.mpr
      simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    re_inner_nonneg x := by
      obtain ⟨M, hM, hxM⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
      let b := fun i ↦ stdOrthonormalBasis 𝕜 (M i)
      obtain ⟨y, hy⟩ := Set.singleton_subset_iff.mp hxM
      rw [← hy, inner_mapIncl_mapIncl, inner_self b, RCLike.ofReal_re]
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _}
  this.toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (⨂[𝕜] i, E i) := .ofCore _

@[simp] theorem norm_tprod (x : Π i, E i) :
    ‖⨂ₜ[𝕜] i, x i‖ = ∏ i, ‖x i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).mp
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re,
    ← RCLike.ofReal_prod, Finset.prod_pow] using congr(RCLike.re $(inner_tprod 𝕜 x x))

@[simp] theorem nnnorm_tprod (x : Π i, E i) :
    ‖⨂ₜ[𝕜] i, x i‖₊ = ∏ i, ‖x i‖₊ := by simp [← NNReal.coe_inj]

@[simp] theorem enorm_tprod (x : Π i, E i) :
    ‖⨂ₜ[𝕜] i, x i‖ₑ = ∏ i, ‖x i‖ₑ := by simp [enorm_eq_nnnorm]

theorem dist_tprod_le (x y : Π i, E i) :
    dist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖ + ∏ i, ‖y i‖ := by
  grw [dist_eq_norm, norm_sub_le]; simp

theorem nndist_tprod_le (x y : Π i, E i) :
    nndist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖₊ + ∏ i, ‖y i‖₊ := by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

theorem edist_tprod_le (x y : Π i, E i) :
    edist (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) ≤ ∏ i, ‖x i‖ₑ + ∏ i, ‖y i‖ₑ := by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

section isometries

noncomputable def mapIsometry (f : Π i, E i →ₗᵢ[𝕜] F i) : (⨂[𝕜] i, E i) →ₗᵢ[𝕜] ⨂[𝕜] i, F i :=
  map (fun i ↦ (f i).toLinearMap) |>.isometryOfInner <| inner_map_map _

@[simp] lemma mapIsometry_apply (f : Π i, E i →ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i) :
    mapIsometry f x = map (fun i ↦ (f i).toLinearMap) x := rfl

@[simp] lemma toLinearMap_mapIsometry (f : Π i, E i →ₗᵢ[𝕜] F i) :
    (mapIsometry f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := rfl

@[simp] lemma norm_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i) :
    ‖map (fun i ↦ (f i).toLinearMap) x‖ = ‖x‖ := (mapIsometry f).norm_map x

@[simp] lemma nnnorm_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i) :
    ‖map (fun i ↦ (f i).toLinearMap) x‖₊ = ‖x‖₊ := (mapIsometry f).nnnorm_map x

@[simp] lemma enorm_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i) :
    ‖map (fun i ↦ (f i).toLinearMap) x‖ₑ = ‖x‖ₑ := (mapIsometry f).enorm_map x

@[simp] lemma mapIsometry_id :
    mapIsometry (fun i ↦ (.id : E i →ₗᵢ[𝕜] E i)) = .id := by ext; simp

noncomputable def congrIsometry (f : Π i, E i ≃ₗᵢ[𝕜] F i) : (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] ⨂[𝕜] i, F i :=
  congr (fun i ↦ (f i).toLinearEquiv) |>.isometryOfInner <|
    inner_map_map (fun i ↦ (f i).toLinearIsometry)

@[simp] lemma congrIsometry_apply (f : Π i, E i ≃ₗᵢ[𝕜] F i) (x : ⨂[𝕜] i, E i) :
    congrIsometry f x = congr (fun i ↦ (f i).toLinearEquiv) x := rfl

lemma congrIsometry_symm (f : Π i, E i ≃ₗᵢ[𝕜] F i) :
    (congrIsometry f).symm = congrIsometry (fun i ↦ (f i).symm) := rfl

@[simp] lemma toLinearEquiv_congrIsometry (f : Π i, E i ≃ₗᵢ[𝕜] F i) :
    (congrIsometry f).toLinearEquiv = congr (fun i ↦ (f i).toLinearEquiv) := rfl

@[simp] lemma congrIsometry_refl :
    congrIsometry (fun i ↦ .refl 𝕜 (E i)) = .refl 𝕜 (⨂[𝕜] i, E i) :=
  LinearIsometryEquiv.toLinearEquiv_inj.mp <| LinearEquiv.toLinearMap_inj.mp <| by ext; simp

noncomputable def mapInclIsometry (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →ₗᵢ[𝕜] ⨂[𝕜] i, E i :=
  mapIsometry fun i ↦ (p i).subtypeₗᵢ

@[simp] lemma mapInclIsometry_apply (p : Π i, Submodule 𝕜 (E i)) (x : ⨂[𝕜] i, p i) :
    mapInclIsometry p x = mapIncl p x := rfl

@[simp] lemma toLinearMap_mapInclIsometry (p : Π i, Submodule 𝕜 (E i)) :
    (mapInclIsometry p).toLinearMap = mapIncl p := rfl

section reindex

variable {ι₂} [Fintype ι₂]

variable (𝕜 E) in
noncomputable def reindexIsometry (e : ι ≃ ι₂) :
    (⨂[𝕜] i : ι, E i) ≃ₗᵢ[𝕜] ⨂[𝕜] i : ι₂, E (e.symm i) :=
  (reindex 𝕜 E e).isometryOfInner fun x y ↦ x.induction_on
    (y.induction_on
      (fun _ u _ v ↦ by
        simp [inner_smul_left, inner_smul_right, Equiv.prod_comp _ fun i ↦ inner 𝕜 (v i) (u i)])
      (by simp_all [inner_add_right]))
    (by simp_all [inner_add_left])

@[simp] lemma reindexIsometry_apply (e : ι ≃ ι₂) (x : ⨂[𝕜] i : ι, E i) :
    reindexIsometry 𝕜 E e x = reindex 𝕜 E e x := rfl

@[simp] lemma reindexIsometry_refl : reindexIsometry 𝕜 E (.refl ι) = .refl 𝕜 _ := by
  ext
  rw [reindexIsometry_apply, reindex_refl]
  congr

end reindex

section isEmpty

variable (ι) [IsEmpty ι]

noncomputable def isEmptyIsometry : (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] 𝕜 :=
  isEmptyEquiv ι |>.isometryOfInner <| by simp [mul_comm]

@[simp] lemma isEmptyIsometry_apply (x : ⨂[𝕜] i, E i) : isEmptyIsometry ι x = isEmptyEquiv ι x :=
  rfl

end isEmpty

section subsingleton

variable [Subsingleton ι] (i₀ : ι)

noncomputable def subsingletonIsometry : (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] E i₀ :=
  subsingletonEquiv i₀ |>.isometryOfInner <| fun x y ↦ x.induction_on
    (y.induction_on
      (by simp [inner_smul_right, inner_smul_left, Fintype.prod_subsingleton _ i₀])
      (by simp_all [_root_.inner_add_right]))
    (by simp_all [_root_.inner_add_left])

@[simp] lemma subsingletonIsometry_apply (x : ⨂[𝕜] i, E i) :
    subsingletonIsometry i₀ x = subsingletonEquiv i₀ x := rfl

end subsingleton

end isometries

end PiTensorProduct
