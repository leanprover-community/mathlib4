/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Topology.Instances.RealVectorSpace


/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/


noncomputable section

open NNReal Topology

open Filter

variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

open AffineMap

@[simp]
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂ := by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]
theorem nndist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (homothety p₁ c p₂) = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_center_homothety _ _ _

@[simp]
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₁ = ‖c‖ * dist p₁ p₂ := by rw [dist_comm, dist_center_homothety]

@[simp]
theorem nndist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_homothety_center _ _ _

@[simp]
theorem dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    dist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂ := by
  rw [dist_comm p₁ p₂]
  simp only [lineMap_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul, norm_smul, vsub_eq_sub]

@[simp]
theorem nndist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    nndist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = nndist c₁ c₂ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_lineMap _ _ _ _

theorem lipschitzWith_lineMap (p₁ p₂ : P) : LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 → P) :=
  LipschitzWith.of_dist_le_mul fun c₁ c₂ =>
    ((dist_lineMap_lineMap p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

@[simp]
theorem dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_zero, dist_zero_right] using dist_lineMap_lineMap p₁ p₂ c 0

@[simp]
theorem nndist_lineMap_left (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_left _ _ _

@[simp]
theorem dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_left _ _ _)

@[simp]
theorem nndist_left_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (lineMap p₁ p₂ c) = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_left_lineMap _ _ _

@[simp]
theorem dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    dist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_one, dist_eq_norm'] using dist_lineMap_lineMap p₁ p₂ c 1

@[simp]
theorem nndist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_right _ _ _

@[simp]
theorem dist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_right _ _ _)

@[simp]
theorem nndist_right_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_right_lineMap _ _ _

@[simp]
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  rw [homothety_eq_lineMap, dist_lineMap_right]

@[simp]
theorem nndist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_homothety_self _ _ _

@[simp]
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₂ (homothety p₁ c p₂) = ‖1 - c‖ * dist p₁ p₂ := by rw [dist_comm, dist_homothety_self]

@[simp]
theorem nndist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (homothety p₁ c p₂) = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_self_homothety _ _ _

section invertibleTwo

variable [Invertible (2 : 𝕜)]

@[simp]
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint, dist_comm, dist_lineMap_left, invOf_eq_inv, ← norm_inv]

@[simp]
theorem nndist_left_midpoint (p₁ p₂ : P) :
    nndist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_left_midpoint _ _

@[simp]
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_left_midpoint]

@[simp]
theorem nndist_midpoint_left (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_midpoint_left _ _

@[simp]
theorem dist_midpoint_right (p₁ p₂ : P) :
    dist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
theorem nndist_midpoint_right (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_midpoint_right _ _

@[simp]
theorem dist_right_midpoint (p₁ p₂ : P) :
    dist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_midpoint_right]

@[simp]
theorem nndist_right_midpoint (p₁ p₂ : P) :
    nndist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_right_midpoint _ _

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
theorem dist_left_midpoint_eq_dist_right_midpoint (p₁ p₂ : P) :
    dist p₁ (midpoint 𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p₂) := by
  rw [dist_left_midpoint p₁ p₂, dist_right_midpoint p₁ p₂]

theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ‖(2 : 𝕜)‖ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add, norm_smul, invOf_eq_inv, norm_inv, ← div_eq_inv_mul]
  grw [norm_add_le]

theorem nndist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    nndist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (nndist p₁ p₃ + nndist p₂ p₄) / ‖(2 : 𝕜)‖₊ :=
  dist_midpoint_midpoint_le' _ _ _ _

end invertibleTwo

@[simp] theorem dist_pointReflection_left (p q : P) :
    dist (Equiv.pointReflection p q) p = dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_left (G := V)]

@[simp] theorem dist_left_pointReflection (p q : P) :
    dist p (Equiv.pointReflection p q) = dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_left _ _)

variable (𝕜) in
theorem dist_pointReflection_right (p q : P) :
    dist (Equiv.pointReflection p q) q = ‖(2 : 𝕜)‖ * dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_right (G := V), ← Nat.cast_smul_eq_nsmul 𝕜,
    norm_smul]

variable (𝕜) in
theorem dist_right_pointReflection (p q : P) :
    dist q (Equiv.pointReflection p q) = ‖(2 : 𝕜)‖ * dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_right 𝕜 _ _)

theorem antilipschitzWith_lineMap {p₁ p₂ : Q} (h : p₁ ≠ p₂) :
    AntilipschitzWith (nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 → Q) :=
  AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_lineMap_lineMap, NNReal.coe_inv, ← dist_nndist, mul_left_comm,
      inv_mul_cancel₀ (dist_ne_zero.2 h), mul_one]

variable (𝕜)

theorem eventually_homothety_mem_of_mem_interior (x : Q) {s : Set Q} {y : Q} (hy : y ∈ interior s) :
    ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s := by
  rw [(NormedAddCommGroup.nhds_basis_norm_lt (1 : 𝕜)).eventually_iff]
  rcases eq_or_ne y x with h | h
  · use 1
    simp [h.symm, interior_subset hy]
  have hxy : 0 < ‖y -ᵥ x‖ := by rwa [norm_pos_iff, vsub_ne_zero]
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hy
  obtain ⟨ε, hε, hyε⟩ := Metric.isOpen_iff.mp hu₂ y hu₃
  refine ⟨ε / ‖y -ᵥ x‖, div_pos hε hxy, fun δ (hδ : ‖δ - 1‖ < ε / ‖y -ᵥ x‖) => hu₁ (hyε ?_)⟩
  rw [lt_div_iff₀ hxy, ← norm_smul, sub_smul, one_smul] at hδ
  rwa [homothety_apply, Metric.mem_ball, dist_eq_norm_vsub W, vadd_vsub_eq_sub_vsub]

theorem eventually_homothety_image_subset_of_finite_subset_interior (x : Q) {s : Set Q} {t : Set Q}
    (ht : t.Finite) (h : t ⊆ interior s) : ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ '' t ⊆ s := by
  suffices ∀ y ∈ t, ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior 𝕜 x (h hy)

end NormedSpace

variable [NormedSpace ℝ V] [NormedSpace ℝ W]

theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 := by
  simpa using dist_midpoint_midpoint_le' (𝕜 := ℝ) p₁ p₂ p₃ p₄

theorem nndist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    nndist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (nndist p₁ p₃ + nndist p₂ p₄) / 2 :=
  dist_midpoint_midpoint_le _ _ _ _

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y))
    (hfc : Continuous f) : P →ᵃ[ℝ] Q :=
  let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
    ((AffineEquiv.vaddConst ℝ (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst ℝ c) (by simp)
    fun x y => by simp [h]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    c fun p => by simp

end

section

open Dilation

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [NormSMulClass 𝕜 E] {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

-- TODO: define `ContinuousAffineEquiv` and reimplement this as one of those.
/-- Scaling by an element `k` of the scalar ring as a `DilationEquiv` with ratio `‖k‖₊`, mapping
from a normed space to a normed torsor over that space sending `0` to `c`. -/
@[simps]
def DilationEquiv.smulTorsor (c : P) {k : 𝕜} (hk : k ≠ 0) : E ≃ᵈ P where
  toFun := (k • · +ᵥ c)
  invFun := k⁻¹ • (· -ᵥ c)
  left_inv x := by simp [inv_smul_smul₀ hk]
  right_inv p := by simp [smul_inv_smul₀ hk]
  edist_eq' := ⟨‖k‖₊, nnnorm_ne_zero_iff.mpr hk, fun x y ↦ by
    rw [show edist (k • x +ᵥ c) (k • y +ᵥ c) = _ from (IsometryEquiv.vaddConst c).isometry ..]
    exact edist_smul₀ ..⟩

-- Cannot be @[simp] because `x` and `y` cannot be inferred by `simp`.
lemma DilationEquiv.smulTorsor_ratio {c : P} {k : 𝕜} (hk : k ≠ 0) {x y : E}
    (h : dist x y ≠ 0) : ratio (smulTorsor c hk) = ‖k‖₊ :=
  Eq.symm <| ratio_unique_of_dist_ne_zero h <| by simp [dist_eq_norm, ← smul_sub, norm_smul]

@[simp]
lemma DilationEquiv.smulTorsor_preimage_ball {c : P} {k : 𝕜} (hk : k ≠ 0) :
    smulTorsor c hk ⁻¹' (Metric.ball c ‖k‖) = Metric.ball (0 : E) 1 := by
  aesop (add simp norm_smul)

end
