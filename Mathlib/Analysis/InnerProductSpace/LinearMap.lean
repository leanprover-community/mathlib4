/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/

import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Linear maps on inner product spaces

This file studies linear maps on inner product spaces.

## Main results

- We define `innerSL` as the inner product bundled as a continuous sesquilinear map, and
  `innerₛₗ` for the non-continuous version.
- We prove a general polarization identity for linear maps (`inner_map_polarization`)
- We show that a linear map preserving the inner product is an isometry
  (`LinearMap.isometryOfInner`) and conversely an isometry preserves the inner product
  (`LinearIsometry.inner_map_map`).

## Tags

inner product space, Hilbert space, norm

-/

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Complex_Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A complex polarization identity, with a linear map. -/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

end Complex_Seminormed

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for all `x`.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply, ← @inner_self_eq_zero ℂ V, inner_map_polarization]
    simp only [hT]
    norm_num
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

/--
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ` holds
for all `x`.
-/
theorem ext_inner_map (S T : V →ₗ[ℂ] V) : (∀ x : V, ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) ↔ S = T := by
  rw [← sub_eq_zero, ← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply, inner_sub_left, sub_eq_zero]

end Complex

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y

/-- The adjoint of a linear isometric equivalence is its inverse. -/
theorem LinearIsometryEquiv.inner_map_eq_flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') :
    ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜 := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_re_inner 𝕜, h]⟩

@[simp]
theorem LinearMap.coe_isometryOfInner (f : E →ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearMap.isometryOfInner_toLinearMap (f : E →ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl

/-- A linear map is an isometry if and it preserves the inner product. -/
theorem LinearMap.norm_map_iff_inner_map_map {F : Type*} [FunLike F E E'] [LinearMapClass F 𝕜 E E']
    (f : F) : (∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜) :=
  ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E →ₗᵢ[𝕜] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

end

variable (𝕜)

/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]
theorem innerₛₗ_apply_coe (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/-- The inner product as a bilinear map in the real case. -/
def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ

@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w

variable {F}

@[simp] lemma innerₗ_apply (v w : F) : innerₗ F v w = ⟪v, w⟫_ℝ := rfl

/-- The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp. `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply]

@[simp]
theorem innerSL_apply_coe (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerSL_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
  rfl

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]
theorem innerSLFlip_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫ :=
  rfl

variable (F) in
@[simp] lemma innerSL_real_flip : (innerSL ℝ (E := F)).flip = innerSL ℝ (E := F) := by
  ext v w
  exact real_inner_comm _ _

variable {𝕜}

namespace ContinuousLinearMap

variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

-- Note: odd and expensive build behavior is explicitly turned off using `noncomputable`
/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `fun x y ↦ ⟪x, A y⟫`, given
as a continuous linear map. -/
noncomputable def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)

@[simp]
theorem toSesqForm_apply_coe (f : E →L[𝕜] E') (x : E') : toSesqForm f x = (innerSL 𝕜 x).comp f :=
  rfl

theorem toSesqForm_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ ≤ ‖f‖ * ‖v‖ := by
  refine opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖ := h₂
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring

end ContinuousLinearMap

variable (𝕜)

/-- `innerSL` is an isometry. Note that the associated `LinearIsometry` is defined in
`InnerProductSpace.Dual` as `toDualMap`. -/
@[simp]
theorem innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖ := by
  refine
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
  rcases (norm_nonneg x).eq_or_lt' with (h | h)
  · simp [h]
  · refine (mul_le_mul_right h).mp ?_
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq, inner_self_eq_norm_sq_to_K, norm_pow, norm_ofReal, abs_norm]
      _ ≤ ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _

lemma norm_innerSL_le : ‖innerSL 𝕜 (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

end Norm_Seminormed

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}

/-- The inner product on an inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem inner_map_complex [SeminormedAddCommGroup G] [InnerProductSpace ℝ G] (f : G ≃ₗᵢ[ℝ] ℂ)
    (x y : G) : ⟪x, y⟫_ℝ = (f y * conj (f x)).re := by rw [← Complex.inner, f.inner_map_map]

end RCLikeToReal

section ReApplyInnerSelf

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Extract a real bilinear form from an operator `T`,
by taking the pairing `fun x ↦ re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫

theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E →L[𝕜] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl

end ReApplyInnerSelf

section ReApplyInnerSelf_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[𝕜] E) :
    Continuous T.reApplyInnerSelf :=
  reCLM.continuous.comp <| T.continuous.inner continuous_id

theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_smul_left, inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

end ReApplyInnerSelf_Seminormed
