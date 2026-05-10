/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Linear maps on inner product spaces

This file studies linear maps on inner product spaces.

## Main results

- We define `innerSL` as the inner product bundled as a continuous sesquilinear map
- We prove a general polarization identity for linear maps (`inner_map_polarization`)
- We show that a linear map preserving the inner product is an isometry
  (`LinearMap.isometryOfInner`) and conversely an isometry preserves the inner product
  (`LinearIsometry.inner_map_map`).

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section

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
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
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
    simp
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

/-- The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp. `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply_apply]

@[simp]
theorem coe_innerSL_apply (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

theorem innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
  rfl

@[simp] theorem ContinuousLinearMap.toLinearMap_innerSL_apply (v : E) :
    (innerSL 𝕜 v).toLinearMap = innerₛₗ 𝕜 v := rfl

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]
theorem innerSLFlip_apply_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫ :=
  rfl

variable (F) in
@[simp] lemma flip_innerSL_real : (innerSL ℝ (E := F)).flip = innerSL ℝ (E := F) := by
  ext v w
  exact real_inner_comm _ _

@[deprecated (since := "2025-11-15")] alias innerₛₗ_apply_coe := coe_innerₛₗ_apply
@[deprecated (since := "2025-11-15")] alias innerₛₗ_apply := innerₛₗ_apply_apply
@[deprecated (since := "2025-11-15")] alias innerₗ_apply := innerₗ_apply_apply
@[deprecated (since := "2025-11-15")] alias innerSL_apply_coe := coe_innerSL_apply
@[deprecated (since := "2025-11-15")] alias innerSL_apply := innerSL_apply_apply
@[deprecated (since := "2025-11-15")] alias innerSLFlip_apply := innerSLFlip_apply_apply
@[deprecated (since := "2025-11-15")] alias innerSL_real_flip := flip_innerSL_real

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
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := by gcongr
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
  · refine (mul_le_mul_iff_left₀ h).mp ?_
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
  simp only [map_smul, ContinuousLinearMap.reApplyInnerSelf_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

end ReApplyInnerSelf_Seminormed

namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open ContinuousLinearMap

variable (𝕜) in
/-- A rank-one operator on an inner product space is given by `x ↦ y ↦ z ↦ ⟪y, z⟫ • x`.

This is also sometimes referred to as an outer product of vectors on a Hilbert space.
This corresponds to the matrix outer product `Matrix.vecMulVec`, see
`InnerProductSpace.toMatrix_rankOne` and `InnerProductSpace.symm_toEuclideanLin_rankOne` in
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`. -/
noncomputable def rankOne : E →L[𝕜] F →L⋆[𝕜] F →L[𝕜] E :=
  .flip <| .comp (.smulRightL 𝕜 _ _) (innerSL 𝕜)

lemma rankOne_def (x : E) (y : F) : rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x := rfl

lemma rankOne_def' (x : E) (y : F) : rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y := rfl

lemma toLinearMap_rankOne (x : E) (y : F) :
    (rankOne 𝕜 x y).toLinearMap = (innerₛₗ 𝕜 y).smulRight x := rfl

@[simp] theorem norm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ = ‖x‖ * ‖y‖ := by
  rw [rankOne_def, norm_smulRight_apply, innerSL_apply_norm, mul_comm]

@[simp] theorem nnnorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖₊ = ‖x‖₊ * ‖y‖₊ :=
  NNReal.eq <| norm_rankOne _ _

@[simp] theorem enorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ₑ = ‖x‖ₑ * ‖y‖ₑ :=
  ENNReal.coe_inj.mpr <| nnnorm_rankOne _ _

@[simp] lemma rankOne_apply (x : E) (y z : F) : rankOne 𝕜 x y z = inner 𝕜 y z • x := rfl

lemma comp_rankOne {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (x : E) (y : F) (f : E →L[𝕜] G) : f ∘L rankOne 𝕜 x y = rankOne 𝕜 (f x) y := by
  simp_rw [rankOne_def', ← comp_assoc, comp_toSpanSingleton]

theorem isIdempotentElem_rankOne_self {x : F} (hx : ‖x‖ = 1) :
    IsIdempotentElem (rankOne 𝕜 x x) := by simp [IsIdempotentElem, mul_def, comp_rankOne, hx]

@[simp] theorem rankOne_one_right_eq_toSpanSingleton (x : F) :
    rankOne 𝕜 x 1 = toSpanSingleton 𝕜 x := by ext; simp

@[simp] theorem rankOne_one_left_eq_innerSL (x : F) : rankOne 𝕜 1 x = innerSL 𝕜 x := by ext; simp

lemma rankOne_comp_rankOne (x : E) (y z : F) (w : G) :
    rankOne 𝕜 x y ∘L rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by simp [comp_rankOne]

lemma inner_left_rankOne_apply (x : F) (y z : G) (w : F) :
    inner 𝕜 (rankOne 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [inner_smul_left, inner_conj_symm]

lemma inner_right_rankOne_apply (x y : F) (z w : G) :
    inner 𝕜 x (rankOne 𝕜 y z w) = inner 𝕜 x y * inner 𝕜 z w := by
  simp [inner_smul_right, mul_comm]

section Normed
variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp] theorem rankOne_eq_zero {x : E} {y : F} : rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp [ContinuousLinearMap.ext_iff, rankOne_apply, forall_or_right, or_comm,
    ext_iff_inner_right 𝕜 (E := F)]

lemma rankOne_ne_zero {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) : rankOne 𝕜 x y ≠ 0 := by
  grind [rankOne_eq_zero]

theorem isIdempotentElem_rankOne_self_iff {x : F} (hx : x ≠ 0) :
    IsIdempotentElem (rankOne 𝕜 x x) ↔ ‖x‖ = 1 := by
  refine ⟨?_, isIdempotentElem_rankOne_self⟩
  simp only [IsIdempotentElem, mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K,
    map_smul, coe_smul', Pi.smul_apply]
  nth_rw 2 [← one_smul 𝕜 (rankOne 𝕜 x x)]
  rw [← sub_eq_zero, ← sub_smul]
  simp only [smul_eq_zero, rankOne_eq_zero, hx, or_self, or_false, sub_eq_zero, sq_eq_one_iff,
    FaithfulSMul.algebraMap_eq_one_iff, ← show ((-(1 : ℝ) : ℝ) : 𝕜) = -1 by grind, ofReal_inj]
  grind [norm_nonneg]

theorem rankOne_eq_rankOne_iff_comm {a c : F} {b d : H} :
    rankOne 𝕜 a b = rankOne 𝕜 c d ↔ rankOne 𝕜 b a = rankOne 𝕜 d c := by
  simp_rw [ContinuousLinearMap.ext_iff, ext_iff_inner_left 𝕜 (E := F),
    ext_iff_inner_right 𝕜 (E := H)]
  rw [forall_comm]
  simp [inner_smul_left, inner_smul_right, mul_comm]

open ComplexOrder in
theorem exists_of_rankOne_eq_rankOne {a c : F} {b d : H}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : rankOne 𝕜 a b = rankOne 𝕜 c d) :
    ∃ (α β : 𝕜) (_ : α ≠ 0) (_ : 0 < β), a = α • c ∧ b = (α * β) • d := by
  have h₂ := rankOne_eq_rankOne_iff_comm.mp h
  simp only [ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  have h₃ := calc
    a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by simp_all
    _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
    _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [h, smul_smul]; ring_nf
  have h₄ := calc
    b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by simp_all
    _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
    _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)) • d := by
      simp_rw [h₂, h₃, inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 ≠ 0 := fun h ↦ by simp [h, hb] at h₄
  have h₆ : c ≠ 0 := fun h ↦ by simp [h, ha] at h₃
  refine ⟨_, ‖c‖ ^ 2 / ‖a‖ ^ 2, div_ne_zero h₅ <| by simpa, ?_, h₃, by simpa using h₄⟩
  simp_rw [← ofReal_pow, ← ofReal_div, pos_iff (K := 𝕜), ofReal_re, ofReal_im, and_true]
  exact div_pos (by simpa [sq_pos_iff]) (by simpa [sq_pos_iff])

end Normed

end InnerProductSpace

namespace ContinuousLinearMap

open InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem opNorm_le_of_re_inner_le {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → re ⟪T x, y⟫_𝕜 ≤ C) : ‖T‖ ≤ C := by
  refine opNorm_le_of_unit_norm hC fun x hx ↦ ?_
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  · specialize h x (((‖T x‖⁻¹ : ℝ) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
    rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
      inv_mul_eq_div, sq, mul_self_div_self] at h

end ContinuousLinearMap
