/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

! This file was ported from Lean 3 source module analysis.normed_space.continuous_linear_map
! leanprover-community/mathlib commit e0e2f10d64d8a5fd11140de398eaa1322eb46c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.Basic

/-! # Constructions of continuous linear maps between (semi-)normed spaces

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`LinearMap` `f : E →ₛₗ[σ] F` is the coercion of some `ContinuousLinearMap` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `LinearMap.mkContinuous`, boundedness implies continuity. The
other direction, `ContinuousLinearMap.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`ContinuousLinearMap.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `LinearMap.mkContinuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

set_option synthInstance.etaExperiment true -- Porting note: gets around lean4#2074
open Metric ContinuousLinearMap

open Set Real

open NNReal

variable {𝕜 𝕜₂ E F G : Type _}

variable [NormedField 𝕜] [NormedField 𝕜₂]

/-! # General constructions -/


section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 G]

variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`LinearMap.mkContinuous_norm_le`. -/
def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩
#align linear_map.mk_continuous LinearMap.mkContinuous

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `LinearMap.toContinuousLinearMap`. -/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x =>
    le_of_eq <| by
      conv_lhs => rw [← mul_one x]
      rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm]
#align linear_map.to_continuous_linear_map₁ LinearMap.toContinuousLinearMap₁

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `LinearMap.mkContinuous` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous_norm_le`. -/
def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩
#align linear_map.mk_continuous_of_exists_bound LinearMap.mkContinuousOfExistsBound

theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
#align continuous_of_linear_of_boundₛₗ continuous_of_linear_of_boundₛₗ

theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₗ[𝕜] G :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
#align continuous_of_linear_of_bound continuous_of_linear_of_bound

@[simp, norm_cast]
theorem LinearMap.mkContinuous_coe (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuous C h : E →ₛₗ[σ] F) = f :=
  rfl
#align linear_map.mk_continuous_coe LinearMap.mkContinuous_coe

@[simp]
theorem LinearMap.mkContinuous_apply (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuous C h x = f x :=
  rfl
#align linear_map.mk_continuous_apply LinearMap.mkContinuous_apply

@[simp, norm_cast]
theorem LinearMap.mkContinuousOfExistsBound_coe (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuousOfExistsBound h : E →ₛₗ[σ] F) = f :=
  rfl
#align linear_map.mk_continuous_of_exists_bound_coe LinearMap.mkContinuousOfExistsBound_coe

@[simp]
theorem LinearMap.mkContinuousOfExistsBound_apply (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuousOfExistsBound h x = f x :=
  rfl
#align linear_map.mk_continuous_of_exists_bound_apply LinearMap.mkContinuousOfExistsBound_apply

@[simp]
theorem LinearMap.toContinuousLinearMap₁_coe (f : 𝕜 →ₗ[𝕜] E) :
    (f.toContinuousLinearMap₁ : 𝕜 →ₗ[𝕜] E) = f :=
  rfl
#align linear_map.to_continuous_linear_map₁_coe LinearMap.toContinuousLinearMap₁_coe

@[simp]
theorem LinearMap.toContinuousLinearMap₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
    f.toContinuousLinearMap₁ x = f x :=
  rfl
#align linear_map.to_continuous_linear_map₁_apply LinearMap.toContinuousLinearMap₁_apply

namespace ContinuousLinearMap

theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound _ h
#align continuous_linear_map.antilipschitz_of_bound ContinuousLinearMap.antilipschitz_of_bound

theorem bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : AntilipschitzWith K f) (x) :
    ‖x‖ ≤ K * ‖f x‖ :=
  AddMonoidHomClass.bound_of_antilipschitz _ h x
#align continuous_linear_map.bound_of_antilipschitz ContinuousLinearMap.bound_of_antilipschitz

end ContinuousLinearMap

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
    (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv
#align linear_equiv.to_continuous_linear_equiv_of_bounds LinearEquiv.toContinuousLinearEquivOfBounds

end

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]

variable {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

theorem ContinuousLinearMap.uniformEmbedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    UniformEmbedding f :=
  (AddMonoidHomClass.antilipschitz_of_bound f hf).uniformEmbedding f.uniformContinuous
#align continuous_linear_map.uniform_embedding_of_bound ContinuousLinearMap.uniformEmbedding_of_bound

end Normed

/-! ## Homotheties -/


section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]

variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- A (semi-)linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def ContinuousLinearMap.ofHomothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀ x, ‖f x‖ = a * ‖x‖) :
    E →SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)
#align continuous_linear_map.of_homothety ContinuousLinearMap.ofHomothety

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

theorem ContinuousLinearEquiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
    (∀ x : E, ‖f x‖ = a * ‖x‖) → ∀ y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖ := by
  intro hf y
  calc
    ‖f.symm y‖ = a⁻¹ * (a * ‖f.symm y‖) := by
      rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul]
    _ = a⁻¹ * ‖f (f.symm y)‖ := by rw [hf]
    _ = a⁻¹ * ‖y‖ := by simp
#align continuous_linear_equiv.homothety_inverse ContinuousLinearEquiv.homothety_inverse

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
noncomputable def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le
#align continuous_linear_equiv.of_homothety ContinuousLinearEquiv.ofHomothety

end Seminormed

/-! ## The span of a single vector -/


section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

variable (𝕜)

theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by
  rw [mul_comm]
  exact norm_smul _ _
#align continuous_linear_map.to_span_singleton_homothety ContinuousLinearMap.toSpanSingleton_homothety

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `𝕜` to `E` by taking multiples of `x`.-/
def toSpanSingleton (x : E) : 𝕜 →L[𝕜] E :=
  ofHomothety (LinearMap.toSpanSingleton 𝕜 E x) ‖x‖ (toSpanSingleton_homothety 𝕜 x)
#align continuous_linear_map.to_span_singleton ContinuousLinearMap.toSpanSingleton

theorem toSpanSingleton_apply (x : E) (r : 𝕜) : toSpanSingleton 𝕜 x r = r • x := by
  simp [toSpanSingleton, ofHomothety, LinearMap.toSpanSingleton]
#align continuous_linear_map.to_span_singleton_apply ContinuousLinearMap.toSpanSingleton_apply

theorem toSpanSingleton_add (x y : E) :
    toSpanSingleton 𝕜 (x + y) = toSpanSingleton 𝕜 x + toSpanSingleton 𝕜 y := by
  ext1
  simp [toSpanSingleton_apply]
#align continuous_linear_map.to_span_singleton_add ContinuousLinearMap.toSpanSingleton_add

theorem toSpanSingleton_smul' (𝕜') [NormedField 𝕜'] [NormedSpace 𝕜' E] [SMulCommClass 𝕜 𝕜' E]
    (c : 𝕜') (x : E) : toSpanSingleton 𝕜 (c • x) = c • toSpanSingleton 𝕜 x := by
  ext1
  rw [toSpanSingleton_apply, smul_apply, toSpanSingleton_apply, smul_comm]
#align continuous_linear_map.to_span_singleton_smul' ContinuousLinearMap.toSpanSingleton_smul'

theorem toSpanSingleton_smul (c : 𝕜) (x : E) :
    toSpanSingleton 𝕜 (c • x) = c • toSpanSingleton 𝕜 x :=
  toSpanSingleton_smul' 𝕜 𝕜 c x
#align continuous_linear_map.to_span_singleton_smul ContinuousLinearMap.toSpanSingleton_smul

end ContinuousLinearMap

section

namespace ContinuousLinearEquiv

variable (𝕜)

theorem toSpanNonzeroSingleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
    ‖LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
  ContinuousLinearMap.toSpanSingleton_homothety _ _ _
#align continuous_linear_equiv.to_span_nonzero_singleton_homothety ContinuousLinearEquiv.toSpanNonzeroSingleton_homothety

end ContinuousLinearEquiv

end

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearEquiv

variable (𝕜)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
noncomputable def toSpanNonzeroSingleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (toSpanNonzeroSingleton_homothety 𝕜 x h)
#align continuous_linear_equiv.to_span_nonzero_singleton ContinuousLinearEquiv.toSpanNonzeroSingleton

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
noncomputable def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 :=
  (toSpanNonzeroSingleton 𝕜 x h).symm
#align continuous_linear_equiv.coord ContinuousLinearEquiv.coord

@[simp]
theorem coe_toSpanNonzeroSingleton_symm {x : E} (h : x ≠ 0) :
    ⇑(toSpanNonzeroSingleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl
#align continuous_linear_equiv.coe_to_span_nonzero_singleton_symm ContinuousLinearEquiv.coe_toSpanNonzeroSingleton_symm

@[simp]
theorem coord_toSpanNonzeroSingleton {x : E} (h : x ≠ 0) (c : 𝕜) :
    coord 𝕜 x h (toSpanNonzeroSingleton 𝕜 x h c) = c :=
  (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c
#align continuous_linear_equiv.coord_to_span_nonzero_singleton ContinuousLinearEquiv.coord_toSpanNonzeroSingleton

@[simp]
theorem toSpanNonzeroSingleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
    toSpanNonzeroSingleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y
#align continuous_linear_equiv.to_span_nonzero_singleton_coord ContinuousLinearEquiv.toSpanNonzeroSingleton_coord

@[simp]
theorem coord_self (x : E) (h : x ≠ 0) :
    (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h
#align continuous_linear_equiv.coord_self ContinuousLinearEquiv.coord_self

end ContinuousLinearEquiv

end Normed
