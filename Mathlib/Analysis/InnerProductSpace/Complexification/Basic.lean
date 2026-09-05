/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Complexification of inner product spaces

In this file we define the complexification of an inner product space. So we can essentially
extend a `𝕜`-space `E` to a `ℂ`-space `E × E`, and extend operators to its complexification
in order to use `ℂ`-results. We call the first component the "real part" (`Complexification.re`)
and the second the "imaginary part" (`Complexification.im`).
This way, we can (informally) think of `(x, y) : Complexification 𝕜 E` as `x + I • y`.

In particular, `ℂ`-scalar multiplication is given by
`α • (x, y) = (ℜ α • x - ℑ α • y, ℜ α • y + ℑ α • x)`
and the `ℂ`-inner product is given by
`⟪(x, y), (z, w)⟫_ℂ = ℜ (⟪x, z⟫_𝕜 + ⟪y, w⟫_𝕜) + (ℜ (⟪x, w⟫_𝕜 - ⟪y, z⟫_𝕜)) * I`.

## Main definitions and results

* `Complexification.instSMul`: Complex scalar multiplication on complexifications.
* `Complexification.instInnerProductSpace`: The complex inner product space on complexifications.
* `Submodule.complexification`: The complexification of a submodule.
* `Complexification.conj`: Conjugation on complexification, i.e., `(x, y) ↦ (x, -y)`.
* `Complexification.realLinearIsometryEquivComplex`: The complexification of
  `ℝ` is equivalent to `ℂ`.
* `ContinuousLinearMap.toComplexification`: The complexification of an operator `T`, which is
  defined as `x ↦ (T x.re, T x.im)`.
* `ContinuousLinearMap.ofComplexification`: Decomplexifying an operator on complexifications given
  that it commutes with the complexification of `algebraMapCLM 𝕜 _ RCLike.I`,
  and is defined as `x ↦ (T (x, 0)).re`.

## References

[Steven Roman, *Advanced linear algebra*][roman_advanced_linear_algebra]

-/

public section

open scoped InnerProductSpace

set_option linter.unusedVariables false in
/-- The complexification of an inner product space.
This is a type synonym of `WithLp 2 (E × E)`, with the same norm. -/
@[expose, nolint unusedArguments, implicit_reducible] def Complexification (𝕜 E : Type*) :
    Type _ := WithLp 2 (E × E)

variable {𝕜 E F G : Type*} {Eₗ Fₗ Gₗ : Type*}
  [NormedAddCommGroup Eₗ] [NormedAddCommGroup Fₗ] [NormedAddCommGroup Gₗ]
  [InnerProductSpace ℝ Eₗ] [InnerProductSpace ℝ Fₗ] [InnerProductSpace ℝ Gₗ]

noncomputable instance [NormedAddCommGroup E] : NormedAddCommGroup (Complexification 𝕜 E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [NormedAddCommGroup E] [CompleteSpace E] : CompleteSpace (Complexification 𝕜 E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

namespace Complexification

/-- The real part of the complexification (the first component of the complexification). -/
protected def re (v : Complexification 𝕜 E) : E := WithLp.fst v

/-- The imaginary part of the complexification (the second component of the complexification). -/
protected def im (v : Complexification 𝕜 E) : E := WithLp.snd v

/-- Converting real and imaginary parts to the complexification. -/
def mk (𝕜 : Type*) (x y : E) : Complexification 𝕜 E := WithLp.toLp 2 (x, y)

@[simp] lemma re_mk (x y : E) : (mk 𝕜 x y).re = x := by rfl
@[simp] lemma im_mk (x y : E) : (mk 𝕜 x y).im = y := by rfl
@[simp] lemma mk_re_im (v : Complexification 𝕜 E) : mk 𝕜 v.re v.im = v := by rfl

@[ext] lemma ext {v w : Complexification 𝕜 E} (h₁ : v.re = w.re) (h₂ : v.im = w.im) : v = w := by
  rw [← mk_re_im v, ← mk_re_im w, h₁, h₂]

variable [NormedAddCommGroup E]

@[simp] lemma re_zero : (0 : Complexification 𝕜 E).re = 0 := by rfl
@[simp] lemma im_zero : (0 : Complexification 𝕜 E).im = 0 := by rfl
@[simp] lemma re_add (v w : Complexification 𝕜 E) : (v + w).re = v.re + w.re := by rfl
@[simp] lemma im_add (v w : Complexification 𝕜 E) : (v + w).im = v.im + w.im := by rfl
@[simp] lemma re_sub (v w : Complexification 𝕜 E) : (v - w).re = v.re - w.re := by rfl
@[simp] lemma im_sub (v w : Complexification 𝕜 E) : (v - w).im = v.im - w.im := by rfl
@[simp] lemma re_neg (v : Complexification 𝕜 E) : (-v).re = -v.re := by rfl
@[simp] lemma im_neg (v : Complexification 𝕜 E) : (-v).im = -v.im := by rfl
@[simp] lemma mk_zero_zero : mk 𝕜 (0 : E) 0 = 0 := by rfl
@[simp] lemma neg_mk (x y : E) : -mk 𝕜 x y = mk 𝕜 (-x) (-y) := by ext <;> simp

@[simp] lemma mk_add_mk (x y z w : E) : mk 𝕜 x y + mk 𝕜 z w = mk 𝕜 (x + z) (y + w) := by
  ext <;> simp
@[simp] lemma mk_sub_mk (x y z w : E) : mk 𝕜 x y - mk 𝕜 z w = mk 𝕜 (x - z) (y - w) := by
  simp [sub_eq_add_neg]

lemma norm_sq_eq (v : Complexification 𝕜 E) : ‖v‖ ^ 2 = ‖v.re‖ ^ 2 + ‖v.im‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 v
lemma norm_eq (v : Complexification 𝕜 E) : ‖v‖ = √(‖v.re‖ ^ 2 + ‖v.im‖ ^ 2) :=
  WithLp.prod_norm_eq_of_L2 v

@[simp] lemma norm_mk_zero_right (x : E) : ‖mk 𝕜 x 0‖ = ‖x‖ := by simp [norm_eq]
@[simp] lemma norm_mk_zero_left (x : E) : ‖mk 𝕜 0 x‖ = ‖x‖ := by simp [norm_eq]

lemma norm_re_le (x : Complexification 𝕜 E) : ‖x.re‖ ≤ ‖x‖ := by
  rw [norm_eq, Real.le_sqrt (norm_nonneg _) (by positivity)]
  simp

lemma norm_im_le (x : Complexification 𝕜 E) : ‖x.im‖ ≤ ‖x‖ := by
  rw [norm_eq, Real.le_sqrt (norm_nonneg _) (by positivity)]
  simp

lemma lipschitzWith_re : LipschitzWith 1 (Complexification.re (𝕜 := 𝕜) (E := E)) :=
  .of_dist_le_mul fun v w ↦ by simpa [dist_eq_norm] using norm_re_le (v - w)
lemma lipschitzWith_im : LipschitzWith 1 (Complexification.im (𝕜 := 𝕜) (E := E)) :=
  .of_dist_le_mul fun v w ↦ by simpa [dist_eq_norm] using norm_im_le (v - w)

@[fun_prop] lemma continuous_re : Continuous (Complexification.re (𝕜 := 𝕜) (E := E)) :=
  lipschitzWith_re.continuous
@[fun_prop] lemma continuous_im : Continuous (Complexification.im (𝕜 := 𝕜) (E := E)) :=
  lipschitzWith_im.continuous

lemma isometry_mk_zero_right : Isometry (mk 𝕜 · (0 : E)) :=
  .of_dist_eq fun x y ↦ by simp [dist_eq_norm]
lemma isometry_mk_zero_left : Isometry (mk 𝕜 (0 : E) ·) :=
  .of_dist_eq fun x y ↦ by simp [dist_eq_norm]

@[fun_prop] lemma continuous_mk_zero_right : Continuous (mk 𝕜 · (0 : E)) :=
  isometry_mk_zero_right.continuous
@[fun_prop] lemma continuous_mk_zero_left : Continuous (mk 𝕜 (0 : E) ·) :=
  isometry_mk_zero_left.continuous
@[fun_prop] lemma continuous_mk : Continuous fun p : E × E ↦ mk 𝕜 p.1 p.2 := by
  suffices Continuous fun (p : E × E) ↦ mk 𝕜 p.1 0 + mk 𝕜 0 p.2 by simpa
  fun_prop

variable [RCLike 𝕜] [InnerProductSpace 𝕜 E]

instance instSMul : SMul ℂ (Complexification 𝕜 E) where
  smul z v := .mk 𝕜 ((z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im) ((z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im)

lemma smul_def (z : ℂ) (v : Complexification 𝕜 E) :
    z • v = .mk 𝕜 ((z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im) ((z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im) :=
  rfl

@[simp] lemma re_smul (z : ℂ) (v : Complexification 𝕜 E) :
    (z • v).re = (z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im := by rfl
@[simp] lemma im_smul (z : ℂ) (v : Complexification 𝕜 E) :
    (z • v).im = (z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im := by rfl

instance : Module ℂ (Complexification 𝕜 E) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp <;> module
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp <;> grind
  add_smul _ _ _ := by ext <;> simp <;> module
  zero_smul _ := by ext <;> simp

@[simp] lemma re_real_smul (r : ℝ) (v : Complexification 𝕜 E) : (r • v).re = (r : 𝕜) • v.re := by
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ) r, -Complex.coe_smul]

@[simp] lemma im_real_smul (r : ℝ) (v : Complexification 𝕜 E) : (r • v).im = (r : 𝕜) • v.im := by
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ) r, -Complex.coe_smul]

@[simp] lemma I_smul (v : Complexification 𝕜 E) : Complex.I • v = mk 𝕜 (-v.im) v.re := by
  ext <;> simp

lemma I_smul_mk (x y : E) : Complex.I • (mk 𝕜 x y) = mk 𝕜 (-y) x := I_smul _

/-- `(x, y) = (x, 0) + I • (y, 0)`. -/
lemma mk_eq_add_I_smul (x y : E) : mk 𝕜 x y = mk 𝕜 x 0 + Complex.I • mk 𝕜 y 0 := by simp

lemma norm_smul_eq (z : ℂ) (v : Complexification 𝕜 E) : ‖z • v‖ = ‖z‖ * ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
  simp [mul_pow, norm_sq_eq, Complex.sq_norm, Complex.normSq_apply,
    -inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_re_symm v.im v.re]
  grind

instance : NormedSpace ℂ (Complexification 𝕜 E) where norm_smul_le z v := (norm_smul_eq z v).le

variable (𝕜 E) in
/-- The real part of a complexification of a real space as a real continuous linear map. -/
@[expose, simps] def reL [Module ℝ E] [IsScalarTower ℝ 𝕜 E] : Complexification 𝕜 E →L[ℝ] E where
  toFun x := x.re
  map_add' := by simp
  map_smul' := by simp

variable (𝕜 E) in
/-- The imaginary part of a complexification of a real space as a real continuous linear map. -/
@[expose, simps] def imL [Module ℝ E] [IsScalarTower ℝ 𝕜 E] : Complexification 𝕜 E →L[ℝ] E where
  toFun x := x.im
  map_add' := by simp
  map_smul' := by simp

instance instInner : Inner ℂ (Complexification 𝕜 E) where
  inner v w := .mk (RCLike.re (⟪v.re, w.re⟫_𝕜 + ⟪v.im, w.im⟫_𝕜))
    (RCLike.re (⟪v.re, w.im⟫_𝕜 - ⟪v.im, w.re⟫_𝕜))

lemma inner_def (v w : Complexification 𝕜 E) :
    inner ℂ v w = RCLike.re (⟪v.re, w.re⟫_𝕜 + ⟪v.im, w.im⟫_𝕜) +
      RCLike.re (⟪v.re, w.im⟫_𝕜 - ⟪v.im, w.re⟫_𝕜) * .I := by simp [inner, Complex.mk_eq_add_mul_I]

@[simp] lemma re_inner (v w : Complexification 𝕜 E) :
    (⟪v, w⟫_ℂ).re = RCLike.re (⟪v.re, w.re⟫_𝕜 + ⟪v.im, w.im⟫_𝕜) := rfl
@[simp] lemma im_inner (v w : Complexification 𝕜 E) :
    (⟪v, w⟫_ℂ).im = RCLike.re (⟪v.re, w.im⟫_𝕜 - ⟪v.im, w.re⟫_𝕜) := rfl

instance instInnerProductSpace : InnerProductSpace ℂ (Complexification 𝕜 E) where
  norm_sq_eq_re_inner v := by simp [norm_sq_eq, RCLike.re_to_complex]
  conj_inner_symm _ _ := by simp [Complex.ext_iff, inner_re_symm]
  add_left _ _ _ := by simp [Complex.ext_iff, inner_add_left]; grind
  smul_left _ _ _ := by
    simp [Complex.ext_iff, inner_sub_left, inner_add_left, inner_smul_left]; grind

variable (𝕜 E) in
/-- Conjugation on the complexification space, given by `(x, y) ↦ (x, -y)`. -/
@[expose, simps -isSimp apply] def conj : Complexification 𝕜 E ≃ₗᵢ⋆[ℂ] Complexification 𝕜 E where
  toFun v := .mk 𝕜 v.re (-v.im)
  invFun v := .mk 𝕜 v.re (-v.im)
  map_add' := by simp [add_comm]
  map_smul' _ _ := by ext <;> simp [RCLike.algebraMap_eq_ofReal, add_comm]
  norm_map' := by simp [norm_eq]
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma symm_conj : (conj 𝕜 E).symm = conj 𝕜 E := rfl
@[simp] lemma conj_conj (x) : conj 𝕜 E (conj 𝕜 E x) = x := by simp [conj_apply]
@[simp] lemma conj_mk (x y : E) : conj 𝕜 E (.mk 𝕜 x y) = .mk 𝕜 x (-y) := by rfl

lemma conj_I_smul (x) : conj 𝕜 E (Complex.I • x) = -Complex.I • conj 𝕜 E x := by
  simp [conj_apply]

@[simp] lemma inner_conj_conj (x y) : inner ℂ (conj 𝕜 E x) (conj 𝕜 E y) = inner ℂ y x := by
  simp [Complex.ext_iff, inner_re_symm, sub_eq_add_neg, add_comm, conj_apply]

lemma inner_conj_left (x y) : inner ℂ (conj 𝕜 E x) y = inner ℂ (conj 𝕜 E y) x := by
  simp [Complex.ext_iff, inner_re_symm, sub_eq_add_neg, add_comm, conj_apply]

lemma inner_conj_right (x y) : inner ℂ x (conj 𝕜 E y) = inner ℂ y (conj 𝕜 E x) := by
  rw [← inner_conj_symm, inner_conj_left]; simp

@[simp] lemma conj_eq_self_iff {x} : conj 𝕜 E x = x ↔ x.im = 0 := by
  simp only [conj_apply, Complexification.ext_iff, re_mk, im_mk, true_and]
  rw [eq_comm, ← sub_eq_zero]
  simp [← two_smul 𝕜]

/-- The complexification of `ℝ` is equivalent to `ℂ`. -/
def realLinearIsometryEquivComplex : Complexification ℝ ℝ ≃ₗᵢ[ℂ] ℂ where
  toFun x := x.re + x.im * Complex.I
  invFun x := .mk ℝ x.re x.im
  map_add' _ _ := by simp [add_mul]; grind
  map_smul' z _ := by
    rw [← Complex.re_add_im z]
    simp [add_mul, mul_add, -Complex.re_add_im, mul_mul_mul_comm _ Complex.I]
    grind
  norm_map' := by simp [norm_eq, Complex.norm_def, Complex.normSq, sq]
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma realLinearIsometryEquivComplex_apply (v : Complexification ℝ ℝ) :
    realLinearIsometryEquivComplex v = v.re + v.im * Complex.I := by
  rfl

@[simp] lemma realLinearIsometryEquivComplex_symm_apply (z : ℂ) :
    realLinearIsometryEquivComplex.symm z = .mk ℝ z.re z.im := by
  rfl
/-- Complexification of a submodule, i.e., `(a, b) ∈ K.complexification ↔ a ∈ K ∧ b ∈ K`. -/
@[expose]
def _root_.Submodule.complexification (K : Submodule 𝕜 E) : Submodule ℂ (Complexification 𝕜 E) where
  carrier := { v | v.re ∈ K } ∩ { v | v.im ∈ K }
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' := by aesop

@[simp] lemma _root_.Submodule.mem_complexification {K : Submodule 𝕜 E} (x : Complexification 𝕜 E) :
    x ∈ K.complexification ↔ x.re ∈ K ∧ x.im ∈ K := by simp [Submodule.complexification]

variable (𝕜 E) in
/-- The inclusion map of a space into its complexification as a linear isometry, given by
`x ↦ (x, 0)`. -/
@[expose, simps] def inclusion [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    E →ₗᵢ[ℝ] Complexification 𝕜 E where
  toFun x := .mk 𝕜 x 0
  map_add' := by simp
  map_smul' _ _ := by ext <;> simp
  norm_map' := by simp

/-- A submodule `U` over the complexificationn of a real space is a complexified submodule
(i.e., there exists a real submodule `S` such that `S.complexification = U`)
iff `U` is closed under conjugation.

This is Chapter 1, Exercise 26 in [roman_advanced_linear_algebra]. -/
lemma _root_.Submodule.exists_complexification_eq_iff (U : Submodule ℂ (Complexification ℝ Eₗ)) :
    (∃ S : Submodule ℝ Eₗ, S.complexification = U) ↔ ∀ v ∈ U, conj ℝ Eₗ v ∈ U := by
  refine ⟨fun ⟨S, hS⟩ v hv ↦ by simpa [← hS, conj_apply] using hv, fun h ↦ ?_⟩
  refine ⟨(U.restrictScalars ℝ).comap (inclusion ℝ Eₗ).toLinearMap, Submodule.ext fun x ↦ ?_⟩
  simp only [Submodule.mem_complexification, Submodule.mem_comap, LinearIsometry.coe_toLinearMap,
    inclusion_apply, Submodule.restrictScalars_mem]
  refine ⟨fun h2 ↦ ?_, fun h2 ↦ ⟨?_, ?_⟩⟩
  · rw [← mk_re_im x, mk_eq_add_I_smul]
    exact add_mem h2.1 (Submodule.smul_mem _ _ h2.2)
  · convert Submodule.smul_mem _ (2 : ℂ)⁻¹ (add_mem h2 (h _ h2))
    simp [conj_apply, Complexification.ext_iff, ← two_smul ℝ]
  · convert Submodule.smul_mem _ (2 * Complex.I)⁻¹ (sub_mem h2 (h _ h2))
    simp [Complexification.ext_iff, conj_apply, ← two_smul ℝ]

end Complexification

namespace ContinuousLinearMap
variable [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open Complexification

/-- Complexification of a continuous linear map between inner product spaces. -/
@[expose, simps apply_apply] def toComplexification :
    (E →L[𝕜] F) →+ Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F where
  toFun T :=
    { toFun v := .mk 𝕜 (T v.re) (T v.im)
      map_add' _ _ := by ext <;> simp
      map_smul' _ _ := by ext <;> simp }
  map_add' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp

@[simp] lemma toComplexification_id :
    (ContinuousLinearMap.id 𝕜 E).toComplexification = .id ℂ (Complexification 𝕜 E) := by
  ext <;> simp

@[simp] lemma toComplexification_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S.comp T).toComplexification = S.toComplexification.comp T.toComplexification := by
  ext <;> simp

@[simp] lemma toComplexification_one : (1 : E →L[𝕜] E).toComplexification = 1 := by ext <;> simp

@[simp] lemma toComplexification_mul (S T : E →L[𝕜] E) :
    (S * T).toComplexification = S.toComplexification * T.toComplexification := by simp [mul_def]

@[simp] lemma opNorm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖ = ‖T‖ := by
  refine le_antisymm ((opNorm_le_iff (norm_nonneg _)).mpr fun _ ↦ ?_) ?_
  · refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    simp only [mul_pow, norm_sq_eq, mul_add, toComplexification_apply_apply, re_mk, im_mk]
    grw [T.le_opNorm, T.le_opNorm]
    simp [mul_pow]
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using T.toComplexification.le_opNorm (.mk 𝕜 x 0)

@[simp] lemma opNNNorm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖₊ = ‖T‖₊ := by
  ext; simp
@[simp] lemma opENorm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖ₑ = ‖T‖ₑ := by
  simp [enorm_eq_nnnorm]

lemma toComplexification_injective :
    Function.Injective (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) := fun S T h ↦ by
  ext x; simpa using congr(($h (.mk 𝕜 x 0)).re)

@[simp] lemma toComplexification_inj {S T : E →L[𝕜] F} :
    S.toComplexification = T.toComplexification ↔ S = T :=
  toComplexification_injective.eq_iff

@[simp] lemma isIdempotentElem_toComplexification_iff {S : E →L[𝕜] E} :
    IsIdempotentElem S.toComplexification ↔ IsIdempotentElem S := by
  simp [IsIdempotentElem, ← toComplexification_mul]

alias ⟨_, _root_.IsIdempotentElem.toComplexification⟩ := isIdempotentElem_toComplexification_iff

@[simp] lemma injective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Injective T.toComplexification ↔ Function.Injective T := by
  refine ⟨fun h x y hxy ↦ ?_, fun h x y hxy ↦ ?_⟩
  · simpa using congr(($(h (a₁ := .mk 𝕜 x 0) (a₂ := .mk 𝕜 y 0)
      (by ext <;> simp [hxy]))).re)
  · have := by simpa [h.eq_iff] using congr(($hxy).re)
    have := by simpa [h.eq_iff] using congr(($hxy).im)
    simp_all [Complexification.ext_iff]

@[simp] lemma surjective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Surjective T.toComplexification ↔ Function.Surjective T := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨v, hv⟩ := h (.mk 𝕜 x 0)
    exact ⟨v.re, by simpa using congr(($hv).re)⟩
  · obtain ⟨v, hv⟩ := h x.re
    obtain ⟨w, hw⟩ := h x.im
    exact ⟨.mk 𝕜 v w, by simp [hv, hw]⟩

@[simp] lemma bijective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Bijective T.toComplexification ↔ Function.Bijective T := by
  simp [Function.Bijective]

lemma isometry_toComplexification : Isometry (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  .of_dist_eq <| by simp [dist_eq_norm, ← map_sub]

@[simp] lemma isometry_toComplexification_iff {T : E →L[𝕜] F} :
    Isometry T.toComplexification ↔ Isometry T := by
  simp only [AddMonoidHomClass.isometry_iff_norm]
  refine ⟨fun h x ↦ by simpa using h (.mk 𝕜 x 0), fun h v ↦ ?_⟩
  simp [← sq_eq_sq₀, norm_sq_eq, h]

@[fun_prop] lemma continuous_toComplexification :
    Continuous (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  isometry_toComplexification.continuous

@[simp] lemma ker_toComplexification (T : E →L[𝕜] F) :
    T.toComplexification.ker = T.ker.complexification := by
  ext; simp [Complexification.ext_iff]

@[simp] lemma range_toComplexification (T : E →L[𝕜] F) :
   T.toComplexification.range = T.range.complexification := by
  ext x
  simp only [LinearMap.mem_range, coe_coe, toComplexification_apply_apply,
    Complexification.ext_iff, re_mk, im_mk, Submodule.mem_complexification]
  exact ⟨by grind, fun ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ ⟨.mk 𝕜 y z, by simp [hy, hz]⟩⟩

/-- Conjugation of a complexified operator given by `T ↦ conj ∘ T ∘ conj`.

An opeartor is equal to its conjugate iff it is a complexified operator
(see `exists_toComplexification_eq_iff`). -/
@[expose, simps! apply_apply] noncomputable def conjugate :
    (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) ≃ₗᵢ⋆[ℂ]
      (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) where
  __ := (conj 𝕜 E).toContinuousLinearEquiv.arrowCongrEquivₛₗ (conj 𝕜 F).toContinuousLinearEquiv
  norm_map' x := by simpa using! opNorm_comp_linearIsometryEquiv _ (conj 𝕜 E).symm

@[simp] lemma conjugate_conjugate (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) :
    T.conjugate.conjugate = T := by ext1; simp

@[simp] lemma symm_conjugate : conjugate (𝕜 := 𝕜) (E := E) (F := F).symm = conjugate := rfl

@[simp] lemma conjugate_id :
    (ContinuousLinearMap.id ℂ (Complexification 𝕜 E)).conjugate = .id ℂ _ := by ext1; simp

@[simp] lemma conjugate_one :
    (1 : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E).conjugate = 1 := conjugate_id

@[simp] lemma conjugate_comp (S : Complexification 𝕜 F →L[ℂ] Complexification 𝕜 G)
    (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) :
    (S ∘SL T).conjugate = S.conjugate ∘SL T.conjugate := by ext1; simp

@[simp] lemma conjugate_mul (S T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :
    (S * T).conjugate = S.conjugate * T.conjugate := conjugate_comp _ _

@[simp] lemma conjugate_toComplexification (S : E →L[𝕜] F) :
    S.toComplexification.conjugate = S.toComplexification := by ext1; simp [conj_apply]

/-- Decomplexifying an operator on complexifications given that it commutes with
the complexification of `algebraMapCLM 𝕜 _ RCLike.I`. -/
@[expose, simps!]
noncomputable def ofComplexification [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F)
    (hT : T ∘SL (algebraMapCLM 𝕜 (E →L[𝕜] E) RCLike.I).toComplexification =
      (algebraMapCLM 𝕜 (F →L[𝕜] F) RCLike.I).toComplexification ∘SL T) :
    E →L[𝕜] F :=
  let S := reL 𝕜 F ∘SL T.restrictScalars ℝ ∘SL (inclusion 𝕜 E).toContinuousLinearMap
  { __ := S.toAddMonoidHom
    map_smul' a x := by
      suffices ∀ x, S ((RCLike.I : 𝕜) • x) = (RCLike.I : 𝕜) • S x by
        rw [← RCLike.re_add_im a, add_smul, mul_smul]
        simp [this, -RCLike.re_add_im, add_smul, mul_smul]
      intro x
      simpa [S] using congr(($hT (.mk 𝕜 x 0)).re) }

@[simp] lemma ofComplexification_zero [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] :
    (0 : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F).ofComplexification (by simp) = 0 := by
  ext; simp

@[simp] lemma ofComplexification_id [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    (.id ℂ _ : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E).ofComplexification (by simp) =
      .id _ _ := by
  ext; simp

@[simp] lemma ofComplexification_one [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    (1 : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E).ofComplexification (by simp [one_def]) =
      1 :=
  ofComplexification_id

@[simp] lemma ofComplexification_toComplexification
    [Module ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    (T : E →L[𝕜] F) (h) :
    T.toComplexification.ofComplexification h = T := by ext; simp

@[simp] lemma restrictScalars_ofComplexification
    [Module ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) (h) :
    (T.ofComplexification h).restrictScalars ℝ =
      reL 𝕜 F ∘SL T.restrictScalars ℝ ∘SL (inclusion 𝕜 E).toContinuousLinearMap := rfl

lemma toComplexification_ofComplexification
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    {T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F} (h) (hT : T.conjugate = T) :
    (T.ofComplexification h).toComplexification = T := by
  ext1 v
  conv_rhs => rw [← mk_re_im v, mk_eq_add_I_smul]
  simp only [map_add, map_smul]
  have (x : E) : T (.mk 𝕜 x 0) = .mk 𝕜 (T (.mk 𝕜 x 0)).re 0 := by
    refine Complexification.ext rfl ?_
    rw [im_mk, ← conj_eq_self_iff]
    conv_rhs => rw [← hT]
    simp
  simp +singlePass only [this]
  ext <;> simp

/-- An operator `T` on a complexification space of a real space is a complexified operator
(i.e., there exists an operator `S` such that `S.toComplexification = T`) iff `T.conjugate = T`
and it commutes with the complexification of `algebraMapCLM 𝕜 _ RCLike.I`.

This is Chapter 2, Exercise 32 in [roman_advanced_linear_algebra]. -/
lemma exists_toComplexification_eq_iff
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    {T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F} :
    (∃ S : E →L[𝕜] F, S.toComplexification = T) ↔ T.conjugate = T ∧
      T ∘SL (algebraMapCLM 𝕜 (E →L[𝕜] E) RCLike.I).toComplexification =
        (algebraMapCLM 𝕜 (F →L[𝕜] F) RCLike.I).toComplexification ∘SL T := by
  refine ⟨fun ⟨S, hS⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ⟨_, toComplexification_ofComplexification h2 h1⟩⟩
  simp [← hS, ContinuousLinearMap.ext_iff]

variable [CompleteSpace E] [CompleteSpace F]

@[simp] lemma adjoint_toComplexification (T : E →L[𝕜] F) :
    T.toComplexification.adjoint = T.adjoint.toComplexification := by
  simp [eq_comm, eq_adjoint_iff, Complex.ext_iff, adjoint_inner_left]

@[simp] lemma star_toComplexification (T : E →L[𝕜] E) :
    star T.toComplexification = (star T).toComplexification :=
  adjoint_toComplexification T

@[simp] lemma isSelfAdjoint_toComplexification_iff {T : E →L[𝕜] E} :
    IsSelfAdjoint T.toComplexification ↔ IsSelfAdjoint T := by simp [isSelfAdjoint_iff]

alias ⟨_, _root_.IsSelfAdjoint.toComplexification⟩ := isSelfAdjoint_toComplexification_iff

attribute [aesop safe apply] IsSelfAdjoint.toComplexification

@[simp] lemma isStarNormal_toComplexification_iff {T : E →L[𝕜] E} :
    IsStarNormal T.toComplexification ↔ IsStarNormal T := by
  simp [isStarNormal_iff, commute_iff_eq, ← toComplexification_mul]

alias ⟨_, _root_.IsStarNormal.toComplexification⟩ := isStarNormal_toComplexification_iff

@[simp] lemma isStarProjection_toComplexification_iff {T : E →L[𝕜] E} :
    IsStarProjection T.toComplexification ↔ IsStarProjection T := by
  simp [isStarProjection_iff]

@[simp] lemma isUnit_toComplexification_iff {T : E →L[𝕜] E} :
    IsUnit T.toComplexification ↔ IsUnit T := by simp [isUnit_iff_bijective]

@[simp] lemma spectrum_toComplexification (T : E →L[𝕜] E) :
    spectrum ℝ T.toComplexification = algebraMap ℝ 𝕜 ⁻¹' spectrum 𝕜 T := by
  ext r
  simp only [spectrum.mem_iff, Set.mem_preimage, not_iff_not]
  conv_rhs => rw [← isUnit_toComplexification_iff]
  congr! 1
  simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.ext_iff, Complexification.ext_iff]

lemma spectrum_toComplexification_real [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    (T : E →L[𝕜] E) : spectrum ℝ T.toComplexification = spectrum ℝ T := by simp

@[simp] lemma quasispectrum_toComplexification (T : E →L[𝕜] E) :
    quasispectrum ℝ T.toComplexification = algebraMap ℝ 𝕜 ⁻¹' quasispectrum 𝕜 T := by
  simp [quasispectrum_eq_spectrum_union_zero, Set.ext_iff]

lemma quasispectrum_toComplexification_real [Algebra ℝ (E →L[𝕜] E)]
    [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] (T : E →L[𝕜] E) :
    quasispectrum ℝ T.toComplexification = quasispectrum ℝ T := by simp

@[simp] lemma conjugate_adjoint (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F) :
    T.adjoint.conjugate = T.conjugate.adjoint := by
  simp [eq_adjoint_iff, inner_conj_left (T.adjoint _), adjoint_inner_right, inner_conj_right (T _)]

@[simp] lemma conjugate_star (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :
    (star T).conjugate = star T.conjugate := conjugate_adjoint _

@[simp] lemma isPositive_toComplexification_iff {T : E →L[𝕜] E} :
    T.toComplexification.IsPositive ↔ T.IsPositive := by
  simp only [isPositive_def', isSelfAdjoint_toComplexification_iff, reApplyInnerSelf_apply,
    toComplexification_apply_apply, RCLike.re_to_complex, re_inner, re_mk, im_mk, map_add,
    and_congr_right_iff]
  refine fun _ ↦ ⟨fun hT x ↦ ?_, fun hT x ↦ add_nonneg (hT x.re) (hT x.im)⟩
  simpa using hT (.mk 𝕜 x 0)

@[simp] lemma toComplexification_nonneg_iff {T : E →L[𝕜] E} :
    0 ≤ T.toComplexification ↔ 0 ≤ T := by simp [nonneg_iff_isPositive]

@[simp] lemma toComplexification_le_toComplexification_iff {S T : E →L[𝕜] E} :
    S.toComplexification ≤ T.toComplexification ↔ S ≤ T := by simp [le_def, ← map_sub]

end ContinuousLinearMap
