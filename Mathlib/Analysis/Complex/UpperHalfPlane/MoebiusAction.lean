/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Group action on the upper half-plane

We equip the upper half-plane with the structure of a `GL (Fin 2) ℝ` action by fractional linear
transformations (composing with complex conjugation when needed to extend the action from the
positive-determinant subgroup, so that `!![-1, 0; 0, 1]` acts as `z ↦ -conj z`.)
-/

@[expose] public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace UpperHalfPlane

/-- Numerator of the formula for a fractional linear transformation -/
def num (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 0 0 * z + g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
def denom (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 1 0 * z + g 1 1

@[simp]
lemma num_neg (g : GL (Fin 2) ℝ) (z : ℂ) : num (-g) z = -(num g z) := by
  simp [num]; ring

@[simp]
lemma denom_neg (g : GL (Fin 2) ℝ) (z : ℂ) : denom (-g) z = -(denom g z) := by
  simp [denom]; ring

theorem linear_ne_zero_of_im {cd : Fin 2 → ℝ} {z : ℂ} (hz : z.im ≠ 0) (h : cd ≠ 0) :
    (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using h
  simp only [this, zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero] at h
  ext i
  fin_cases i <;> assumption

theorem linear_ne_zero {cd : Fin 2 → ℝ} (τ : ℍ) (h : cd ≠ 0) :
    (cd 0 : ℂ) * τ + cd 1 ≠ 0 :=
  linear_ne_zero_of_im τ.im_ne_zero h

theorem denom_ne_zero_of_im (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : denom g z ≠ 0 := by
  refine linear_ne_zero_of_im hz fun H ↦ g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

theorem denom_ne_zero (g : GL (Fin 2) ℝ) (z : ℍ) : denom g z ≠ 0 :=
  denom_ne_zero_of_im g z.im_ne_zero

theorem normSq_denom_pos (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

theorem normSq_denom_ne_zero (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gt (normSq_denom_pos g hz)

lemma denom_cocycle (g h : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    denom (g * h) z = denom g (num h z / denom h z) * denom h z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero_of_im h hz]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

lemma moebius_im (g : GL (Fin 2) ℝ) (z : ℂ) :
    (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z) := by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

/-- Automorphism of `ℂ`: the identity if `0 < det g` and conjugation otherwise. -/
noncomputable def σ (g : GL (Fin 2) ℝ) : ℂ ≃A[ℝ] ℂ :=
  if 0 < g.det.val then .refl ℝ ℂ else Complex.conjCAE

lemma σ_conj (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (conj z) = conj (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp]
lemma σ_ofReal (g : GL (Fin 2) ℝ) (y : ℝ) : σ g y = y := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_num (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (num h z) = num h (σ g z) := by
  simp [num]

lemma σ_denom (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (denom h z) = denom h (σ g z) := by
  simp [denom]

@[simp]
lemma σ_neg (g : GL (Fin 2) ℝ) : σ (-g) = σ g := by
  simp [σ, det_neg]

@[simp]
lemma σ_sq (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ g z) = z := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_im_ne_zero {g z} : (σ g z).im ≠ 0 ↔ z.im ≠ 0 := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_mul (g g' : GL (Fin 2) ℝ) (z : ℂ) : σ (g * g') z = σ g (σ g' z) := by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').not_gt, h, h'.not_gt]
  · simp [mul_pos h h', h, h']

lemma σ_mul_comm (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ h z) = σ h (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp] lemma norm_σ (g : GL (Fin 2) ℝ) (z : ℂ) : ‖σ g z‖ = ‖z‖ := by
  simp only [σ]
  split_ifs <;> simp

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux' (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := σ g (num g z / denom g z)

lemma smulAux'_im (g : GL (Fin 2) ℝ) (z : ℂ) :
    (smulAux' g z).im = |g.det.val| * z.im / Complex.normSq (denom g z) := by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
    neg_mul, neg_div, neg_inj] using moebius_im g z

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux (g : GL (Fin 2) ℝ) (z : ℍ) : ℍ :=
  mk (smulAux' g z) <| by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)

lemma denom_cocycle' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g (smulAux h z)) * denom h z := by
  simp only [smulAux, smulAux', coe_mk, map_div₀, σ_num, σ_denom, σ_sq]
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero h z]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

theorem mul_smul' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    smulAux (g * h) z = smulAux g (smulAux h z) := by
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  generalize hu : σ g (σ h z) = u
  have hu : u.im ≠ 0 := by simpa only [← hu, σ_im_ne_zero] using z.im_ne_zero
  have hu' : (num h u / denom h u).im ≠ 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_zero h.det_ne_zero hu) (normSq_denom_ne_zero _ hu)
  rw [div_eq_div_iff (denom_ne_zero_of_im _ hu) (denom_ne_zero_of_im _ hu'),
    denom, mul_div, div_add' _ _ _ (denom_ne_zero_of_im _ hu), mul_div]
  conv_rhs => rw [num]
  rw [mul_div, div_add' _ _ _ (denom_ne_zero_of_im _ hu), div_mul_eq_mul_div]
  congr 1
  simp only [num, denom, Units.val_mul, mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- Action of `GL (Fin 2) ℝ` on the upper half-plane, with `GL(2, ℝ)⁺` acting by Moebius
transformations in the usual way, extended to all of `GL (Fin 2) ℝ` using complex conjugation. -/
instance glAction : MulAction (GL (Fin 2) ℝ) ℍ where
  smul := smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'

lemma coe_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    ↑(g • z) = σ g (num g z / denom g z) := rfl

lemma coe_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    ↑(g • z) = num g z / denom g z := by
  change smulAux' g z = _
  rw [smulAux', σ, if_pos hg, ContinuousAlgEquiv.refl_apply, num, denom]

lemma denom_cocycle_σ (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g ↑(h • z)) * denom h z :=
  denom_cocycle' g h z

lemma glPos_smul_def {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    g • z = ⟨num g z / denom g z, coe_smul_of_det_pos hg z ▸ (g • z).im_pos⟩ := by
  ext; simp [coe_smul_of_det_pos hg]

variable (g : GL (Fin 2) ℝ) (z : ℍ)

theorem re_smul : (g • z).re = (num g z / denom g z).re := by
  change (smulAux' g z).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]

theorem im_smul : (g • z).im = |(num g z / denom g z).im| := by
  change (smulAux' g z).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
    Complex.conjCAE_apply, Complex.conj_im, ← neg_div, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : ℂ).im from z.coe_im ▸ z.im_pos),
    abs_of_nonneg <| Complex.normSq_nonneg _]
  split_ifs with h <;> [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]]

lemma im_smul_eq_div_normSq : (g • z).im = |g.det.val| * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z

theorem c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom g z) := by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]
theorem neg_smul : -g • z = g • z := by
  ext1
  simp [coe_smul]

lemma denom_one : denom 1 z = 1 := by
  simp [denom]

section SLAction
/-!
## Action of the special linear group
-/

noncomputable instance SLAction {R : Type*} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.mapGL ℝ

theorem coe_specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    ↑(g • z) =
      (((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ)) /
      ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ))) := by
  rw [MulAction.compHom_smul_def, coe_smul_of_det_pos (by simp)]
  rfl

theorem specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    g • z = mk
      (((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ)) /
      ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ)))
      (coe_specialLinearGroup_apply g z ▸ (g • z).im_pos) := by
  ext; simp [coe_specialLinearGroup_apply]

/- these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/
theorem modular_S_smul (z : ℍ) :
    ModularGroup.S • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos := by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div, inv_neg]

theorem modular_T_zpow_smul (z : ℍ) (n : ℤ) : ModularGroup.T ^ n • z = (n : ℝ) +ᵥ z := by
  rw [UpperHalfPlane.ext_iff, coe_vadd, add_comm, coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one]

theorem modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : ℝ) +ᵥ z := by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v : ℝ), (g • · : ℍ → ℍ) = (v +ᵥ ·) ∘ (u • ·) := by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by simpa [specialLinearGroup_apply, add_mul]
  ring

theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : g 1 0 ≠ 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v w : ℝ),
      (g • · : ℍ → ℍ) =
        (w +ᵥ ·) ∘ (ModularGroup.S • · : ℍ → ℍ) ∘ (v +ᵥ · : ℍ → ℍ) ∘ (u • · : ℍ → ℍ) := by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c ≠ 0 := by simpa using hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹ by
    simpa [modular_S_smul, coe_specialLinearGroup_apply]
  replace hc : (c : ℂ) ≠ 0 := by norm_cast
  replace h_denom : ↑c * z + d ≠ 0 := by simpa using h_denom ⟨z, hz⟩
  replace h : (a * d - b * c : ℂ) = (1 : ℂ) := by norm_cast
  grind

end SLAction

section toSL2R

/-- Map from `ℍ` to `SL(2, ℝ)`, giving a continuous section of the map `g ↦ g • I`. -/
noncomputable def toSL2R (z : ℍ) : SL(2, ℝ) :=
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩

lemma toSL2R_apply (z : ℍ) : z.toSL2R =
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩ := (rfl)

@[simp] lemma coe_toSL2R (z : ℍ) : z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im] := (rfl)

@[simp] lemma toSL2R_smul_I (z : ℍ) : z.toSL2R • I = z := by
  have : √z.im ≠ (0 : ℂ) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply, div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this), mul_right_comm, ← Complex.ofReal_mul, ← Real.sqrt_mul z.im_pos.le,
    Real.sqrt_mul_self z.im_pos.le, re_add_im, div_eq_mul_inv]

/-- `SL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveSL2R : MulAction.IsPretransitive SL(2, ℝ) ℍ :=
  .of_orbit fun z ↦ ⟨_, toSL2R_smul_I z⟩

/-- `GL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ :=
  .of_smul_eq ((↑) : SL(2, ℝ) → _) fun {g z} ↦ (MulAction.compHom_smul_def _ g z).symm

end toSL2R

section J
/-!
## The anti-holomorphic involution `J`
-/

/-- The matrix `[-1, 0; 0, 1]`, which defines an anti-holomorphic involution of `ℍ` via
`τ ↦ -conj τ`. -/
def J : GL (Fin 2) ℝ := .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

lemma coe_J_smul (τ : ℍ) : (↑(J • τ) : ℂ) = -conj ↑τ := by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : ℝ) < 0 by simp, num, denom]

@[simp] lemma val_J : J.val = !![-1, 0; 0, 1] := rfl

@[simp] lemma J_sq : J ^ 2 = 1 := by ext; simp [J, sq, Matrix.one_fin_two]

@[simp] lemma det_J : J.det = -1 := by ext; simp [J]

@[simp] lemma sigma_J : σ J = Complex.conjCAE := by simp [σ, J]

@[simp] lemma denom_J (τ : ℂ) : denom J τ = 1 := by simp [J, denom]

@[simp]
lemma denom_J_mul (g : GL (Fin 2) ℝ) (τ : ℂ) : denom (J * g) τ = denom g τ := by
  simp [denom, vecMul, vecHead, vecTail]

@[simp] lemma inv_J : J⁻¹ = J := by rw [inv_eq_iff_mul_eq_one, ← sq, J_sq]

@[simp] lemma J_smul_pos_smul_I {t : ℝ} (ht : 0 < t) :
    J • Subtype.mk t ht • I = Subtype.mk t ht • I := by
  ext
  simp [coe_J_smul]

end J

section Stabilizer
/-!
## Stabilizers and fixed points
-/

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)₊` is the scalar multiples
of the identity. -/
lemma forall_smul_pos_mul_I_eq_iff_of_det_pos {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) :
    (∀ (t : ℝ) (ht : 0 < t), g • (Subtype.mk t ht • I) = (Subtype.mk t ht • I))
      ↔ ∃ r : ℝˣ, g = r • 1 where
  mp hg := by
    have (t : ℝ) (ht : 0 < t) : g 0 1 = -t ^ 2 * g 1 0 ∧ g 0 0 = g 1 1 := by
      have := congr_arg UpperHalfPlane.coe <| hg t ht
      simp only [coe_smul_of_det_pos hdet, coe_pos_real_smul, coe_I, Complex.real_smul] at this
      rw [div_eq_iff (denom_ne_zero_of_im _ <| by simp [ht.ne']), Complex.ext_iff] at this
      grind [num, denom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have hbc : g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = g 0 0 := by grind [this 1 one_pos, this 2 two_pos]
    have : g 0 0 ≠ 0 := by grind [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    use .mk0 _ this
    ext i j
    simp only [Fin.isValue, Units.val_smul, Units.val_one, Matrix.one_fin_two, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Units.smul_mk0, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [hbc]
  mpr := by
    rintro ⟨r, rfl⟩ t ht
    ext
    simp [coe_pos_real_smul, coe_smul_of_det_pos hdet, num, denom, Units.smul_def]

/-- The pointwise stabilizer of the vertical line `ℝ₊ • I` in `GL(2, ℝ)` consists of the scalar
multiples of the identity and of `J = [-1, 0; 0, 1]`. -/
lemma forall_smul_pos_mul_I_eq_iff {g : GL (Fin 2) ℝ} :
    (∀ (t : ℝ) (ht : 0 < t), g • (Subtype.mk t ht • I) = (Subtype.mk t ht • I)) ↔
      (∃ r : ℝˣ, g = r • 1) ∨ (∃ r : ℝˣ, g = r • J) := by
  by_cases h : 0 < g.det.val
  · rw [forall_smul_pos_mul_I_eq_iff_of_det_pos h]
    suffices ¬∃ r, g = r • J by tauto
    contrapose! h
    obtain ⟨r, rfl⟩ := h
    simp [Units.smul_def, mul_self_nonneg r.val]
  · -- If `det g < 0`, we show that `g * J⁻¹` also fixes the vertical line
    have : ¬∃ r : ℝˣ, g = r • 1 := by
      contrapose! h
      rcases h with ⟨r, rfl⟩
      refine lt_of_le_of_ne' ?_ (Units.ne_zero _)
      simp [Units.smul_def, sq_nonneg]
    rw [eq_false_intro this, false_or]
    conv => enter [1, t, ht, 1]; rw [← J_smul_pos_smul_I, ← SemigroupAction.mul_smul, ← inv_J]
    rw [forall_smul_pos_mul_I_eq_iff_of_det_pos]
    · simp only [mul_inv_eq_iff_eq_mul (a := g), smul_one_mul]
    · rw [map_mul, map_inv, det_J, inv_neg_one, mul_neg_one, Units.val_neg]
      grind [g.det_ne_zero.lt_or_gt, Matrix.GeneralLinearGroup.val_det_apply]

/-- The only elements of `GL(2, ℝ)` that act trivially on the whole upper half-plane are the
scalar matrices. -/
lemma forall_smul_eq_iff {g : GL (Fin 2) ℝ} : (∀ τ : ℍ, g • τ = τ) ↔ (∃ r : ℝˣ, g = r • 1) where
  mp h := by
    refine (forall_smul_pos_mul_I_eq_iff.mp (fun t ht ↦ h _)).resolve_right fun ⟨r, hr⟩ ↦ ?_
    simpa [hr, UpperHalfPlane.ext_iff, coe_smul, σ, Units.smul_def, (mul_self_nonneg r.val).not_gt,
      num, denom, div_eq_iff (Complex.ofReal_ne_zero.mpr r.ne_zero), Complex.ext_iff, neg_eq_self]
      using h ((1 : ℝ) +ᵥ I)
  mpr := fun ⟨r, hr⟩ τ ↦ UpperHalfPlane.ext <| by
    simp [hr, coe_smul, σ, Units.smul_def, sq_pos_of_ne_zero r.ne_zero, num, denom]

lemma forall_smul_eq_iff_of_det_eq_one {g : GL (Fin 2) ℝ} (hg : g.det = 1) :
    (∀ τ : ℍ, g • τ = τ) ↔ g = 1 ∨ g = -1 := by
  rw [UpperHalfPlane.forall_smul_eq_iff]
  constructor
  · rintro ⟨r, rfl⟩
    have : r ^ 2 • (1 : ℝ) = 1 := by simpa [Units.ext_iff] using hg
    have : r = 1 ∨ r = -1 := by simpa [Units.smul_def]
    aesop
  · rintro (rfl | rfl)
    · exact ⟨1, by ext; simp⟩
    · exact ⟨-1, by ext; simp⟩

end Stabilizer

end UpperHalfPlane

namespace ModularGroup -- results specific to `SL(2, ℤ)`
-- TODO: Move these elsewhere, maybe somewhere in the algebra or number theory hierarchies?

section ModularScalarTowers

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`. -/
@[coe]
def coe (g : SL(2, ℤ)) : GL(2, ℝ)⁺ := ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)

@[simp]
lemma coe_inj (a b : SL(2, ℤ)) : coe a = coe b ↔ a = b := by
  refine ⟨fun h ↦ a.ext b fun i j ↦ ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

instance : Coe SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨coe⟩

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`, bundled as a group hom. -/
def coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺ := toGLPos.comp <| map <| Int.castRingHom _

@[simp] lemma coeHom_apply (g : SL(2, ℤ)) : coeHom g = coe g := rfl

@[simp]
theorem coe_apply_complex {g : SL(2, ℤ)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe g) i j = (Subtype.val g i j : ℂ) :=
  rfl

@[simp]
theorem det_coe {g : SL(2, ℤ)} : det (Units.val <| Subtype.val <| coe g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

lemma coe_one : coe 1 = 1 := by
  simp only [coe, map_one]

instance SLOnGLPos : SMul SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩

theorem SLOnGLPos_smul_apply (s : SL(2, ℤ)) (g : GL(2, ℝ)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl

instance SL_to_GL_tower : IsScalarTower SL(2, ℤ) GL(2, ℝ)⁺ ℍ where
  smul_assoc s g z := by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

end ModularScalarTowers

section SLModularAction

variable (g : SL(2, ℤ)) (z : ℍ)

@[simp]
theorem sl_moeb : g • z = (g : GL (Fin 2) ℝ) • z := rfl

@[simp high]
theorem SL_neg_smul : -g • z = g • z := by
  rw [sl_moeb, ← z.neg_smul]
  congr 1 with i j
  simp [toGL]

theorem im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  simpa using z.im_smul_eq_div_normSq g

theorem denom_apply : denom g z = g 1 0 * z + g 1 1 := rfl

@[simp] lemma denom_S : denom S z = z := by simp [S, denom_apply]

/-- No element of `SL(2, ℤ)` except `±1` acts trivially on `ℍ`. -/
lemma forall_smul_eq_iff : (∀ τ : ℍ, g • τ = τ) ↔ g = 1 ∨ g = -1 := by
  simp only [sl_moeb, forall_smul_eq_iff_of_det_eq_one <| coeToGL_det _, ← mapGL_inj (S := ℝ),
    map_one]
  congr!
  ext
  simp

end SLModularAction

end ModularGroup
