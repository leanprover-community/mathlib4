/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Parity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The upper half plane and its automorphisms

This file defines `UpperHalfPlane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of a `GLPos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

noncomputable section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }

@[inherit_doc] scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

open UpperHalfPlane

namespace UpperHalfPlane

/-- The coercion first into an element of  `GL(2, ℝ)⁺`, then  `GL(2, ℝ)` and finally a 2 × 2
matrix.

This notation is scoped in namespace `UpperHalfPlane`. -/
scoped notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)

instance instCoeFun : CoeFun GL(2, ℝ)⁺ fun _ => Fin 2 → Fin 2 → ℝ where coe A := ↑ₘA

/-- The coercion into an element of  `GL(2, R)` and finally a 2 × 2 matrix over `R`. This is
similar to `↑ₘ`, but without positivity requirements, and allows the user to specify the ring `R`,
which can be useful to help Lean elaborate correctly.

This notation is scoped in namespace `UpperHalfPlane`. -/
scoped notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

/-- Canonical embedding of the upper half-plane into `ℂ`. -/
@[coe] protected def coe (z : ℍ) : ℂ := z.1

instance : CoeOut ℍ ℂ := ⟨UpperHalfPlane.coe⟩

instance : Inhabited ℍ :=
  ⟨⟨Complex.I, by simp⟩⟩

@[ext] theorem ext {a b : ℍ} (h : (a : ℂ) = b) : a = b := Subtype.eq h

@[simp, norm_cast] theorem ext_iff' {a b : ℍ} : (a : ℂ) = b ↔ a = b := UpperHalfPlane.ext_iff.symm

instance canLift : CanLift ℂ ℍ ((↑) : ℍ → ℂ) fun z => 0 < z.im :=
  Subtype.canLift fun (z : ℂ) => 0 < z.im

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re

/-- Extensionality lemma in terms of `UpperHalfPlane.re` and `UpperHalfPlane.im`. -/
theorem ext' {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im) : a = b :=
  ext <| Complex.ext hre him

/-- Constructor for `UpperHalfPlane`. It is useful if `⟨z, h⟩` makes Lean use a wrong
typeclass instance. -/
def mk (z : ℂ) (h : 0 < z.im) : ℍ :=
  ⟨z, h⟩

@[simp]
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl

@[simp]
theorem mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl

@[simp]
theorem mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl

@[simp]
theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl

@[simp]
lemma coe_mk_subtype {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z := by
  rfl

@[simp]
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  rfl

theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.I : ℂ) = z :=
  Complex.re_add_im z

theorem im_pos (z : ℍ) : 0 < z.im :=
  z.2

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero

/-- Define I := √-1 as an element on the upper half plane. -/
def I : ℍ := ⟨Complex.I, by simp⟩

@[simp]
lemma I_im : I.im = 1 := rfl

@[simp]
lemma I_re : I.re = 0 := rfl

@[simp, norm_cast]
lemma coe_I : I = Complex.I := rfl

end UpperHalfPlane

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `UpperHalfPlane.im`. -/
@[positivity UpperHalfPlane.im _]
def evalUpperHalfPlaneIm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(UpperHalfPlane.im $a) =>
    assertInstancesCommute
    pure (.positive q(@UpperHalfPlane.im_pos $a))
  | _, _, _ => throwError "not UpperHalfPlane.im"

/-- Extension for the `positivity` tactic: `UpperHalfPlane.coe`. -/
@[positivity UpperHalfPlane.coe _]
def evalUpperHalfPlaneCoe : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(UpperHalfPlane.coe $a) =>
    assertInstancesCommute
    pure (.nonzero q(@UpperHalfPlane.ne_zero $a))
  | _, _, _ => throwError "not UpperHalfPlane.coe"

end Mathlib.Meta.Positivity

namespace UpperHalfPlane

theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_pos]; exact z.ne_zero

theorem normSq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (normSq_pos z).ne'

theorem im_inv_neg_coe_pos (z : ℍ) : 0 < (-z : ℂ)⁻¹.im := by
  simpa using div_pos z.property (normSq_pos z)

lemma ne_nat (z : ℍ) : ∀ n : ℕ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

lemma ne_int (z : ℍ) : ∀ n : ℤ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

/-- Numerator of the formula for a fractional linear transformation -/
def num (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ := g 0 0 * z + g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
def denom (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ := g 1 0 * z + g 1 1

theorem linear_ne_zero (cd : Fin 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose! h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [z.im_ne_zero, Complex.add_im, add_zero, coe_im, zero_mul, or_false,
      Complex.ofReal_im, Complex.zero_im, Complex.mul_im, mul_eq_zero] using h
  simp only [this, zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero]
    at h
  ext i
  fin_cases i <;> assumption

theorem denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : denom g z ≠ 0 := by
  intro H
  have DET := (mem_glpos _).1 g.prop
  simp only [GeneralLinearGroup.val_det_apply] at DET
  obtain hg | hz : g 1 0 = 0 ∨ z.im = 0 := by simpa [num, denom] using congr_arg Complex.im H
  · simp only [hg, Complex.ofReal_zero, denom, zero_mul, zero_add, Complex.ofReal_eq_zero] at H
    simp only [Matrix.det_fin_two g.1.1, H, hg, mul_zero, sub_zero, lt_self_iff_false] at DET
  · exact z.prop.ne' hz

theorem normSq_denom_pos (g : GL(2, ℝ)⁺) (z : ℍ) : 0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero g z)

theorem normSq_denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gt (normSq_denom_pos g z)

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux' (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  num g z / denom g z

theorem smulAux'_im (g : GL(2, ℝ)⁺) (z : ℍ) :
    (smulAux' g z).im = det ↑ₘg * z.im / Complex.normSq (denom g z) := by
  simp only [smulAux', num, denom, Complex.div_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, coe_im, Complex.ofReal_im, coe_re, zero_mul, add_zero, Complex.add_re,
    Complex.mul_re, sub_zero, ← sub_div, g.1.1.det_fin_two]
  ring

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux (g : GL(2, ℝ)⁺) (z : ℍ) : ℍ :=
  mk (smulAux' g z) <| by
    rw [smulAux'_im]
    convert mul_pos ((mem_glpos _).1 g.prop)
        (div_pos z.im_pos (Complex.normSq_pos.mpr (denom_ne_zero g z))) using 1
    simp only [GeneralLinearGroup.val_det_apply]
    ring

theorem denom_cocycle (x y : GL(2, ℝ)⁺) (z : ℍ) :
    denom (x * y) z = denom x (smulAux y z) * denom y z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero]
  simp only [denom, Subgroup.coe_mul, Fin.isValue, Units.val_mul, mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Complex.ofReal_add, Complex.ofReal_mul, num]
  ring

theorem mul_smul' (x y : GL(2, ℝ)⁺) (z : ℍ) : smulAux (x * y) z = smulAux x (smulAux y z) := by
  ext1
  change _ / _ = (_ * (_ / _) + _) / _
  rw [denom_cocycle]
  field_simp [denom_ne_zero]
  simp only [num, Subgroup.coe_mul, Fin.isValue, Units.val_mul, mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Complex.ofReal_add, Complex.ofReal_mul, denom]
  ring

/-- The action of `GLPos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
instance : MulAction GL(2, ℝ)⁺ ℍ where
  smul := smulAux
  one_smul z := by
    ext1
    change _ / _ = _
    simp [num, denom]
  mul_smul := mul_smul'

instance SLAction {R : Type*} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.toGLPos.comp <| map (algebraMap R ℝ)

-- Porting note: in the statement, we used to have coercions `↑· : ℝ`
-- rather than `algebraMap R ℝ ·`.
theorem specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    g • z =
      mk
        (((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ)) /
          ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ)))
        (g • z).property :=
  rfl

variable (g : GL(2, ℝ)⁺) (z : ℍ)

@[simp]
theorem coe_smul : ↑(g • z) = num g z / denom g z :=
  rfl

@[simp]
theorem re_smul : (g • z).re = (num g z / denom g z).re :=
  rfl

theorem im_smul : (g • z).im = (num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_normSq : (g • z).im = det ↑ₘg * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z

theorem c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom g z) := by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by dsimp [c, d, denom, Complex.normSq]; ring

@[simp]
theorem neg_smul : -g • z = g • z := by
  ext1
  change _ / _ = _ / _
  field_simp [denom_ne_zero]
  simp only [num, denom, Complex.ofReal_neg, neg_mul, GLPos.coe_neg_GL, Units.val_neg, neg_apply]
  ring_nf

lemma denom_one : denom 1 z = 1 := by
  simp [denom]

section PosRealAction

instance posRealAction : MulAction { x : ℝ // 0 < x } ℍ where
  smul x z := mk ((x : ℝ) • (z : ℂ)) <| by simpa using mul_pos x.2 z.2
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul x y z := Subtype.ext <| mul_smul (x : ℝ) y (z : ℂ)

variable (x : { x : ℝ // 0 < x }) (z : ℍ)

@[simp]
theorem coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) :=
  rfl

@[simp]
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _

@[simp]
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _

end PosRealAction

section RealAddAction

instance : AddAction ℝ ℍ where
  vadd x z := mk (x + z) <| by simpa using z.im_pos
  zero_vadd _ := Subtype.ext <| by simp [HVAdd.hVAdd]
  add_vadd x y z := Subtype.ext <| by simp [HVAdd.hVAdd, add_assoc]

variable (x : ℝ) (z : ℍ)

@[simp]
theorem coe_vadd : ↑(x +ᵥ z) = (x + z : ℂ) :=
  rfl

@[simp]
theorem vadd_re : (x +ᵥ z).re = x + z.re :=
  rfl

@[simp]
theorem vadd_im : (x +ᵥ z).im = z.im :=
  zero_add _

end RealAddAction

/- these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/
theorem modular_S_smul (z : ℍ) : ModularGroup.S • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos := by
  rw [specialLinearGroup_apply]; simp [ModularGroup.S, neg_div, inv_neg, toGL]

theorem modular_T_zpow_smul (z : ℍ) (n : ℤ) : ModularGroup.T ^ n • z = (n : ℝ) +ᵥ z := by
  rw [UpperHalfPlane.ext_iff, coe_vadd, add_comm, specialLinearGroup_apply, coe_mk]
  simp [toGL, ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, algebraMap.coe_one, Complex.ofReal_one, one_mul, cons_val_one,
    head_cons, algebraMap.coe_zero, zero_mul, zero_add, div_one]

theorem modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : ℝ) +ᵥ z := by
  simpa only [Int.cast_one] using modular_T_zpow_smul z 1

theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v : ℝ), (g • · : ℍ → ℍ) = (v +ᵥ ·) ∘ (u • ·) := by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by
    simpa [toGL, specialLinearGroup_apply, add_mul]
  ring

theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : g 1 0 ≠ 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v w : ℝ),
      (g • · : ℍ → ℍ) =
        (w +ᵥ ·) ∘ (ModularGroup.S • · : ℍ → ℍ) ∘ (v +ᵥ · : ℍ → ℍ) ∘ (u • · : ℍ → ℍ) := by
  have h_denom := denom_ne_zero g
  induction' g using Matrix.SpecialLinearGroup.fin_two_induction with a b c d h
  replace hc : c ≠ 0 := by simpa using hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹ by
    simpa only [modular_S_smul, inv_neg, Function.comp_apply, coe_vadd, Complex.ofReal_mul,
      coe_pos_real_smul, Complex.real_smul, Complex.ofReal_div, coe_mk]
  replace hc : (c : ℂ) ≠ 0 := by norm_cast
  replace h_denom : ↑c * z + d ≠ 0 := by simpa using h_denom ⟨z, hz⟩
  have h_aux : (c : ℂ) * d + ↑c * ↑c * z ≠ 0 := by
    rw [mul_assoc, ← mul_add, add_comm]
    exact mul_ne_zero hc h_denom
  replace h : (a * d - b * c : ℂ) = (1 : ℂ) := by norm_cast
  field_simp
  linear_combination (-(z * (c : ℂ) ^ 2) - c * d) * h

end UpperHalfPlane

namespace ModularGroup -- results specific to `SL(2, ℤ)`

section ModularScalarTowers

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`. -/
@[coe]
def coe (g : SL(2, ℤ)) : GL(2, ℝ)⁺ := ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)

@[deprecated (since := "2024-11-19")] noncomputable alias coe' := coe

instance : Coe SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨coe⟩

@[simp]
theorem coe_apply_complex {g : SL(2, ℤ)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe g) i j = (Subtype.val g i j : ℂ) :=
  rfl

@[deprecated (since := "2024-11-19")] alias coe'_apply_complex := coe_apply_complex

@[simp]
theorem det_coe {g : SL(2, ℤ)} : det (Units.val <| Subtype.val <| coe g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated (since := "2024-11-19")] alias det_coe' := det_coe

lemma coe_one : coe 1 = 1 := by
  simp only [coe, _root_.map_one]

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
theorem sl_moeb (A : SL(2, ℤ)) (z : ℍ) : A • z = (A : GL(2, ℝ)⁺) • z :=
  rfl

@[simp high]
theorem SL_neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z := by
  simp only [coe_GLPos_neg, sl_moeb, coe_int_neg, neg_smul, coe]

theorem im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  simpa only [coe, coe_GLPos_coe_GL_coe_matrix, (g : SL(2, ℝ)).prop, one_mul] using
    z.im_smul_eq_div_normSq g

theorem denom_apply (g : SL(2, ℤ)) (z : ℍ) :
    denom g z = g 1 0 * z + g 1 1 := by
  simp [denom, coe]

@[simp]
lemma denom_S (z : ℍ) : denom S z = z := by
  simp only [S, denom_apply, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    cons_val_one, head_fin_const, Int.cast_one, one_mul, head_cons, Int.cast_zero, add_zero]

end SLModularAction

end ModularGroup
