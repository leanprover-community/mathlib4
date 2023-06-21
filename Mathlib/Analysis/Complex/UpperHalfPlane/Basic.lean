/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu

! This file was ported from Lean 3 source module analysis.complex.upper_half_plane.basic
! leanprover-community/mathlib commit 34d3797325d202bd7250431275bb871133cdb611
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Parity
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathbin.Analysis.Complex.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathbin.Tactic.LinearCombination

/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `GL_pos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/


noncomputable section

open Matrix Matrix.SpecialLinearGroup

open scoped Classical BigOperators MatrixGroups

attribute [local instance] Fintype.card_fin_even

/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

attribute [-instance] Matrix.GeneralLinearGroup.hasCoeToFun

local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

local notation:1024 "↑ₘ[" R "]" => @coe _ (Matrix (Fin 2) (Fin 2) R) _

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler λ α,
has_coe[has_coe] α exprℂ() -/
/-- The open upper half plane -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }
deriving «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler λ α,
  has_coe[has_coe] α exprℂ()»
#align upper_half_plane UpperHalfPlane

scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

namespace UpperHalfPlane

instance : Inhabited ℍ :=
  ⟨⟨Complex.I, by simp⟩⟩

instance canLift : CanLift ℂ ℍ coe fun z => 0 < z.im :=
  Subtype.canLift fun z => 0 < z.im
#align upper_half_plane.can_lift UpperHalfPlane.canLift

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im
#align upper_half_plane.im UpperHalfPlane.im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re
#align upper_half_plane.re UpperHalfPlane.re

/-- Constructor for `upper_half_plane`. It is useful if `⟨z, h⟩` makes Lean use a wrong
typeclass instance. -/
def mk (z : ℂ) (h : 0 < z.im) : ℍ :=
  ⟨z, h⟩
#align upper_half_plane.mk UpperHalfPlane.mk

@[simp]
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl
#align upper_half_plane.coe_im UpperHalfPlane.coe_im

@[simp]
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl
#align upper_half_plane.coe_re UpperHalfPlane.coe_re

@[simp]
theorem mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl
#align upper_half_plane.mk_re UpperHalfPlane.mk_re

@[simp]
theorem mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl
#align upper_half_plane.mk_im UpperHalfPlane.mk_im

@[simp]
theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl
#align upper_half_plane.coe_mk UpperHalfPlane.coe_mk

@[simp]
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  Subtype.eta z h
#align upper_half_plane.mk_coe UpperHalfPlane.mk_coe

theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.I : ℂ) = z :=
  Complex.re_add_im z
#align upper_half_plane.re_add_im UpperHalfPlane.re_add_im

theorem im_pos (z : ℍ) : 0 < z.im :=
  z.2
#align upper_half_plane.im_pos UpperHalfPlane.im_pos

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'
#align upper_half_plane.im_ne_zero UpperHalfPlane.im_ne_zero

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero
#align upper_half_plane.ne_zero UpperHalfPlane.ne_zero

theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by rw [Complex.normSq_pos];
  exact z.ne_zero
#align upper_half_plane.norm_sq_pos UpperHalfPlane.normSq_pos

theorem normSq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (normSq_pos z).ne'
#align upper_half_plane.norm_sq_ne_zero UpperHalfPlane.normSq_ne_zero

theorem im_inv_neg_coe_pos (z : ℍ) : 0 < (-z : ℂ)⁻¹.im := by
  simpa using div_pos z.property (norm_sq_pos z)
#align upper_half_plane.im_inv_neg_coe_pos UpperHalfPlane.im_inv_neg_coe_pos

/-- Numerator of the formula for a fractional linear transformation -/
@[simp]
def num (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 0 0 : ℝ) * z + (↑ₘg 0 1 : ℝ)
#align upper_half_plane.num UpperHalfPlane.num

/-- Denominator of the formula for a fractional linear transformation -/
@[simp]
def denom (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 1 0 : ℝ) * z + (↑ₘg 1 1 : ℝ)
#align upper_half_plane.denom UpperHalfPlane.denom

theorem linear_ne_zero (cd : Fin 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 :=
  by
  contrapose! h
  have : cd 0 = 0 :=
    by
    -- we will need this twice
    apply_fun Complex.im at h 
    simpa only [z.im_ne_zero, Complex.add_im, add_zero, coe_im, MulZeroClass.zero_mul, or_false_iff,
      Complex.ofReal_im, Complex.zero_im, Complex.mul_im, mul_eq_zero] using h
  simp only [this, MulZeroClass.zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero] at
    h 
  ext i
  fin_cases i <;> assumption
#align upper_half_plane.linear_ne_zero UpperHalfPlane.linear_ne_zero

theorem denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : denom g z ≠ 0 :=
  by
  intro H
  have DET := (mem_GL_pos _).1 g.prop
  have hz := z.prop
  simp only [general_linear_group.coe_det_apply] at DET 
  have H1 : (↑ₘg 1 0 : ℝ) = 0 ∨ z.im = 0 := by simpa using congr_arg Complex.im H
  cases H1
  · simp only [H1, Complex.ofReal_zero, denom, coe_fn_eq_coe, MulZeroClass.zero_mul, zero_add,
      Complex.ofReal_eq_zero] at H 
    rw [← coe_coe, Matrix.det_fin_two (↑g : Matrix (Fin 2) (Fin 2) ℝ)] at DET 
    simp only [coe_coe, H, H1, MulZeroClass.mul_zero, sub_zero, lt_self_iff_false] at DET 
    exact DET
  · change z.im > 0 at hz 
    linarith
#align upper_half_plane.denom_ne_zero UpperHalfPlane.denom_ne_zero

theorem normSq_denom_pos (g : GL(2, ℝ)⁺) (z : ℍ) : 0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero g z)
#align upper_half_plane.norm_sq_denom_pos UpperHalfPlane.normSq_denom_pos

theorem normSq_denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gt (normSq_denom_pos g z)
#align upper_half_plane.norm_sq_denom_ne_zero UpperHalfPlane.normSq_denom_ne_zero

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux' (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  num g z / denom g z
#align upper_half_plane.smul_aux' UpperHalfPlane.smulAux'

theorem smulAux'_im (g : GL(2, ℝ)⁺) (z : ℍ) :
    (smulAux' g z).im = det ↑ₘg * z.im / (denom g z).normSq :=
  by
  rw [smul_aux', Complex.div_im]
  set NsqBot := (denom g z).normSq
  have : NsqBot ≠ 0 := by simp only [denom_ne_zero g z, map_eq_zero, Ne.def, not_false_iff]
  field_simp [smul_aux', -coe_coe]
  rw [Matrix.det_fin_two ↑ₘg]
  ring
#align upper_half_plane.smul_aux'_im UpperHalfPlane.smulAux'_im

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux (g : GL(2, ℝ)⁺) (z : ℍ) : ℍ :=
  ⟨smulAux' g z, by
    rw [smul_aux'_im]
    convert
      mul_pos ((mem_GL_pos _).1 g.prop)
        (div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z)))
    simp only [general_linear_group.coe_det_apply, coe_coe]
    ring⟩
#align upper_half_plane.smul_aux UpperHalfPlane.smulAux

theorem denom_cocycle (x y : GL(2, ℝ)⁺) (z : ℍ) :
    denom (x * y) z = denom x (smulAux y z) * denom y z :=
  by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero, -denom, -Num]
  simp only [Matrix.mul, dot_product, Fin.sum_univ_succ, denom, Num, coe_coe, Subgroup.coe_mul,
    general_linear_group.coe_mul, Fintype.univ_ofSubsingleton, Fin.mk_zero, Finset.sum_singleton,
    Fin.succ_zero_eq_one, Complex.ofReal_add, Complex.ofReal_mul]
  ring
#align upper_half_plane.denom_cocycle UpperHalfPlane.denom_cocycle

theorem mul_smul' (x y : GL(2, ℝ)⁺) (z : ℍ) : smulAux (x * y) z = smulAux x (smulAux y z) :=
  by
  ext1
  change _ / _ = (_ * (_ / _) + _) * _
  rw [denom_cocycle]
  field_simp [denom_ne_zero, -denom, -Num]
  simp only [Matrix.mul, dot_product, Fin.sum_univ_succ, Num, denom, coe_coe, Subgroup.coe_mul,
    general_linear_group.coe_mul, Fintype.univ_ofSubsingleton, Fin.mk_zero, Finset.sum_singleton,
    Fin.succ_zero_eq_one, Complex.ofReal_add, Complex.ofReal_mul]
  ring
#align upper_half_plane.mul_smul' UpperHalfPlane.mul_smul'

/-- The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
instance : MulAction GL(2, ℝ)⁺ ℍ where
  smul := smulAux
  one_smul z := by
    ext1; change _ / _ = _
    simp [coeFn_coe_base']
  mul_smul := mul_smul'

section ModularScalarTowers

variable (Γ : Subgroup (SpecialLinearGroup (Fin 2) ℤ))

instance sLAction {R : Type _} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.toGLPos.comp <| map (algebraMap R ℝ)
#align upper_half_plane.SL_action UpperHalfPlane.sLAction

instance : Coe SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun g => ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)⟩

instance sLOnGLPos : SMul SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩
#align upper_half_plane.SL_on_GL_pos UpperHalfPlane.sLOnGLPos

theorem sLOnGLPos_smul_apply (s : SL(2, ℤ)) (g : GL(2, ℝ)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl
#align upper_half_plane.SL_on_GL_pos_smul_apply UpperHalfPlane.sLOnGLPos_smul_apply

instance SL_to_GL_tower : IsScalarTower SL(2, ℤ) GL(2, ℝ)⁺ ℍ
    where smul_assoc := by intro s g z; simp only [SL_on_GL_pos_smul_apply, coe_coe];
    apply mul_smul'
#align upper_half_plane.SL_to_GL_tower UpperHalfPlane.SL_to_GL_tower

instance subgroupGLPos : SMul Γ GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩
#align upper_half_plane.subgroup_GL_pos UpperHalfPlane.subgroupGLPos

theorem subgroup_on_gLPos_smul_apply (s : Γ) (g : GL(2, ℝ)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl
#align upper_half_plane.subgroup_on_GL_pos_smul_apply UpperHalfPlane.subgroup_on_gLPos_smul_apply

instance subgroup_on_gLPos : IsScalarTower Γ GL(2, ℝ)⁺ ℍ
    where smul_assoc := by intro s g z; simp only [subgroup_on_GL_pos_smul_apply, coe_coe];
    apply mul_smul'
#align upper_half_plane.subgroup_on_GL_pos UpperHalfPlane.subgroup_on_gLPos

instance subgroupSL : SMul Γ SL(2, ℤ) :=
  ⟨fun s g => s * g⟩
#align upper_half_plane.subgroup_SL UpperHalfPlane.subgroupSL

theorem subgroup_on_SL_apply (s : Γ) (g : SL(2, ℤ)) (z : ℍ) :
    (s • g) • z = ((s : SL(2, ℤ)) * g) • z :=
  rfl
#align upper_half_plane.subgroup_on_SL_apply UpperHalfPlane.subgroup_on_SL_apply

instance subgroup_to_SL_tower : IsScalarTower Γ SL(2, ℤ) ℍ
    where smul_assoc s g z := by rw [subgroup_on_SL_apply]; apply MulAction.mul_smul
#align upper_half_plane.subgroup_to_SL_tower UpperHalfPlane.subgroup_to_SL_tower

end ModularScalarTowers

theorem specialLinearGroup_apply {R : Type _} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    g • z =
      mk
        ((((↑(↑ₘ[R] g 0 0) : ℝ) : ℂ) * z + ((↑(↑ₘ[R] g 0 1) : ℝ) : ℂ)) /
          (((↑(↑ₘ[R] g 1 0) : ℝ) : ℂ) * z + ((↑(↑ₘ[R] g 1 1) : ℝ) : ℂ)))
        (g • z).property :=
  rfl
#align upper_half_plane.special_linear_group_apply UpperHalfPlane.specialLinearGroup_apply

@[simp]
theorem coe_smul (g : GL(2, ℝ)⁺) (z : ℍ) : ↑(g • z) = num g z / denom g z :=
  rfl
#align upper_half_plane.coe_smul UpperHalfPlane.coe_smul

@[simp]
theorem re_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).re = (num g z / denom g z).re :=
  rfl
#align upper_half_plane.re_smul UpperHalfPlane.re_smul

theorem im_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).im = (num g z / denom g z).im :=
  rfl
#align upper_half_plane.im_smul UpperHalfPlane.im_smul

theorem im_smul_eq_div_normSq (g : GL(2, ℝ)⁺) (z : ℍ) :
    (g • z).im = det ↑ₘg * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z
#align upper_half_plane.im_smul_eq_div_norm_sq UpperHalfPlane.im_smul_eq_div_normSq

@[simp]
theorem neg_smul (g : GL(2, ℝ)⁺) (z : ℍ) : -g • z = g • z :=
  by
  ext1
  change _ / _ = _ / _
  field_simp [denom_ne_zero, -denom, -Num]
  simp only [Num, denom, coe_coe, Complex.ofReal_neg, neg_mul, GL_pos.coe_neg_GL, Units.val_neg,
    Pi.neg_apply]
  ring_nf
#align upper_half_plane.neg_smul UpperHalfPlane.neg_smul

section SLModularAction

variable (g : SL(2, ℤ)) (z : ℍ) (Γ : Subgroup SL(2, ℤ))

@[simp]
theorem sl_moeb (A : SL(2, ℤ)) (z : ℍ) : A • z = (A : GL(2, ℝ)⁺) • z :=
  rfl
#align upper_half_plane.sl_moeb UpperHalfPlane.sl_moeb

theorem subgroup_moeb (A : Γ) (z : ℍ) : A • z = (A : GL(2, ℝ)⁺) • z :=
  rfl
#align upper_half_plane.subgroup_moeb UpperHalfPlane.subgroup_moeb

@[simp]
theorem subgroup_to_sl_moeb (A : Γ) (z : ℍ) : A • z = (A : SL(2, ℤ)) • z :=
  rfl
#align upper_half_plane.subgroup_to_sl_moeb UpperHalfPlane.subgroup_to_sl_moeb

@[simp]
theorem SL_neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z := by
  simp only [coe_GL_pos_neg, sl_moeb, coe_coe, coe_int_neg, neg_smul]
#align upper_half_plane.SL_neg_smul UpperHalfPlane.SL_neg_smul

theorem c_mul_im_sq_le_normSq_denom (z : ℍ) (g : SL(2, ℝ)) :
    ((↑ₘg 1 0 : ℝ) * z.im) ^ 2 ≤ Complex.normSq (denom g z) :=
  by
  let c := (↑ₘg 1 0 : ℝ)
  let d := (↑ₘg 1 1 : ℝ)
  calc
    (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [Complex.normSq] <;> ring
#align upper_half_plane.c_mul_im_sq_le_norm_sq_denom UpperHalfPlane.c_mul_im_sq_le_normSq_denom

theorem SpecialLinearGroup.im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) :=
  by
  convert im_smul_eq_div_norm_sq g z
  simp only [coe_coe, general_linear_group.coe_det_apply, coe_GL_pos_coe_GL_coe_matrix,
    Int.coe_castRingHom, (g : SL(2, ℝ)).Prop, one_mul]
#align upper_half_plane.special_linear_group.im_smul_eq_div_norm_sq UpperHalfPlane.SpecialLinearGroup.im_smul_eq_div_normSq

theorem denom_apply (g : SL(2, ℤ)) (z : ℍ) :
    denom g z = (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * z + (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  simp
#align upper_half_plane.denom_apply UpperHalfPlane.denom_apply

end SLModularAction

section PosRealAction

instance posRealAction : MulAction { x : ℝ // 0 < x } ℍ
    where
  smul x z := mk ((x : ℝ) • z) <| by simpa using mul_pos x.2 z.2
  one_smul z := Subtype.ext <| one_smul _ _
  mul_smul x y z := Subtype.ext <| mul_smul (x : ℝ) y (z : ℂ)
#align upper_half_plane.pos_real_action UpperHalfPlane.posRealAction

variable (x : { x : ℝ // 0 < x }) (z : ℍ)

@[simp]
theorem coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) :=
  rfl
#align upper_half_plane.coe_pos_real_smul UpperHalfPlane.coe_pos_real_smul

@[simp]
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _
#align upper_half_plane.pos_real_im UpperHalfPlane.pos_real_im

@[simp]
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _
#align upper_half_plane.pos_real_re UpperHalfPlane.pos_real_re

end PosRealAction

section RealAddAction

instance : AddAction ℝ ℍ
    where
  vadd x z := mk (x + z) <| by simpa using z.im_pos
  zero_vadd z := Subtype.ext <| by simp
  add_vadd x y z := Subtype.ext <| by simp [add_assoc]

variable (x : ℝ) (z : ℍ)

@[simp]
theorem coe_vadd : ↑(x +ᵥ z) = (x + z : ℂ) :=
  rfl
#align upper_half_plane.coe_vadd UpperHalfPlane.coe_vadd

@[simp]
theorem vadd_re : (x +ᵥ z).re = x + z.re :=
  rfl
#align upper_half_plane.vadd_re UpperHalfPlane.vadd_re

@[simp]
theorem vadd_im : (x +ᵥ z).im = z.im :=
  zero_add _
#align upper_half_plane.vadd_im UpperHalfPlane.vadd_im

end RealAddAction

/- these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/
theorem modular_s_smul (z : ℍ) : ModularGroup.S • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos := by
  rw [special_linear_group_apply]; simp [ModularGroup.S, neg_div, inv_neg]
#align upper_half_plane.modular_S_smul UpperHalfPlane.modular_s_smul

theorem modular_t_zpow_smul (z : ℍ) (n : ℤ) : ModularGroup.T ^ n • z = (n : ℝ) +ᵥ z :=
  by
  rw [← Subtype.coe_inj, coe_vadd, add_comm, special_linear_group_apply, coe_mk,
    ModularGroup.coe_T_zpow]
  simp only [of_apply, cons_val_zero, algebraMap.coe_one, Complex.ofReal_one, one_mul, cons_val_one,
    head_cons, algebraMap.coe_zero, MulZeroClass.zero_mul, zero_add, div_one]
#align upper_half_plane.modular_T_zpow_smul UpperHalfPlane.modular_t_zpow_smul

theorem modular_t_smul (z : ℍ) : ModularGroup.T • z = (1 : ℝ) +ᵥ z := by
  simpa only [algebraMap.coe_one] using modular_T_zpow_smul z 1
#align upper_half_plane.modular_T_smul UpperHalfPlane.modular_t_smul

theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : ↑ₘ[ℝ] g 1 0 = 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v : ℝ), ((· • ·) g : ℍ → ℍ) = (fun z => v +ᵥ z) ∘ fun z => u • z :=
  by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine' ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, _⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by rw [special_linear_group_apply];
    simpa [add_mul]
  ring
#align upper_half_plane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero

theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : ↑ₘ[ℝ] g 1 0 ≠ 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v w : ℝ),
      ((· • ·) g : ℍ → ℍ) =
        ((· +ᵥ ·) w : ℍ → ℍ) ∘
          ((· • ·) ModularGroup.S : ℍ → ℍ) ∘ ((· +ᵥ ·) v : ℍ → ℍ) ∘ ((· • ·) u : ℍ → ℍ) :=
  by
  have h_denom := denom_ne_zero g
  induction' g using Matrix.SpecialLinearGroup.fin_two_induction with a b c d h
  replace hc : c ≠ 0; · simpa using hc
  refine' ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, _⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹
    by
    rw [special_linear_group_apply]
    simpa only [inv_neg, modular_S_smul, Subtype.coe_mk, coe_vadd, Complex.ofReal_mul,
      coe_pos_real_smul, Complex.real_smul, Function.comp_apply, Complex.ofReal_div]
  replace hc : (c : ℂ) ≠ 0; · norm_cast; assumption
  replace h_denom : ↑c * z + d ≠ 0; · simpa using h_denom ⟨z, hz⟩
  have h_aux : (c : ℂ) * d + ↑c * ↑c * z ≠ 0 := by rw [mul_assoc, ← mul_add, add_comm];
    exact mul_ne_zero hc h_denom
  replace h : (a * d - b * c : ℂ) = (1 : ℂ); · norm_cast; assumption
  field_simp
  linear_combination (-(z * ↑c ^ 2) - ↑c * ↑d) * h
#align upper_half_plane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero

end UpperHalfPlane

