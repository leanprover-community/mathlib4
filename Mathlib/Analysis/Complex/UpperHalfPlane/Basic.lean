/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Analysis.Complex.Basic

/-!
# The upper half plane

This file defines `UpperHalfPlane` to be the upper half plane in `ℂ`.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

noncomputable section

/-- The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }

@[inherit_doc] scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

open UpperHalfPlane

namespace UpperHalfPlane

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

open Complex in
lemma pnat_div_upperHalfPlane_im_pos (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  simp only [div_im, neg_im, natCast_im, neg_zero, coe_re, zero_mul, zero_div, neg_re, natCast_re,
    coe_im, neg_mul, zero_sub, Left.neg_pos_iff, div_neg_iff, Left.neg_neg_iff, Nat.cast_pos,
    PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos, ne_eq]
  right
  simpa using ⟨z.2, ne_zero z⟩

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
  simpa [neg_div] using div_pos z.property (normSq_pos z)

lemma ne_nat (z : ℍ) : ∀ n : ℕ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

lemma ne_int (z : ℍ) : ∀ n : ℤ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

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

section upperHalfPlaneSet

/-- The upper half plane as a subset of `ℂ`. This is convenient for taking derivatives of functions
on the upper half plane. -/
abbrev upperHalfPlaneSet := {z : ℂ | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet

lemma isOpen_upperHalfPlaneSet : IsOpen ℍₒ := isOpen_lt continuous_const Complex.continuous_im

end upperHalfPlaneSet

end UpperHalfPlane
