/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The upper half plane

This file defines `UpperHalfPlane` to be the upper half plane in `ℂ`.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

@[expose] public section

noncomputable section

/-- The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace -/
@[ext]
structure UpperHalfPlane where
  /-- Canonical embedding of the upper half-plane into `ℂ`. -/
  protected coe : ℂ
  coe_im_pos : 0 < coe.im

@[inherit_doc] scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

open UpperHalfPlane

namespace UpperHalfPlane

attribute [coe] UpperHalfPlane.coe

instance : CoeOut ℍ ℂ := ⟨UpperHalfPlane.coe⟩

/-- Define I := √-1 as an element on the upper half plane. -/
def I : ℍ := ⟨Complex.I, zero_lt_one⟩

instance : Inhabited ℍ := ⟨.I⟩

@[simp, norm_cast] theorem coe_inj {a b : ℍ} : (a : ℂ) = b ↔ a = b := UpperHalfPlane.ext_iff.symm

@[deprecated (since := "2026-01-31")] alias ext_iff' := coe_inj

theorem coe_injective : Function.Injective UpperHalfPlane.coe := fun _ _ ↦ UpperHalfPlane.ext

instance canLift : CanLift ℂ ℍ ((↑) : ℍ → ℂ) fun z => 0 < z.im where
  prf z hz := ⟨⟨z, hz⟩, rfl⟩

protected theorem «forall» {P : ℍ → Prop} : (∀ z, P z) ↔ ∀ z hz, P ⟨z, hz⟩ :=
  ⟨fun h z hz ↦ h ⟨z, hz⟩, fun h z ↦ h z.1 z.2⟩

protected theorem «exists» {P : ℍ → Prop} : (∃ z, P z) ↔ ∃ z hz, P ⟨z, hz⟩ :=
  ⟨fun ⟨⟨z, hz⟩, hP⟩ ↦ ⟨z, hz, hP⟩, fun ⟨z, hz, hP⟩ ↦ ⟨⟨z, hz⟩, hP⟩⟩

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re

/-- Extensionality lemma in terms of `UpperHalfPlane.re` and `UpperHalfPlane.im`. -/
theorem ext_re_im {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im) : a = b :=
  UpperHalfPlane.ext <| Complex.ext hre him

@[deprecated (since := "2026-01-29")]
alias ext' := ext_re_im

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

theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  rfl

@[simp]
lemma I_im : I.im = 1 := rfl

@[simp]
lemma I_re : I.re = 0 := rfl

@[simp, norm_cast]
lemma coe_I : I = Complex.I := rfl

@[deprecated coe_mk (since := "2026-01-29")]
lemma coe_mk_subtype {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z :=
  rfl

theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.I : ℂ) = z :=
  Complex.re_add_im z

theorem im_pos (z : ℍ) : 0 < z.im := z.coe_im_pos

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero

end UpperHalfPlane

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `UpperHalfPlane.im`. -/
@[positivity UpperHalfPlane.im _]
meta def evalUpperHalfPlaneIm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(UpperHalfPlane.im $a) =>
    assertInstancesCommute
    pure (.positive q(@UpperHalfPlane.im_pos $a))
  | _, _, _ => throwError "not UpperHalfPlane.im"

/-- Extension for the `positivity` tactic: `UpperHalfPlane.coe`. -/
@[positivity UpperHalfPlane.coe _]
meta def evalUpperHalfPlaneCoe : PositivityExt where eval {u α} _zα _pα e := do
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
  simpa [neg_div] using div_pos z.im_pos (normSq_pos z)

lemma im_pnat_div_pos (n : ℕ) [NeZero n] (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  suffices 0 < n * z.im / Complex.normSq z by simpa [Complex.div_im, neg_div]
  positivity [NeZero.ne n, z.normSq_pos]

lemma ne_ofReal (z : ℍ) (x : ℝ) : (z : ℂ) ≠ x :=
  ne_of_apply_ne Complex.im <| by simp [im_ne_zero]

lemma ne_intCast (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n := mod_cast ne_ofReal z n

@[deprecated (since := "2026-01-29")] alias ne_int := ne_intCast

lemma ne_natCast (z : ℍ) (n : ℕ) : (z : ℂ) ≠ n := mod_cast ne_intCast z n

@[deprecated (since := "2026-01-29")] alias ne_nat := ne_natCast

section PosRealAction

instance posRealAction : MulAction {x : ℝ // 0 < x} ℍ where
  smul x z := mk ((x : ℝ) • (z : ℂ)) <| by simpa using mul_pos x.2 z.im_pos
  one_smul _ := UpperHalfPlane.ext <| one_smul _ _
  mul_smul x y z := UpperHalfPlane.ext <| mul_smul (x : ℝ) y (z : ℂ)

variable (x : {x : ℝ // 0 < x}) (z : ℍ)

@[simp]
theorem coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) :=
  rfl

@[simp]
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _

@[simp]
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _

theorem pos_real_smul_injective (z : ℍ) :
    Function.Injective fun x : {x : ℝ // 0 < x} ↦ x • z := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp_all [UpperHalfPlane.ext_iff, ne_zero]

end PosRealAction

section RealAddAction

instance : AddAction ℝ ℍ where
  vadd x z := mk (x + z) <| by simpa using z.im_pos
  zero_vadd _ := by simp [HVAdd.hVAdd]
  add_vadd x y z := by simp [HVAdd.hVAdd, add_assoc]

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

@[simp]
protected theorem vadd_right_cancel_iff {x y : ℝ} (z : ℍ) : x +ᵥ z = y +ᵥ z ↔ x = y := by
  simp [UpperHalfPlane.ext_iff]

protected theorem vadd_left_injective (z : ℍ) : Function.Injective fun x : ℝ ↦ x +ᵥ z := by
  simp [Function.Injective]

instance : Infinite ℍ :=
  .of_injective _ <| UpperHalfPlane.vadd_left_injective I

instance : Nontrivial ℍ := inferInstance

end RealAddAction

section upperHalfPlaneSet

/-- The upper half plane as a subset of `ℂ`.
This is convenient for taking derivatives of functions on the upper half plane. -/
abbrev upperHalfPlaneSet := {z : ℂ | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet

lemma isOpen_upperHalfPlaneSet : IsOpen ℍₒ := isOpen_lt continuous_const Complex.continuous_im

@[simp]
theorem range_coe : Set.range UpperHalfPlane.coe = ℍₒ := by
  ext; simp [UpperHalfPlane.exists]

end upperHalfPlaneSet

end UpperHalfPlane
