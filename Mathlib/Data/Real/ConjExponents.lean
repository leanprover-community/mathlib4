/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Holder
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Real conjugate exponents

This file defines Hölder triple and Hölder conjugate exponents in `ℝ` and `ℝ≥0`. Real numbers `p`,
`q` and `r` form a *Hölder triple* if `0 < p` and `0 < q` and `p⁻¹ + q⁻¹ = r⁻¹` (which of course
implies `0 < r`). We say `p` and `q` are *Hölder conjugate* if `p`, `q` and `1` are a Hölder triple.
In this case, `1 < p` and `1 < q`. This property shows up often in analysis, especially when dealing
with `L^p` spaces.

These notions mimic the same notions for extended nonnegative reals where `p q r : ℝ≥0∞` are allowed
to take the values `0` and `∞`.

## Main declarations

* `Real.HolderTriple`: Predicate for two real numbers to be a Hölder triple.
* `Real.HolderConjugate`: Predicate for two real numbers to be Hölder conjugate.
* `Real.conjExponent`: Conjugate exponent of a real number.
* `NNReal.HolderTriple`: Predicate for two nonnegative real numbers to be a Hölder triple.
* `NNReal.HolderConjugate`: Predicate for two nonnegative real numbers to be Hölder conjugate.
* `NNReal.conjExponent`: Conjugate exponent of a nonnegative real number.
* `ENNReal.conjExponent`: Conjugate exponent of an extended nonnegative real number.

## TODO

* Eradicate the `1 / p` spelling in lemmas.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Real

/-- Real numbers `p q r : ℝ` are said to be a **Hölder triple** if `p` and `q` are positive
and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
structure HolderTriple (p q r : ℝ) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/-- Real numbers `p q : ℝ` are **Hölder conjugate** if they are positive and satisfy the
equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `Real.HolderTriple p q 1`. This condition
shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `Real.holderConjugate_iff`. -/
abbrev HolderConjugate (p q : ℝ) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p / (p-1)`, so that `p⁻¹ + q⁻¹ = 1`. -/
def conjExponent (p : ℝ) : ℝ := p / (p - 1)

variable {a b p q r : ℝ}

namespace HolderTriple

lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

theorem pos : 0 < p := h.left_pos
theorem nonneg : 0 ≤ p := h.pos.le
theorem ne_zero : p ≠ 0 := h.pos.ne'
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
theorem pos' : 0 < r := inv_pos.mp <| h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/-- For `r`, instead of `p` -/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
theorem ne_zero' : r ≠ 0 := h.pos'.ne'
/-- For `r`, instead of `p` -/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/-- For `r`, instead of `p` -/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using h.inv_add_inv_eq_inv
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by simp [h.inv_add_inv_eq_inv]

protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := calc
  p⁻¹ = p⁻¹ + 0 := add_zero _ |>.symm
  _ < p⁻¹ + q⁻¹ := by gcongr; exact h.symm.inv_pos
  _ = r⁻¹ := h.inv_add_inv_eq_inv
lemma lt : r < p := by simpa using inv_strictAnti₀ h.inv_pos h.inv_lt_inv
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := sub_eq_of_eq_add h.inv_eq

lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by norm_num
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := ℝ) ▸ h.inv_add_inv_eq_inv

theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.lt
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

theorem conjugate_eq : q = p / (p - 1) := by
  convert inv_inv q ▸ congr($(h.symm.inv_sub_inv_eq_inv.symm)⁻¹) using 1
  field [h.ne_zero]

lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by simpa using congr(-$(h.one_sub_inv))

theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

theorem inv_add_inv_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos h.pos,
    ← ENNReal.ofReal_inv_of_pos h.symm.pos, ← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_eq_one]

end

lemma _root_.Real.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  refine ⟨fun h ↦ ⟨h.lt, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, h⟩
  have hp' := zero_lt_one.trans hp
  refine ⟨inv_one (G := ℝ) |>.symm ▸ h, hp', ?_⟩
  rw [← inv_lt_one₀ hp', ← sub_pos] at hp
  exact inv_pos.mp <| eq_sub_of_add_eq' h ▸ hp

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀ |>.mpr ha₁, by simp⟩

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) :=
  ⟨HolderConjugate.conjugate_eq, fun h ↦ holderConjugate_iff.mpr ⟨hp, by simp [field, h]⟩⟩

lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end Real

namespace NNReal

/-- Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p` and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
structure HolderTriple (p q r : ℝ≥0) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/-- Nonnegative real numbers `p q : ℝ≥0` are **Hölder conjugate** if they are positive and satisfy
the equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `NNReal.HolderTriple p q 1`. This
condition shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `NNReal.holderConjugate_iff`. -/
abbrev HolderConjugate (p q : ℝ≥0) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `p⁻¹ + q⁻¹ = 1`. -/
def conjExponent (p : ℝ≥0) : ℝ≥0 := p / (p - 1)

@[simp, norm_cast]
lemma holderTriple_coe_iff {p q r : ℝ≥0} :
    Real.HolderTriple (p : ℝ) (q : ℝ) (r : ℝ) ↔ HolderTriple p q r := by
  rw_mod_cast [Real.holderTriple_iff, holderTriple_iff]

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    Real.HolderConjugate (p : ℝ) (q : ℝ) ↔ HolderConjugate p q :=
  holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

variable {a b p q r : ℝ≥0}

namespace HolderTriple

lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

theorem pos : 0 < p := h.left_pos
theorem nonneg : 0 ≤ p := h.pos.le
theorem ne_zero : p ≠ 0 := h.pos.ne'
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
theorem pos' : 0 < r := inv_pos.mp <| h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/-- For `r`, instead of `p` -/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
theorem ne_zero' : r ≠ 0 := h.pos'.ne'
/-- For `r`, instead of `p` -/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/-- For `r`, instead of `p` -/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by exact_mod_cast h.coe.one_div_add_one_div
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by exact_mod_cast h.coe.inv_inv_add_inv

protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := h.coe.inv_lt_inv
lemma lt : r < p := h.coe.lt
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := by
  have := h.symm.inv_lt_inv.le
  exact_mod_cast h.coe.inv_sub_inv_eq_inv

lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by simpa using add_halves (1 : ℝ≥0)
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := ℝ≥0) ▸ h.inv_add_inv_eq_inv

theorem sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.lt
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

theorem conjugate_eq : q = p / (p - 1) := by
  have : ((1 : ℝ≥0) : ℝ) ≤ p := h.coe.lt.le
  exact_mod_cast NNReal.coe_sub this ▸ coe_one ▸ h.coe.conjugate_eq

lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

theorem mul_eq_add : p * q = p + q := by
  simpa [mul_add, add_mul, h.ne_zero, h.symm.ne_zero, add_comm q] using congr(p * $(h.inv_eq) * q)

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

lemma inv_add_inv_ennreal : (p⁻¹ + q⁻¹ : ℝ≥0∞) = 1 := by norm_cast; exact h.inv_add_inv_eq_one

end

lemma _root_.NNReal.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  rw [← holderConjugate_coe_iff, Real.holderConjugate_iff, ← coe_one]
  exact_mod_cast Iff.rfl

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀ |>.mpr ha₁, by simpa using add_tsub_cancel_of_le ha₁.le⟩

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) := by
  rw [← holderConjugate_coe_iff, Real.holderConjugate_iff_eq_conjExponent (by exact_mod_cast hp),
    ← coe_one, ← NNReal.coe_sub hp.le]
  exact_mod_cast Iff.rfl

lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end NNReal

protected lemma Real.HolderTriple.toNNReal {p q r : ℝ} (h : p.HolderTriple q r) :
    p.toNNReal.HolderTriple q.toNNReal r.toNNReal := by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']

protected lemma Real.HolderConjugate.toNNReal {p q : ℝ} (h : p.HolderConjugate q) :
    p.toNNReal.HolderConjugate q.toNNReal := by
  simpa using Real.HolderTriple.toNNReal h

namespace ENNReal

/-- The conjugate exponent of `p` is `q = 1 + (p - 1)⁻¹`, so that `p⁻¹ + q⁻¹ = 1`. -/
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := 1 + (p - 1)⁻¹

lemma coe_conjExponent {p : ℝ≥0} (hp : 1 < p) : p.conjExponent = conjExponent p := by
  rw [NNReal.conjExponent, conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]


variable {a b p q r : ℝ≥0∞}

@[simp, norm_cast]
lemma holderTriple_coe_iff {p q r : ℝ≥0} (hr : r ≠ 0) :
    HolderTriple (p : ℝ≥0∞) (q : ℝ≥0∞) (r : ℝ≥0∞) ↔ NNReal.HolderTriple p q r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [NNReal.holderTriple_iff]
    obtain ⟨hp, hq⟩ : p ≠ 0 ∧ q ≠ 0 := by
      constructor
      all_goals
        rintro rfl
        apply hr
        exact_mod_cast (coe_zero ▸ h).unique _ _ r 0
    exact ⟨by exact_mod_cast h.inv_add_inv_eq_inv, hp.bot_lt, hq.bot_lt⟩
  · rw [holderTriple_iff]
    have hp := h.ne_zero
    have hq := h.symm.ne_zero
    exact_mod_cast h.inv_add_inv_eq_inv

alias ⟨_, _root_.NNReal.HolderTriple.coe_ennreal⟩ := holderTriple_coe_iff

@[simp, norm_cast]
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    HolderConjugate (p : ℝ≥0∞) (q : ℝ≥0∞) ↔ NNReal.HolderConjugate p q :=
  holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

namespace HolderTriple

lemma _root_.Real.HolderTriple.ennrealOfReal {p q r : ℝ} (h : p.HolderTriple q r) :
    HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  simpa [holderTriple_iff, ofReal_inv_of_pos, h.pos, h.symm.pos, h.pos', ofReal_add, h.nonneg,
    h.symm.nonneg] using congr(ENNReal.ofReal $(h.inv_add_inv_eq_inv))

lemma _root_.Real.HolderConjugate.ennrealOfReal {p q : ℝ} (h : p.HolderConjugate q) :
    HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  simpa using Real.HolderTriple.ennrealOfReal h

lemma of_toReal (h : Real.HolderTriple p.toReal q.toReal r.toReal) : HolderTriple p q r := by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

variable (r) in
lemma toReal_iff (hp : 0 < p.toReal) (hq : 0 < q.toReal) :
    Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r := by
  refine ⟨of_toReal, fun h ↦ ⟨?_, hp, hq⟩⟩
  rw [toReal_pos_iff] at hp hq
  simpa [toReal_add, Finiteness.inv_ne_top, hp.1.ne', hq.1.ne']
    using congr(ENNReal.toReal $(h.inv_add_inv_eq_inv))

variable (r) in
lemma toReal (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r] :
    Real.HolderTriple p.toReal q.toReal r.toReal :=
  toReal_iff r hp hq |>.mpr ‹_›

lemma of_toNNReal (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal) :
    HolderTriple p q r :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe

variable (r) in
lemma toNNReal_iff (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal ↔ HolderTriple p q r := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

variable (r) in
lemma toNNReal (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r] :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal :=
  toNNReal_iff r hp hq |>.mpr ‹_›

end HolderTriple

namespace HolderConjugate

lemma of_toReal (h : p.toReal.HolderConjugate q.toReal) : p.HolderConjugate q := by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)

lemma toReal_iff (hp : 1 < p.toReal) :
    p.toReal.HolderConjugate q.toReal ↔ p.HolderConjugate q := by
  refine ⟨of_toReal, fun h ↦ ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
    refine ⟨pos q p, lt_top_iff_one_lt q p |>.mpr ?_⟩
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq

lemma toReal (hp : 1 < p.toReal) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal_iff hp |>.mpr ‹_›

lemma of_toNNReal (h : NNReal.HolderConjugate p.toNNReal q.toNNReal) :
    HolderConjugate p q :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe

lemma toNNReal_iff (hp : 1 < p.toNNReal) :
    NNReal.HolderConjugate p.toNNReal q.toNNReal ↔ HolderConjugate p q := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

lemma toNNReal (hp : 1 < p.toNNReal) [HolderConjugate p q] :
    NNReal.HolderConjugate p.toNNReal q.toNNReal :=
  toNNReal_iff hp |>.mpr ‹_›

protected lemma conjExponent {p : ℝ≥0∞} (hp : 1 ≤ p) : p.HolderConjugate (conjExponent p) := by
  have : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate, holderTriple_iff, conjExponent, add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := ℝ≥0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div, ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp), one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le, ← inv_eq_iff_eq_inv, div_eq_mul_inv, ENNReal.mul_inv, inv_inv,
        ENNReal.mul_sub, ENNReal.inv_mul_cancel, mul_one] <;> simp [*]

instance {p : ℝ≥0∞} [Fact (1 ≤ p)] : p.HolderConjugate (conjExponent p) := .conjExponent Fact.out

section

variable [h : HolderConjugate p q]

lemma conjExponent_eq : conjExponent p = q :=
  have : Fact (1 ≤ p) := ⟨one_le p q⟩
  unique p (conjExponent p) q

lemma conj_eq : q = 1 + (p - 1)⁻¹ := conjExponent_eq.symm

lemma mul_eq_add : p * q = p + q := by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
    ENNReal.inv_mul_cancel_right] using congr(p * $((inv_add_inv_eq_one p q).symm) * q)

lemma div_conj_eq_sub_one : p / q = p - 1 := by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq, ← ENNReal.add_div, ← h.mul_eq_add, mul_div_assoc,
    ENNReal.div_self (ne_zero q p) hq, mul_one]

end

protected lemma inv_inv (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa [inv_inv] using hab

lemma inv_one_sub_inv (ha : a ≤ 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  .inv_inv <| add_tsub_cancel_of_le ha

lemma inv_one_sub_inv' (ha : 1 ≤ a) : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)

lemma one_sub_inv_inv (ha : a ≤ 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ := (inv_one_sub_inv ha).symm

lemma top_one : HolderConjugate ∞ 1 := ⟨by simp⟩
lemma one_top : HolderConjugate 1 ∞ := ⟨by simp⟩

end HolderConjugate

lemma isConjExponent_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨(·.symm), (·.symm)⟩

lemma isConjExponent_iff_eq_conjExponent (hp : 1 ≤ p) : p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹ :=
  ⟨fun h ↦ h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

end ENNReal
