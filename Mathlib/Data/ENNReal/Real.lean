/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Inv

#align_import data.real.ennreal from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

# Main theorems

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

open Set NNReal ENNReal

namespace ENNReal

section Real

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl
#align ennreal.to_real_add ENNReal.toReal_add

theorem toReal_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞) :
    (a - b).toReal = a.toReal - b.toReal := by
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  simp only [← ENNReal.coe_sub, ENNReal.coe_toReal, NNReal.coe_sub (ENNReal.coe_le_coe.mp h)]
#align ennreal.to_real_sub_of_le ENNReal.toReal_sub_of_le

theorem le_toReal_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _
#align ennreal.le_to_real_sub ENNReal.le_toReal_sub

theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, top_toReal, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, top_toReal, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)
#align ennreal.to_real_add_le ENNReal.toReal_add_le

theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_inj,
    Real.toNNReal_add hp hq]
#align ennreal.of_real_add ENNReal.ofReal_add

theorem ofReal_add_le {p q : ℝ} : ENNReal.ofReal (p + q) ≤ ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le
#align ennreal.of_real_add_le ENNReal.ofReal_add_le

@[simp]
theorem toReal_le_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
#align ennreal.to_real_le_to_real ENNReal.toReal_le_toReal

@[gcongr]
theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h
#align ennreal.to_real_mono ENNReal.toReal_mono

-- Porting note (#10756): new lemma
theorem toReal_mono' (h : a ≤ b) (ht : b = ∞ → a = ∞) : a.toReal ≤ b.toReal := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]
theorem toReal_lt_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
#align ennreal.to_real_lt_to_real ENNReal.toReal_lt_toReal

@[gcongr]
theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h
#align ennreal.to_real_strict_mono ENNReal.toReal_strict_mono

@[gcongr]
theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal :=
  toReal_mono hb h
#align ennreal.to_nnreal_mono ENNReal.toNNReal_mono

-- Porting note (#10756): new lemma
/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

-- Porting note (#10756): new lemma
/-- If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add (hle : a ≤ b + c) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    a.toReal ≤ b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)

@[simp]
theorem toNNReal_le_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal ≤ b.toNNReal ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩
#align ennreal.to_nnreal_le_to_nnreal ENNReal.toNNReal_le_toNNReal

theorem toNNReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]
#align ennreal.to_nnreal_strict_mono ENNReal.toNNReal_strict_mono

@[simp]
theorem toNNReal_lt_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩
#align ennreal.to_nnreal_lt_to_nnreal ENNReal.toNNReal_lt_toNNReal

theorem toReal_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim
    (fun h => by simp only [h, (ENNReal.toReal_le_toReal hr hp).2 h, max_eq_right]) fun h => by
    simp only [h, (ENNReal.toReal_le_toReal hp hr).2 h, max_eq_left]
#align ennreal.to_real_max ENNReal.toReal_max

theorem toReal_min {a b : ℝ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim (fun h => by simp only [h, (ENNReal.toReal_le_toReal hr hp).2 h, min_eq_left])
    fun h => by simp only [h, (ENNReal.toReal_le_toReal hp hr).2 h, min_eq_right]
#align ennreal.to_real_min ENNReal.toReal_min

theorem toReal_sup {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).toReal = a.toReal ⊔ b.toReal :=
  toReal_max
#align ennreal.to_real_sup ENNReal.toReal_sup

theorem toReal_inf {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).toReal = a.toReal ⊓ b.toReal :=
  toReal_min
#align ennreal.to_real_inf ENNReal.toReal_inf

theorem toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞ := by
  induction a <;> simp
#align ennreal.to_nnreal_pos_iff ENNReal.toNNReal_pos_iff

theorem toNNReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNNReal :=
  toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩
#align ennreal.to_nnreal_pos ENNReal.toNNReal_pos

theorem toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  NNReal.coe_pos.trans toNNReal_pos_iff
#align ennreal.to_real_pos_iff ENNReal.toReal_pos_iff

theorem toReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toReal :=
  toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩
#align ennreal.to_real_pos ENNReal.toReal_pos

@[gcongr]
theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]
#align ennreal.of_real_le_of_real ENNReal.ofReal_le_ofReal

theorem ofReal_le_of_le_toReal {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ENNReal.toReal b) :
    ENNReal.ofReal a ≤ b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le
#align ennreal.of_real_le_of_le_to_real ENNReal.ofReal_le_of_le_toReal

@[simp]
theorem ofReal_le_ofReal_iff {p q : ℝ} (h : 0 ≤ q) :
    ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_le_coe, Real.toNNReal_le_toNNReal_iff h]
#align ennreal.of_real_le_of_real_iff ENNReal.ofReal_le_ofReal_iff

lemma ofReal_le_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p ≤ .ofReal q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

lemma ofReal_lt_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]
theorem ofReal_eq_ofReal_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_inj, Real.toNNReal_eq_toNNReal_iff hp hq]
#align ennreal.of_real_eq_of_real_iff ENNReal.ofReal_eq_ofReal_iff

@[simp]
theorem ofReal_lt_ofReal_iff {p q : ℝ} (h : 0 < q) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff h]
#align ennreal.of_real_lt_of_real_iff ENNReal.ofReal_lt_ofReal_iff

theorem ofReal_lt_ofReal_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]
#align ennreal.of_real_lt_of_real_iff_of_nonneg ENNReal.ofReal_lt_ofReal_iff_of_nonneg

@[simp]
theorem ofReal_pos {p : ℝ} : 0 < ENNReal.ofReal p ↔ 0 < p := by simp [ENNReal.ofReal]
#align ennreal.of_real_pos ENNReal.ofReal_pos

@[simp]
theorem ofReal_eq_zero {p : ℝ} : ENNReal.ofReal p = 0 ↔ p ≤ 0 := by simp [ENNReal.ofReal]
#align ennreal.of_real_eq_zero ENNReal.ofReal_eq_zero

@[simp]
theorem zero_eq_ofReal {p : ℝ} : 0 = ENNReal.ofReal p ↔ p ≤ 0 :=
  eq_comm.trans ofReal_eq_zero
#align ennreal.zero_eq_of_real ENNReal.zero_eq_ofReal

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero
#align ennreal.of_real_of_nonpos ENNReal.ofReal_of_nonpos

@[simp]
lemma ofReal_lt_natCast {p : ℝ} {n : ℕ} (hn : n ≠ 0) : ENNReal.ofReal p < n ↔ p < n := by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[deprecated (since := "2024-04-17")]
alias ofReal_lt_nat_cast := ofReal_lt_natCast

@[simp]
lemma ofReal_lt_one {p : ℝ} : ENNReal.ofReal p < 1 ↔ p < 1 := by
  exact mod_cast ofReal_lt_natCast one_ne_zero

@[simp]
lemma ofReal_lt_ofNat {p : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal p < no_index (OfNat.ofNat n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_natCast (NeZero.ne n)

@[simp]
lemma natCast_le_ofReal {n : ℕ} {p : ℝ} (hn : n ≠ 0) : n ≤ ENNReal.ofReal p ↔ n ≤ p := by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[deprecated (since := "2024-04-17")]
alias nat_cast_le_ofReal := natCast_le_ofReal

@[simp]
lemma one_le_ofReal {p : ℝ} : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p := by
  exact mod_cast natCast_le_ofReal one_ne_zero

@[simp]
lemma ofNat_le_ofReal {n : ℕ} [n.AtLeastTwo] {p : ℝ} :
    no_index (OfNat.ofNat n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p :=
  natCast_le_ofReal (NeZero.ne n)

@[simp]
lemma ofReal_le_natCast {r : ℝ} {n : ℕ} : ENNReal.ofReal r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Real.toNNReal_le_natCast

@[deprecated (since := "2024-04-17")]
alias ofReal_le_nat_cast := ofReal_le_natCast

@[simp]
lemma ofReal_le_one {r : ℝ} : ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
lemma ofReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r ≤ no_index (OfNat.ofNat n) ↔ r ≤ OfNat.ofNat n :=
  ofReal_le_natCast

@[simp]
lemma natCast_lt_ofReal {n : ℕ} {r : ℝ} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.natCast_lt_toNNReal

@[deprecated (since := "2024-04-17")]
alias nat_cast_lt_ofReal := natCast_lt_ofReal

@[simp]
lemma one_lt_ofReal {r : ℝ} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
lemma ofNat_lt_ofReal {n : ℕ} [n.AtLeastTwo] {r : ℝ} :
    no_index (OfNat.ofNat n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  natCast_lt_ofReal

@[simp]
lemma ofReal_eq_natCast {r : ℝ} {n : ℕ} (h : n ≠ 0) : ENNReal.ofReal r = n ↔ r = n :=
  ENNReal.coe_inj.trans <| Real.toNNReal_eq_natCast h

@[deprecated (since := "2024-04-17")]
alias ofReal_eq_nat_cast := ofReal_eq_natCast

@[simp]
lemma ofReal_eq_one {r : ℝ} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]
lemma ofReal_eq_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r = no_index (OfNat.ofNat n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_natCast (NeZero.ne n)

theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq, sub_add_cancel]
#align ennreal.of_real_sub ENNReal.ofReal_sub

theorem ofReal_le_iff_le_toReal {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
    ENNReal.ofReal a ≤ b ↔ a ≤ ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe
#align ennreal.of_real_le_iff_le_to_real ENNReal.ofReal_le_iff_le_toReal

theorem ofReal_lt_iff_lt_toReal {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    ENNReal.ofReal a < b ↔ a < ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha
#align ennreal.of_real_lt_iff_lt_to_real ENNReal.ofReal_lt_iff_lt_toReal

theorem ofReal_lt_coe_iff {a : ℝ} {b : ℝ≥0} (ha : 0 ≤ a) : ENNReal.ofReal a < b ↔ a < b :=
  (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans <| by rw [coe_toReal]

theorem le_ofReal_iff_toReal_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ ENNReal.ofReal b ↔ ENNReal.toReal a ≤ b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb
#align ennreal.le_of_real_iff_to_real_le ENNReal.le_ofReal_iff_toReal_le

theorem toReal_le_of_le_ofReal {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ENNReal.ofReal b) :
    ENNReal.toReal a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h
#align ennreal.to_real_le_of_le_of_real ENNReal.toReal_le_of_le_ofReal

theorem lt_ofReal_iff_toReal_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
    a < ENNReal.ofReal b ↔ ENNReal.toReal a < b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt
#align ennreal.lt_of_real_iff_to_real_lt ENNReal.lt_ofReal_iff_toReal_lt

theorem toReal_lt_of_lt_ofReal {b : ℝ} (h : a < ENNReal.ofReal b) : ENNReal.toReal a < b :=
  (lt_ofReal_iff_toReal_lt h.ne_top).1 h

theorem ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]
#align ennreal.of_real_mul ENNReal.ofReal_mul

theorem ofReal_mul' {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm, ofReal_mul hq, mul_comm]
#align ennreal.of_real_mul' ENNReal.ofReal_mul'

theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp, ← coe_pow, ← ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]
#align ennreal.of_real_pow ENNReal.ofReal_pow

theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]
#align ennreal.of_real_nsmul ENNReal.ofReal_nsmul

theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]
#align ennreal.of_real_inv_of_pos ENNReal.ofReal_inv_of_pos

theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy.le), ofReal_inv_of_pos hy]
#align ennreal.of_real_div_of_pos ENNReal.ofReal_div_of_pos

@[simp]
theorem toNNReal_mul {a b : ℝ≥0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal :=
  WithTop.untop'_zero_mul a b
#align ennreal.to_nnreal_mul ENNReal.toNNReal_mul

theorem toNNReal_mul_top (a : ℝ≥0∞) : ENNReal.toNNReal (a * ∞) = 0 := by simp
#align ennreal.to_nnreal_mul_top ENNReal.toNNReal_mul_top

theorem toNNReal_top_mul (a : ℝ≥0∞) : ENNReal.toNNReal (∞ * a) = 0 := by simp
#align ennreal.to_nnreal_top_mul ENNReal.toNNReal_top_mul

@[simp]
theorem smul_toNNReal (a : ℝ≥0) (b : ℝ≥0∞) : (a • b).toNNReal = a * b.toNNReal := by
  change ((a : ℝ≥0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
#align ennreal.smul_to_nnreal ENNReal.smul_toNNReal

-- Porting note (#11215): TODO: upgrade to `→*₀`
/-- `ENNReal.toNNReal` as a `MonoidHom`. -/
def toNNRealHom : ℝ≥0∞ →* ℝ≥0 where
  toFun := ENNReal.toNNReal
  map_one' := toNNReal_coe
  map_mul' _ _ := toNNReal_mul
#align ennreal.to_nnreal_hom ENNReal.toNNRealHom

@[simp]
theorem toNNReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toNNReal = a.toNNReal ^ n :=
  toNNRealHom.map_pow a n
#align ennreal.to_nnreal_pow ENNReal.toNNReal_pow

@[simp]
theorem toNNReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i ∈ s, f i).toNNReal = ∏ i ∈ s, (f i).toNNReal :=
  map_prod toNNRealHom _ _
#align ennreal.to_nnreal_prod ENNReal.toNNReal_prod

-- Porting note (#11215): TODO: upgrade to `→*₀`
/-- `ENNReal.toReal` as a `MonoidHom`. -/
def toRealHom : ℝ≥0∞ →* ℝ :=
  (NNReal.toRealHom : ℝ≥0 →* ℝ).comp toNNRealHom
#align ennreal.to_real_hom ENNReal.toRealHom

@[simp]
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b
#align ennreal.to_real_mul ENNReal.toReal_mul

theorem toReal_nsmul (a : ℝ≥0∞) (n : ℕ) : (n • a).toReal = n • a.toReal := by simp

@[simp]
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n
#align ennreal.to_real_pow ENNReal.toReal_pow

@[simp]
theorem toReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i ∈ s, f i).toReal = ∏ i ∈ s, (f i).toReal :=
  map_prod toRealHom _ _
#align ennreal.to_real_prod ENNReal.toReal_prod

theorem toReal_ofReal_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h]
#align ennreal.to_real_of_real_mul ENNReal.toReal_ofReal_mul

theorem toReal_mul_top (a : ℝ≥0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [toReal_mul, top_toReal, mul_zero]
#align ennreal.to_real_mul_top ENNReal.toReal_mul_top

theorem toReal_top_mul (a : ℝ≥0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact toReal_mul_top _
#align ennreal.to_real_top_mul ENNReal.toReal_top_mul

theorem toReal_eq_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal = b.toReal ↔ a = b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  simp only [coe_inj, NNReal.coe_inj, coe_toReal]
#align ennreal.to_real_eq_to_real ENNReal.toReal_eq_toReal

theorem toReal_smul (r : ℝ≥0) (s : ℝ≥0∞) : (r • s).toReal = r • s.toReal := by
  rw [ENNReal.smul_def, smul_eq_mul, toReal_mul, coe_toReal]
  rfl
#align ennreal.to_real_smul ENNReal.toReal_smul

protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using toReal_pos
#align ennreal.trichotomy ENNReal.trichotomy

protected theorem trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toReal ∨
          p = ∞ ∧ q = ∞ ∨
            0 < p.toReal ∧ q = ∞ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal ≤ q.toReal := by
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with (rfl | hq)
  · simpa using p.trichotomy
  repeat' right
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal.toReal_le_toReal hp'.ne hq.ne, ENNReal.toReal_pos_iff, hpq, hp, hp', hq', hq]
#align ennreal.trichotomy₂ ENNReal.trichotomy₂

protected theorem dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal :=
  haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 ≤ p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 ≤ p)
  this.imp_right fun h => h.2
#align ennreal.dichotomy ENNReal.dichotomy

theorem toReal_pos_iff_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] : 0 < p.toReal ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    have : (0 : ℝ) ≠ 0 := top_toReal ▸ (hp ▸ h.ne : 0 ≠ ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩
#align ennreal.to_real_pos_iff_ne_top ENNReal.toReal_pos_iff_ne_top

theorem toNNReal_inv (a : ℝ≥0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  induction' a with a; · simp
  rcases eq_or_ne a 0 with (rfl | ha); · simp
  rw [← coe_inv ha, toNNReal_coe, toNNReal_coe]
#align ennreal.to_nnreal_inv ENNReal.toNNReal_inv

theorem toNNReal_div (a b : ℝ≥0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv, toNNReal_mul, toNNReal_inv, div_eq_mul_inv]
#align ennreal.to_nnreal_div ENNReal.toNNReal_div

theorem toReal_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]
#align ennreal.to_real_inv ENNReal.toReal_inv

theorem toReal_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, toReal_mul, toReal_inv, div_eq_mul_inv]
#align ennreal.to_real_div ENNReal.toReal_div

theorem ofReal_prod_of_nonneg {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_prod, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf
#align ennreal.of_real_prod_of_nonneg ENNReal.ofReal_prod_of_nonneg

#noalign ennreal.to_nnreal_bit0
#noalign ennreal.to_nnreal_bit1
#noalign ennreal.to_real_bit0
#noalign ennreal.to_real_bit1
#noalign ennreal.of_real_bit0
#noalign ennreal.of_real_bit1

end Real

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}
variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, top_toNNReal, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]
#align ennreal.to_nnreal_infi ENNReal.toNNReal_iInf

theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  -- Porting note: `← sInf_image'` had to be replaced by `← image_eq_range` as the lemmas are used
  -- in a different order.
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iInf hf)
#align ennreal.to_nnreal_Inf ENNReal.toNNReal_sInf

theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, top_toNNReal]
#align ennreal.to_nnreal_supr ENNReal.toNNReal_iSup

theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  -- Porting note: `← sSup_image'` had to be replaced by `← image_eq_range` as the lemmas are used
  -- in a different order.
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iSup hf)
#align ennreal.to_nnreal_Sup ENNReal.toNNReal_sSup

theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]
#align ennreal.to_real_infi ENNReal.toReal_iInf

theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]
#align ennreal.to_real_Inf ENNReal.toReal_sInf

theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]
#align ennreal.to_real_supr ENNReal.toReal_iSup

theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]
#align ennreal.to_real_Sup ENNReal.toReal_sSup

theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)
#align ennreal.infi_add ENNReal.iInf_add

theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))
#align ennreal.supr_sub ENNReal.iSup_sub

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm]
#align ennreal.sub_infi ENNReal.sub_iInf

theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]
#align ennreal.Inf_add ENNReal.sInf_add

theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]
#align ennreal.add_infi ENNReal.add_iInf

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun a => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
#align ennreal.infi_add_infi ENNReal.iInf_add_iInf

theorem iInf_sum {α : Type*} {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a ∈ s, f i a = ∑ a ∈ s, ⨅ i, f i a := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.sum_empty, ciInf_const]
  · simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)
#align ennreal.infi_sum ENNReal.iInf_sum

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ENNReal.iInf_mul` that assumes `[Nonempty ι]` but does not require `x ≠ 0`. -/
theorem iInf_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    iInf f * x = ⨅ i, f i * x :=
  le_antisymm mul_right_mono.map_iInf_le
    ((ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mp <|
      le_iInf fun _ => (ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mpr <| iInf_le _ _)
#align ennreal.infi_mul_of_ne ENNReal.iInf_mul_of_ne

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ENNReal.iInf_mul_of_ne` that assumes `x ≠ 0` but does not require `[Nonempty ι]`. -/
theorem iInf_mul {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    iInf f * x = ⨅ i, f i * x := by
  by_cases h0 : x = 0
  · simp only [h0, mul_zero, iInf_const]
  · exact iInf_mul_of_ne h0 h
#align ennreal.infi_mul ENNReal.iInf_mul

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ENNReal.mul_iInf_of_ne` that assumes `x ≠ 0` but does not require `[Nonempty ι]`. -/
theorem mul_iInf {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    x * iInf f = ⨅ i, x * f i := by simpa only [mul_comm] using iInf_mul h
#align ennreal.mul_infi ENNReal.mul_iInf

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ENNReal.mul_iInf` that assumes `[Nonempty ι]` but does not require `x ≠ 0`. -/
theorem mul_iInf_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    x * iInf f = ⨅ i, x * f i := by simpa only [mul_comm] using iInf_mul_of_ne h0 h
#align ennreal.mul_infi_of_ne ENNReal.mul_iInf_of_ne

/-! `supr_mul`, `mul_supr` and variants are in `Topology.Instances.ENNReal`. -/

end iInf

section iSup

@[simp]
theorem iSup_eq_zero {ι : Sort*} {f : ι → ℝ≥0∞} : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  iSup_eq_bot
#align ennreal.supr_eq_zero ENNReal.iSup_eq_zero

@[simp]
theorem iSup_zero_eq_zero {ι : Sort*} : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp
#align ennreal.supr_zero_eq_zero ENNReal.iSup_zero_eq_zero

theorem sup_eq_zero {a b : ℝ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 :=
  sup_eq_bot_iff
#align ennreal.sup_eq_zero ENNReal.sup_eq_zero

theorem iSup_natCast : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  (iSup_eq_top _).2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)
#align ennreal.supr_coe_nat ENNReal.iSup_natCast

@[deprecated (since := "2024-04-05")] alias iSup_coe_nat := iSup_natCast

end iSup

end ENNReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.ofReal`. -/
@[positivity ENNReal.ofReal _]
def evalENNRealOfReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(ENNReal.ofReal $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(Iff.mpr (@ENNReal.ofReal_pos $a) $pa))
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofReal"
end Mathlib.Meta.Positivity
