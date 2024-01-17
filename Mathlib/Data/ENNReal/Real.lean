/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Inv

/-!
# Coercion between real and extended non-negative real numbers

TODO write main docstring
-/

open Set BigOperators NNReal ENNReal

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
  induction a using recTopCoe
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
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_eq_coe,
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

theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h
#align ennreal.to_real_mono ENNReal.toReal_mono

-- porting note: new lemma
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

theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h
#align ennreal.to_real_strict_mono ENNReal.toReal_strict_mono

theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal :=
  toReal_mono hb h
#align ennreal.to_nnreal_mono ENNReal.toNNReal_mono

-- porting note: new lemma
/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

-- porting note: new lemma
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
  induction a using recTopCoe <;> simp
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

theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]
#align ennreal.of_real_le_of_real ENNReal.ofReal_le_ofReal

theorem ofReal_le_of_le_toReal {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ENNReal.toReal b) :
    ENNReal.ofReal a ≤ b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le
#align ennreal.of_real_le_of_le_to_real ENNReal.ofReal_le_of_le_toReal

@[simp]
theorem ofReal_le_ofReal_iff {p q : ℝ} (h : 0 ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q :=
  by rw [ENNReal.ofReal, ENNReal.ofReal, coe_le_coe, Real.toNNReal_le_toNNReal_iff h]
#align ennreal.of_real_le_of_real_iff ENNReal.ofReal_le_ofReal_iff

lemma ofReal_le_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p ≤ .ofReal q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

lemma ofReal_lt_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]
theorem ofReal_eq_ofReal_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_eq_coe, Real.toNNReal_eq_toNNReal_iff hp hq]
#align ennreal.of_real_eq_of_real_iff ENNReal.ofReal_eq_ofReal_iff

@[simp]
theorem ofReal_lt_ofReal_iff {p q : ℝ} (h : 0 < q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q :=
  by rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff h]
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
lemma ofReal_lt_nat_cast {p : ℝ} {n : ℕ} (hn : n ≠ 0) : ENNReal.ofReal p < n ↔ p < n := by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
lemma ofReal_lt_one {p : ℝ} : ENNReal.ofReal p < 1 ↔ p < 1 := by
  exact mod_cast ofReal_lt_nat_cast one_ne_zero

@[simp]
lemma ofReal_lt_ofNat {p : ℝ} {n : ℕ} [h : n.AtLeastTwo] :
    ENNReal.ofReal p < no_index (OfNat.ofNat n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_nat_cast h.ne_zero

@[simp]
lemma nat_cast_le_ofReal {n : ℕ} {p : ℝ} (hn : n ≠ 0) : n ≤ ENNReal.ofReal p ↔ n ≤ p := by
  simp only [← not_lt, ofReal_lt_nat_cast hn]

@[simp]
lemma one_le_ofReal {p : ℝ} : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p := by
  exact mod_cast nat_cast_le_ofReal one_ne_zero

@[simp]
lemma ofNat_le_ofReal {n : ℕ} [h : n.AtLeastTwo] {p : ℝ} :
    no_index (OfNat.ofNat n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p :=
  nat_cast_le_ofReal h.ne_zero

@[simp]
lemma ofReal_le_nat_cast {r : ℝ} {n : ℕ} : ENNReal.ofReal r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Real.toNNReal_le_nat_cast

@[simp]
lemma ofReal_le_one {r : ℝ} : ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
lemma ofReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r ≤ no_index (OfNat.ofNat n) ↔ r ≤ OfNat.ofNat n :=
  ofReal_le_nat_cast

@[simp]
lemma nat_cast_lt_ofReal {n : ℕ} {r : ℝ} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.nat_cast_lt_toNNReal

@[simp]
lemma one_lt_ofReal {r : ℝ} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
lemma ofNat_lt_ofReal {n : ℕ} [n.AtLeastTwo] {r : ℝ} :
    no_index (OfNat.ofNat n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  nat_cast_lt_ofReal

@[simp]
lemma ofReal_eq_nat_cast {r : ℝ} {n : ℕ} (h : n ≠ 0) : ENNReal.ofReal r = n ↔ r = n :=
  ENNReal.coe_eq_coe.trans <| Real.toNNReal_eq_nat_cast h

@[simp]
lemma ofReal_eq_one {r : ℝ} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_eq_coe.trans Real.toNNReal_eq_one

@[simp]
lemma ofReal_eq_ofNat {r : ℝ} {n : ℕ} [h : n.AtLeastTwo] :
    ENNReal.ofReal r = no_index (OfNat.ofNat n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_nat_cast h.ne_zero

theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine' ENNReal.eq_sub_of_add_eq ofReal_ne_top _
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

theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n :=
  by rw [ofReal_eq_coe_nnreal hp, ← coe_pow, ← ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]
#align ennreal.of_real_pow ENNReal.ofReal_pow

theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_coe_nat n, ← ofReal_mul n.cast_nonneg]
#align ennreal.of_real_nsmul ENNReal.ofReal_nsmul

theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal x⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_eq_coe,
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

-- porting note: todo: upgrade to `→*₀`
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
    (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal :=
  map_prod toNNRealHom _ _
#align ennreal.to_nnreal_prod ENNReal.toNNReal_prod

-- porting note: todo: upgrade to `→*₀`
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
    (∏ i in s, f i).toReal = ∏ i in s, (f i).toReal :=
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
  simp only [coe_eq_coe, NNReal.coe_eq, coe_toReal]
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
  induction' a using recTopCoe with a; · simp
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
    ENNReal.ofReal (∏ i in s, f i) = ∏ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_prod, coe_eq_coe]
  exact Real.toNNReal_prod_of_nonneg hf
#align ennreal.of_real_prod_of_nonneg ENNReal.ofReal_prod_of_nonneg

#noalign ennreal.to_nnreal_bit0
#noalign ennreal.to_nnreal_bit1
#noalign ennreal.to_real_bit0
#noalign ennreal.to_real_bit1
#noalign ennreal.of_real_bit0
#noalign ennreal.of_real_bit1

end Real

end ENNReal
