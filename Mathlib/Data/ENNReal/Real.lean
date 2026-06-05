/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Basic

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

## Main statements

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

section Real

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl

theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)

theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_inj,
    Real.toNNReal_add hp hq]

theorem ofReal_add_le {p q : ℝ} : ENNReal.ofReal (p + q) ≤ ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le

@[simp]
theorem toReal_le_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

@[gcongr]
theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h

theorem toReal_mono' (h : a ≤ b) (ht : b = ∞ → a = ∞) : a.toReal ≤ b.toReal := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]
theorem toReal_lt_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

@[gcongr]
theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h

@[gcongr]
theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal :=
  toReal_mono hb h

theorem le_toNNReal_of_coe_le (h : p ≤ a) (ha : a ≠ ∞) : p ≤ a.toNNReal :=
  @toNNReal_coe p ▸ toNNReal_mono ha h

@[simp]
theorem toNNReal_le_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal ≤ b.toNNReal ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩

@[gcongr]
theorem toNNReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]

@[simp]
theorem toNNReal_lt_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩

theorem toNNReal_lt_of_lt_coe (h : a < p) : a.toNNReal < p :=
  @toNNReal_coe p ▸ toNNReal_strict_mono coe_ne_top h

theorem toReal_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim
    (fun h => by simp only [h, ENNReal.toReal_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNReal.toReal_mono hr h, max_eq_left]

theorem toReal_min {a b : ℝ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim (fun h => by simp only [h, ENNReal.toReal_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNReal.toReal_mono hr h, min_eq_right]

theorem toReal_sup {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).toReal = a.toReal ⊔ b.toReal :=
  toReal_max

theorem toReal_inf {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).toReal = a.toReal ⊓ b.toReal :=
  toReal_min

theorem toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞ := by
  induction a <;> simp

theorem toNNReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNNReal :=
  toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

theorem toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  NNReal.coe_pos.trans toNNReal_pos_iff

theorem toReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toReal :=
  toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]
theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]

lemma ofReal_mono : Monotone ENNReal.ofReal := fun _ _ ↦ ENNReal.ofReal_le_ofReal

theorem ofReal_le_of_le_toReal {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ENNReal.toReal b) :
    ENNReal.ofReal a ≤ b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le

@[simp]
theorem ofReal_le_ofReal_iff {p q : ℝ} (h : 0 ≤ q) :
    ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_le_coe, Real.toNNReal_le_toNNReal_iff h]

lemma ofReal_le_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p ≤ .ofReal q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

@[simp, norm_cast]
lemma ofReal_le_coe {a : ℝ} {b : ℝ≥0} : ENNReal.ofReal a ≤ b ↔ a ≤ b := by
  simp [← ofReal_le_ofReal_iff]

lemma ofReal_lt_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]
theorem ofReal_eq_ofReal_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_inj, Real.toNNReal_eq_toNNReal_iff hp hq]

@[simp]
theorem ofReal_lt_ofReal_iff {p q : ℝ} (h : 0 < q) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff h]

theorem ofReal_lt_ofReal_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]

@[simp]
theorem ofReal_pos {p : ℝ} : 0 < ENNReal.ofReal p ↔ 0 < p := by simp [ENNReal.ofReal]

@[bound] private alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ofReal_pos

@[simp]
theorem ofReal_eq_zero {p : ℝ} : ENNReal.ofReal p = 0 ↔ p ≤ 0 := by simp [ENNReal.ofReal]

@[simp] lemma ofReal_min (x y : ℝ) : ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_min

@[simp] lemma ofReal_max (x y : ℝ) : ENNReal.ofReal (max x y) = max (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_max

theorem ofReal_ne_zero_iff {r : ℝ} : ENNReal.ofReal r ≠ 0 ↔ 0 < r := by
  rw [← pos_iff_ne_zero, ENNReal.ofReal_pos]

@[simp]
theorem zero_eq_ofReal {p : ℝ} : 0 = ENNReal.ofReal p ↔ p ≤ 0 :=
  eq_comm.trans ofReal_eq_zero

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero

@[simp]
lemma ofReal_lt_natCast {p : ℝ} {n : ℕ} (hn : n ≠ 0) : ENNReal.ofReal p < n ↔ p < n := mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
lemma ofReal_lt_one {p : ℝ} : ENNReal.ofReal p < 1 ↔ p < 1 := mod_cast ofReal_lt_natCast one_ne_zero

@[simp]
lemma ofReal_lt_ofNat {p : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal p < ofNat(n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_natCast (NeZero.ne n)

@[simp]
lemma natCast_le_ofReal {n : ℕ} {p : ℝ} (hn : n ≠ 0) : n ≤ ENNReal.ofReal p ↔ n ≤ p := by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[simp]
lemma one_le_ofReal {p : ℝ} : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p := mod_cast natCast_le_ofReal one_ne_zero

@[simp]
lemma ofNat_le_ofReal {n : ℕ} [n.AtLeastTwo] {p : ℝ} :
    ofNat(n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p :=
  natCast_le_ofReal (NeZero.ne n)

@[simp, norm_cast]
lemma ofReal_le_natCast {r : ℝ} {n : ℕ} : ENNReal.ofReal r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Real.toNNReal_le_natCast

@[simp]
lemma ofReal_le_one {r : ℝ} : ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
lemma ofReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r ≤ ofNat(n) ↔ r ≤ OfNat.ofNat n :=
  ofReal_le_natCast

@[simp]
lemma natCast_lt_ofReal {n : ℕ} {r : ℝ} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.natCast_lt_toNNReal

@[simp]
lemma one_lt_ofReal {r : ℝ} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
lemma ofNat_lt_ofReal {n : ℕ} [n.AtLeastTwo] {r : ℝ} :
    ofNat(n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  natCast_lt_ofReal

@[simp]
lemma ofReal_eq_natCast {r : ℝ} {n : ℕ} (h : n ≠ 0) : ENNReal.ofReal r = n ↔ r = n :=
  ENNReal.coe_inj.trans <| Real.toNNReal_eq_natCast h

@[simp]
lemma ofReal_eq_one {r : ℝ} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]
lemma ofReal_eq_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r = ofNat(n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_natCast (NeZero.ne n)

theorem ofReal_le_iff_le_toReal {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
    ENNReal.ofReal a ≤ b ↔ a ≤ ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe

theorem ofReal_lt_iff_lt_toReal {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    ENNReal.ofReal a < b ↔ a < ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha

@[simp] lemma coe_lt_ofReal {a : ℝ≥0} {b : ℝ} : a < ENNReal.ofReal b ↔ a < b := by
  simp [ENNReal.ofReal, Real.lt_toNNReal_iff_coe_lt]

theorem ofReal_lt_coe_iff {a : ℝ} {b : ℝ≥0} (ha : 0 ≤ a) : ENNReal.ofReal a < b ↔ a < b :=
  (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans <| by rw [coe_toReal]

theorem le_ofReal_iff_toReal_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ ENNReal.ofReal b ↔ ENNReal.toReal a ≤ b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb

theorem toReal_le_of_le_ofReal {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ENNReal.ofReal b) :
    ENNReal.toReal a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h

theorem lt_ofReal_iff_toReal_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
    a < ENNReal.ofReal b ↔ ENNReal.toReal a < b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt

theorem toReal_lt_of_lt_ofReal {b : ℝ} (h : a < ENNReal.ofReal b) : ENNReal.toReal a < b :=
  (lt_ofReal_iff_toReal_lt h.ne_top).1 h

@[simp]
theorem ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]

theorem ofReal_mul' {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm, ofReal_mul hq, mul_comm]

@[simp]
theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp, ← coe_pow, ← ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]

theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]

@[simp]
theorem toNNReal_mul {a b : ℝ≥0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal :=
  WithTop.untopD_zero_mul a b

theorem toNNReal_mul_top (a : ℝ≥0∞) : ENNReal.toNNReal (a * ∞) = 0 := by simp

theorem toNNReal_top_mul (a : ℝ≥0∞) : ENNReal.toNNReal (∞ * a) = 0 := by simp

/-- `ENNReal.toNNReal` as a `MonoidHom`. -/
noncomputable def toNNRealHom : ℝ≥0∞ →*₀ ℝ≥0 where
  toFun := ENNReal.toNNReal
  map_one' := toNNReal_coe _
  map_mul' _ _ := toNNReal_mul
  map_zero' := toNNReal_zero

@[simp]
theorem toNNReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toNNReal = a.toNNReal ^ n :=
  toNNRealHom.map_pow a n

/-- `ENNReal.toReal` as a `MonoidHom`. -/
noncomputable def toRealHom : ℝ≥0∞ →*₀ ℝ :=
  (NNReal.toRealHom : ℝ≥0 →*₀ ℝ).comp toNNRealHom

@[simp]
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b

theorem toReal_nsmul (a : ℝ≥0∞) (n : ℕ) : (n • a).toReal = n • a.toReal := by simp

@[simp]
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n

theorem toReal_ofReal_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h]

theorem toReal_mul_top (a : ℝ≥0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [toReal_mul, toReal_top, mul_zero]

theorem toReal_top_mul (a : ℝ≥0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact toReal_mul_top _

protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using toReal_pos

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
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal.toReal_mono hq.ne hpq, ENNReal.toReal_pos_iff, hp, hp', hq', hq]

protected theorem dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal :=
  haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 ≤ p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 ≤ p)
  this.imp_right fun h => h.2

theorem toReal_pos_iff_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] : 0 < p.toReal ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    have : (0 : ℝ) ≠ 0 := toReal_top ▸ (hp ▸ h.ne : 0 ≠ ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

end Real

end ENNReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.ofReal`. -/
@[positivity ENNReal.ofReal _]
meta def evalENNRealOfReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(ENNReal.ofReal $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(Iff.mpr (@ENNReal.ofReal_pos $a) $pa))
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofReal"
end Mathlib.Meta.Positivity
