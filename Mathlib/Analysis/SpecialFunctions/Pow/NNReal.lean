/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

#align_import analysis.special_functions.pow.nnreal from "leanprover-community/mathlib"@"4fa54b337f7d52805480306db1b1439c741848c8"

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

noncomputable section

open Classical Real NNReal ENNReal BigOperators ComplexConjugate

open Finset Set

namespace NNReal

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg_of_nonneg x.2 y⟩
#align nnreal.rpow NNReal.rpow

noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align nnreal.rpow_eq_pow NNReal.rpow_eq_pow

@[simp, norm_cast]
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl
#align nnreal.coe_rpow NNReal.coe_rpow

@[simp]
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  NNReal.eq <| Real.rpow_zero _
#align nnreal.rpow_zero NNReal.rpow_zero

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_eq, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2
#align nnreal.rpow_eq_zero_iff NNReal.rpow_eq_zero_iff

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
  NNReal.eq <| Real.zero_rpow h
#align nnreal.zero_rpow NNReal.zero_rpow

@[simp]
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  NNReal.eq <| Real.rpow_one _
#align nnreal.rpow_one NNReal.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  NNReal.eq <| Real.one_rpow _
#align nnreal.one_rpow NNReal.one_rpow

theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add ((pos_iff_ne_zero (α := ℝ≥0)).2 hx) _ _
#align nnreal.rpow_add NNReal.rpow_add

theorem rpow_add' (x : ℝ≥0) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add' x.2 h
#align nnreal.rpow_add' NNReal.rpow_add'

theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  NNReal.eq <| Real.rpow_mul x.2 y z
#align nnreal.rpow_mul NNReal.rpow_mul

theorem rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.rpow_neg x.2 _
#align nnreal.rpow_neg NNReal.rpow_neg

theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align nnreal.rpow_neg_one NNReal.rpow_neg_one

theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub ((pos_iff_ne_zero (α := ℝ≥0)).2 hx) y z
#align nnreal.rpow_sub NNReal.rpow_sub

theorem rpow_sub' (x : ℝ≥0) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub' x.2 h
#align nnreal.rpow_sub' NNReal.rpow_sub'

theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_inv_rpow_self NNReal.rpow_inv_rpow_self

theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_self_rpow_inv NNReal.rpow_self_rpow_inv

theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.inv_rpow x.2 y
#align nnreal.inv_rpow NNReal.inv_rpow

theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  NNReal.eq <| Real.div_rpow x.2 y.2 z
#align nnreal.div_rpow NNReal.div_rpow

theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
  refine' NNReal.eq _
  push_cast
  exact Real.sqrt_eq_rpow x.1
#align nnreal.sqrt_eq_rpow NNReal.sqrt_eq_rpow

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  NNReal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_nat_cast x n
#align nnreal.rpow_nat_cast NNReal.rpow_nat_cast

@[simp]
lemma rpow_ofNat (x : ℝ≥0) (n : ℕ) [n.AtLeastTwo] :
    x ^ (no_index (OfNat.ofNat n) : ℝ) = x ^ (OfNat.ofNat n : ℕ) :=
  rpow_nat_cast x n

theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
#align nnreal.rpow_two NNReal.rpow_two

theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  NNReal.eq <| Real.mul_rpow x.2 y.2
#align nnreal.mul_rpow NNReal.mul_rpow

/-- `rpow` as a `MonoidHom`-/
@[simps]
def rpowMonoidHom (r : ℝ) : ℝ≥0 →* ℝ≥0 where
  toFun := (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

/-- `rpow` variant of `List.prod_map_pow` for `ℝ≥0`-/
theorem list_prod_map_rpow (l : List ℝ≥0) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r :=
  l.prod_hom (rpowMonoidHom r)

theorem list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ≥0) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← list_prod_map_rpow, List.map_map]; rfl

/-- `rpow` version of `Multiset.prod_map_pow` for `ℝ≥0`. -/
lemma multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r :=
  s.prod_hom' (rpowMonoidHom r) _

/-- `rpow` version of `Finset.prod_pow` for `ℝ≥0`. -/
lemma finset_prod_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (∏ i in s, f i ^ r) = (∏ i in s, f i) ^ r :=
  multiset_prod_map_rpow _ _ _

-- note: these don't really belong here, but they're much easier to prove in terms of the above

section Real

/-- `rpow` version of `List.prod_map_pow` for `Real`. -/
theorem _root_.Real.list_prod_map_rpow (l : List ℝ) (hl : ∀ x ∈ l, (0 : ℝ) ≤ x) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r := by
  lift l to List ℝ≥0 using hl
  have := congr_arg ((↑) : ℝ≥0 → ℝ) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this

theorem _root_.Real.list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ)
    (hl : ∀ i ∈ l, (0 : ℝ) ≤ f i) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← Real.list_prod_map_rpow (l.map f) _ r, List.map_map]; rfl
  simpa using hl

/-- `rpow` version of `Multiset.prod_map_pow`. -/
theorem _root_.Real.multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ)
    (hs : ∀ i ∈ s, (0 : ℝ) ≤ f i) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r := by
  induction' s using Quotient.inductionOn with l
  simpa using Real.list_prod_map_rpow' l f hs r

/-- `rpow` version of `Finset.prod_pow`. -/
theorem _root_.Real.finset_prod_rpow
    {ι} (s : Finset ι) (f : ι → ℝ) (hs : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i in s, f i ^ r) = (∏ i in s, f i) ^ r :=
  Real.multiset_prod_map_rpow s.val f hs r

end Real

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂
#align nnreal.rpow_le_rpow NNReal.rpow_le_rpow

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂
#align nnreal.rpow_lt_rpow NNReal.rpow_lt_rpow

theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz
#align nnreal.rpow_lt_rpow_iff NNReal.rpow_lt_rpow_iff

theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz
#align nnreal.rpow_le_rpow_iff NNReal.rpow_le_rpow_iff

theorem le_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.le_rpow_one_div_iff NNReal.le_rpow_one_div_iff

theorem rpow_one_div_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.rpow_one_div_le_iff NNReal.rpow_one_div_le_iff

@[gcongr] theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz
#align nnreal.rpow_lt_rpow_of_exponent_lt NNReal.rpow_lt_rpow_of_exponent_lt

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz
#align nnreal.rpow_le_rpow_of_exponent_le NNReal.rpow_le_rpow_of_exponent_le

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz
#align nnreal.rpow_lt_rpow_of_exponent_gt NNReal.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz
#align nnreal.rpow_le_rpow_of_exponent_ge NNReal.rpow_le_rpow_of_exponent_ge

theorem rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x ^ p := by
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : ℝ) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)
#align nnreal.rpow_pos NNReal.rpow_pos

theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz
#align nnreal.rpow_lt_one NNReal.rpow_lt_one

theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz
#align nnreal.rpow_le_one NNReal.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz
#align nnreal.rpow_lt_one_of_one_lt_of_neg NNReal.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz
#align nnreal.rpow_le_one_of_one_le_of_nonpos NNReal.rpow_le_one_of_one_le_of_nonpos

theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz
#align nnreal.one_lt_rpow NNReal.one_lt_rpow

theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁
#align nnreal.one_le_rpow NNReal.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz
#align nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz
#align nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos

theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le
#align nnreal.rpow_le_self_of_le_one NNReal.rpow_le_self_of_le_one

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz
#align nnreal.rpow_left_injective NNReal.rpow_left_injective

theorem rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff
#align nnreal.rpow_eq_rpow_iff NNReal.rpow_eq_rpow_iff

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align nnreal.rpow_left_surjective NNReal.rpow_left_surjective

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align nnreal.rpow_left_bijective NNReal.rpow_left_bijective

theorem eq_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x = y ^ (1 / z) ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.eq_rpow_one_div_iff NNReal.eq_rpow_one_div_iff

theorem rpow_one_div_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ (1 / z) = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.rpow_one_div_eq_iff NNReal.rpow_one_div_eq_iff

theorem pow_rpow_inv_natCast (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← NNReal.coe_eq, coe_rpow, NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn
#align nnreal.pow_nat_rpow_nat_inv NNReal.pow_rpow_inv_natCast

theorem rpow_inv_natCast_pow (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← NNReal.coe_eq, NNReal.coe_pow, coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn
#align nnreal.rpow_nat_inv_pow_nat NNReal.rpow_inv_natCast_pow

theorem _root_.Real.toNNReal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y := by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow, Real.toNNReal_coe]
#align real.to_nnreal_rpow_of_nonneg Real.toNNReal_rpow_of_nonneg

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0 => x ^ z :=
  fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h, coe_lt_coe]

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0 => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0 => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0 => x ^ (1 / y)`. -/
@[simps! apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0 ≃o ℝ≥0 :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]

theorem orderIsoRpow_symm_eq (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]; rfl

end NNReal

namespace ENNReal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0
#align ennreal.rpow ENNReal.rpow

noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align ennreal.rpow_eq_pow ENNReal.rpow_eq_pow

@[simp]
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [lt_irrefl]
#align ennreal.rpow_zero ENNReal.rpow_zero

theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl
#align ennreal.top_rpow_def ENNReal.top_rpow_def

@[simp]
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]
#align ennreal.top_rpow_of_pos ENNReal.top_rpow_of_pos

@[simp]
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]
#align ennreal.top_rpow_of_neg ENNReal.top_rpow_of_neg

@[simp]
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h, asymm h, ne_of_gt h]
#align ennreal.zero_rpow_of_pos ENNReal.zero_rpow_of_pos

@[simp]
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h, ne_of_gt h]
#align ennreal.zero_rpow_of_neg ENNReal.zero_rpow_of_neg

theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ := by
  rcases lt_trichotomy (0 : ℝ) y with (H | rfl | H)
  · simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl]
  · simp [lt_irrefl]
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]
#align ennreal.zero_rpow_def ENNReal.zero_rpow_def

@[simp]
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * (0 : ℝ≥0∞) ^ y = (0 : ℝ≥0∞) ^ y := by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]
#align ennreal.zero_rpow_mul_self ENNReal.zero_rpow_mul_self

@[norm_cast]
theorem coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) := by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]
#align ennreal.coe_rpow_of_ne_zero ENNReal.coe_rpow_of_ne_zero

@[norm_cast]
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) := by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _
#align ennreal.coe_rpow_of_nonneg ENNReal.coe_rpow_of_nonneg

theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else ↑(x ^ y) :=
  rfl
#align ennreal.coe_rpow_def ENNReal.coe_rpow_def

@[simp]
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_lt
#align ennreal.rpow_one ENNReal.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 := by
  rw [← coe_one, coe_rpow_of_ne_zero one_ne_zero]
  simp
#align ennreal.one_rpow ENNReal.one_rpow

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_zero_iff ENNReal.rpow_eq_zero_iff

@[simp]
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_top_iff ENNReal.rpow_eq_top_iff

theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]
#align ennreal.rpow_eq_top_iff_of_pos ENNReal.rpow_eq_top_iff_of_pos

lemma rpow_lt_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y < ∞ ↔ x < ∞ := by
  simp only [lt_top_iff_ne_top, Ne.def, rpow_eq_top_iff_of_pos hy]

theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ := by
  rw [ENNReal.rpow_eq_top_iff]
  rintro (h|h)
  · exfalso
    rw [lt_iff_not_ge] at h
    exact h.right hy0
  · exact h.left
#align ennreal.rpow_eq_top_of_nonneg ENNReal.rpow_eq_top_of_nonneg

theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h
#align ennreal.rpow_ne_top_of_nonneg ENNReal.rpow_ne_top_of_nonneg

theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)
#align ennreal.rpow_lt_top_of_nonneg ENNReal.rpow_lt_top_of_nonneg

theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z := by
  cases' x with x
  · exact (h'x rfl).elim
  have : x ≠ 0 := fun h => by simp [h] at hx
  simp [coe_rpow_of_ne_zero this, NNReal.rpow_add this]
#align ennreal.rpow_add ENNReal.rpow_add

theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]
#align ennreal.rpow_neg ENNReal.rpow_neg

theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]
#align ennreal.rpow_sub ENNReal.rpow_sub

theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align ennreal.rpow_neg_one ENNReal.rpow_neg_one

theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, coe_rpow_of_ne_zero this, NNReal.rpow_mul]
#align ennreal.rpow_mul ENNReal.rpow_mul

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_pos _)]
  · simp [coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]
#align ennreal.rpow_nat_cast ENNReal.rpow_nat_cast

@[simp]
lemma rpow_ofNat (x : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    x ^ (no_index (OfNat.ofNat n) : ℝ) = x ^ (OfNat.ofNat n) :=
  rpow_nat_cast x n

theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
#align ennreal.rpow_two ENNReal.rpow_two

theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_lt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_le hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y using ENNReal.recTopCoe <;> cases' hz with hz hz <;> simp [*, hz.not_lt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x using ENNReal.recTopCoe
  · cases' hz with hz hz <;> simp [hz, top_unique hxy]
  induction y using ENNReal.recTopCoe
  · rw [ne_eq, coe_eq_zero] at hx0
    cases' hz with hz hz <;> simp [*]
  simp only [*, false_and_iff, and_false_iff, false_or_iff, if_false]
  norm_cast at *
  rw [coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_rpow]
  norm_cast
#align ennreal.mul_rpow_eq_ite ENNReal.mul_rpow_eq_ite

theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_top ENNReal.mul_rpow_of_ne_top

@[norm_cast]
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = (x : ℝ≥0∞) ^ z * (y : ℝ≥0∞) ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z
#align ennreal.coe_mul_rpow ENNReal.coe_mul_rpow

theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i in s, (f i : ℝ≥0∞) ^ r = ((∏ i in s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | insert hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_zero ENNReal.mul_rpow_of_ne_zero

theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_lt, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_nonneg ENNReal.mul_rpow_of_nonneg

theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_lt_top h2f |>.ne

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | insert hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_lt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_rpow]
#align ennreal.inv_rpow ENNReal.inv_rpow

theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]
#align ennreal.div_rpow_of_nonneg ENNReal.div_rpow_of_nonneg

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z := by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]
#align ennreal.strict_mono_rpow_of_pos ENNReal.strictMono_rpow_of_pos

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone
#align ennreal.monotone_rpow_of_nonneg ENNReal.monotone_rpow_of_nonneg

/-- Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`. -/
@[simps! apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]
#align ennreal.order_iso_rpow ENNReal.orderIsoRpow

theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]
  rfl
#align ennreal.order_iso_rpow_symm_apply ENNReal.orderIsoRpow_symm_apply

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁
#align ennreal.rpow_le_rpow ENNReal.rpow_le_rpow

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁
#align ennreal.rpow_lt_rpow ENNReal.rpow_lt_rpow

theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le
#align ennreal.rpow_le_rpow_iff ENNReal.rpow_le_rpow_iff

theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt
#align ennreal.rpow_lt_rpow_iff ENNReal.rpow_lt_rpow_iff

theorem le_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z hz.ne']
  rw [rpow_mul, ← one_div, @rpow_le_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.le_rpow_one_div_iff ENNReal.le_rpow_one_div_iff

theorem lt_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, ← one_div, @rpow_lt_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.lt_rpow_one_div_iff ENNReal.lt_rpow_one_div_iff

theorem rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 2 [← @_root_.mul_inv_cancel _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ← one_div, ENNReal.rpow_le_rpow_iff (one_div_pos.2 hz)]
#align ennreal.rpow_one_div_le_iff ENNReal.rpow_one_div_le_iff

theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]
#align ennreal.rpow_lt_rpow_of_exponent_lt ENNReal.rpow_lt_rpow_of_exponent_lt

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl] <;>
    linarith
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]
#align ennreal.rpow_le_rpow_of_exponent_le ENNReal.rpow_le_rpow_of_exponent_le

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
#align ennreal.rpow_lt_rpow_of_exponent_gt ENNReal.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]
#align ennreal.rpow_le_rpow_of_exponent_ge ENNReal.rpow_le_rpow_of_exponent_ge

theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le
#align ennreal.rpow_le_self_of_le_one ENNReal.rpow_le_self_of_le_one

theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z := by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le
#align ennreal.le_rpow_self_of_one_le ENNReal.le_rpow_self_of_one_le

theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne.def] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos
#align ennreal.rpow_pos_of_nonneg ENNReal.rpow_pos_of_nonneg

theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p := by
  cases' lt_or_le 0 p with hp_pos hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top
#align ennreal.rpow_pos ENNReal.rpow_pos

theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]
#align ennreal.rpow_lt_one ENNReal.rpow_lt_one

theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]
#align ennreal.rpow_le_one ENNReal.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]
#align ennreal.rpow_lt_one_of_one_lt_of_neg ENNReal.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]
#align ennreal.rpow_le_one_of_one_le_of_neg ENNReal.rpow_le_one_of_one_le_of_neg

theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]
#align ennreal.one_lt_rpow ENNReal.one_lt_rpow

theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]
#align ennreal.one_le_rpow ENNReal.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]
#align ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg ENNReal.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]
#align ennreal.one_le_rpow_of_pos_of_le_one_of_neg ENNReal.one_le_rpow_of_pos_of_le_one_of_neg

theorem toNNReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toNNReal ^ z = (x ^ z).toNNReal := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases' x with x
    · simp [H, ne_of_lt]
    by_cases hx : x = 0
    · simp [hx, H, ne_of_lt]
    · simp [coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [coe_rpow_of_nonneg _ (le_of_lt H)]
#align ennreal.to_nnreal_rpow ENNReal.toNNReal_rpow

theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_rpow, ENNReal.toNNReal_rpow]
#align ennreal.to_real_rpow ENNReal.toReal_rpow

theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [coe_rpow_of_ne_zero, coe_eq_coe, Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]
#align ennreal.of_real_rpow_of_pos ENNReal.ofReal_rpow_of_pos

theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne.def] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne.def] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)
#align ennreal.of_real_rpow_of_nonneg ENNReal.ofReal_rpow_of_nonneg

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0∞ => y ^ x := by
  intro y z hyz
  dsimp only at hyz
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul, rpow_mul, hyz]
#align ennreal.rpow_left_injective ENNReal.rpow_left_injective

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align ennreal.rpow_left_surjective ENNReal.rpow_left_surjective

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align ennreal.rpow_left_bijective ENNReal.rpow_left_bijective

end ENNReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- section Tactics

-- /-!
-- ## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-- -/


-- namespace NormNum

-- theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, NNReal.rpow_nat_cast]
-- #align norm_num.nnrpow_pos NormNum.nnrpow_pos

-- theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_nat_cast]
-- #align norm_num.nnrpow_neg NormNum.nnrpow_neg

-- theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, ENNReal.rpow_nat_cast]
-- #align norm_num.ennrpow_pos NormNum.ennrpow_pos

-- theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_nat_cast]
-- #align norm_num.ennrpow_neg NormNum.ennrpow_neg

-- /-- Evaluate `NNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))
-- #align norm_num.prove_nnrpow norm_num.prove_nnrpow

-- /-- Evaluate `ENNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))
-- #align norm_num.prove_ennrpow norm_num.prove_ennrpow

-- /-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_nnrpow_ennrpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | _ => tactic.failed
-- #align norm_num.eval_nnrpow_ennrpow norm_num.eval_nnrpow_ennrpow

-- end NormNum

-- namespace Tactic

-- namespace Positivity

-- private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
--   NNReal.rpow_pos ha
-- #align tactic.positivity.nnrpow_pos tactic.positivity.nnrpow_pos

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals.
-- -/
-- unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   match strictness_a with
--     | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
--     | _ => failed
-- #align tactic.positivity.prove_nnrpow tactic.positivity.prove_nnrpow

-- -- We already know `0 ≤ x` for all `x : ℝ≥0`
-- private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
--   ENNReal.rpow_pos_of_nonneg ha hb.le
-- #align tactic.positivity.ennrpow_pos tactic.positivity.ennrpow_pos

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of extended
-- nonnegative reals. -/
-- unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   let strictness_b ← core b
--   match strictness_a, strictness_b with
--     | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
--     | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
--     | _, _ => failed
-- #align tactic.positivity.prove_ennrpow tactic.positivity.prove_ennrpow

-- -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
-- end Positivity

-- open Positivity

-- /-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
-- the base is nonnegative and positive when the base is positive. -/
-- @[positivity]
-- unsafe def positivity_nnrpow_ennrpow : expr → tactic strictness
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
--   | q(NNReal.rpow $(a) $(b)) => prove_nnrpow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
--   | q(ENNReal.rpow $(a) $(b)) => prove_ennrpow a b
--   | _ => failed
-- #align tactic.positivity_nnrpow_ennrpow tactic.positivity_nnrpow_ennrpow

-- end Tactic

-- end Tactics
