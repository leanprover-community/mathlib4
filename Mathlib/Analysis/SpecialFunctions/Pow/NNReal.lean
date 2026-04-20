/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.Rify
public import Qq

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

@[expose] public section

noncomputable section

open Real NNReal ENNReal ComplexConjugate Finset Function Set

namespace NNReal
variable {x : ℝ≥0} {w y z : ℝ}

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg x.2 y⟩

noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp, norm_cast]
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl

@[simp]
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  NNReal.eq <| Real.rpow_zero _

theorem rpow_zero_pos (x : ℝ≥0) : 0 < x ^ (0 : ℝ) := by rw [rpow_zero]; exact one_pos

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2

lemma rpow_eq_zero (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by simp [hy]

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
  NNReal.eq <| Real.zero_rpow h

theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0) ^ y = if y = 0 then 1 else 0 := by
  split_ifs with h <;> simp [h]

@[simp]
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  NNReal.eq <| Real.rpow_one _

lemma rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.rpow_neg x.2 _

@[simp, norm_cast]
lemma rpow_natCast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  NNReal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]
lemma rpow_intCast (x : ℝ≥0) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  NNReal.eq <| Real.one_rpow _

theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _

theorem rpow_add' (h : y + z ≠ 0) (x : ℝ≥0) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add' x.2 h

lemma rpow_add_intCast (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _

lemma rpow_add_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _

lemma rpow_sub_intCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _

lemma rpow_sub_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _

lemma rpow_add_intCast' {n : ℤ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h

lemma rpow_add_natCast' {n : ℕ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h

lemma rpow_sub_intCast' {n : ℤ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h

lemma rpow_sub_natCast' {n : ℕ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h

lemma rpow_add_one (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1

lemma rpow_sub_one (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1

lemma rpow_add_one' (h : y + 1 ≠ 0) (x : ℝ≥0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' h, rpow_one]

lemma rpow_one_add' (h : 1 + y ≠ 0) (x : ℝ≥0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' h, rpow_one]

theorem rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

/-- Variant of `NNReal.rpow_add'` that avoids having to prove `y + z = w` twice. -/
lemma rpow_of_add_eq (x : ℝ≥0) (hw : w ≠ 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h, rpow_add']; rwa [h]

theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  NNReal.eq <| Real.rpow_mul x.2 y z

lemma rpow_natCast_mul (x : ℝ≥0) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_mul_natCast (x : ℝ≥0) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_intCast_mul (x : ℝ≥0) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_mul_intCast (x : ℝ≥0) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]

theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]

theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) y z

theorem rpow_sub' (h : y - z ≠ 0) (x : ℝ≥0) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub' x.2 h

lemma rpow_sub_one' (h : y - 1 ≠ 0) (x : ℝ≥0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' h, rpow_one]

lemma rpow_one_sub' (h : 1 - y ≠ 0) (x : ℝ≥0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' h, rpow_one]

theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x := by
  rw [← rpow_mul]
  field_simp
  simp

theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x := by
  rw [← rpow_mul]
  field_simp
  simp

theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.inv_rpow x.2 y

theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  NNReal.eq <| Real.div_rpow x.2 y.2 z

theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

@[simp]
lemma rpow_ofNat (x : ℝ≥0) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (OfNat.ofNat n : ℕ) :=
  rpow_natCast x n

theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2

theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  NNReal.eq <| Real.mul_rpow x.2 y.2

/-- `rpow` as a `MonoidHom` -/
@[simps]
def rpowMonoidHom (r : ℝ) : ℝ≥0 →* ℝ≥0 where
  toFun := (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

/-- `rpow` variant of `List.prod_map_pow` for `ℝ≥0` -/
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
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
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
  rw [← Real.list_prod_map_rpow (l.map f) _ r, List.map_map]
  · rfl
  simpa using hl

/-- `rpow` version of `Multiset.prod_map_pow`. -/
theorem _root_.Real.multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ)
    (hs : ∀ i ∈ s, (0 : ℝ) ≤ f i) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r := by
  obtain ⟨l⟩ := s
  simpa using Real.list_prod_map_rpow' l f hs r

/-- `rpow` version of `Finset.prod_pow`. -/
theorem _root_.Real.finset_prod_rpow
    {ι} (s : Finset ι) (f : ι → ℝ) (hs : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
  Real.multiset_prod_map_rpow s.val f hs r

end Real

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂

theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz

theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz

theorem le_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']

theorem rpow_inv_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']

theorem lt_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  simp only [← not_le, rpow_inv_le_iff hz]

theorem rpow_inv_lt_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

section
variable {y : ℝ≥0}

lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z :=
  Real.rpow_lt_rpow_of_neg hx hxy hz

lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z :=
  Real.rpow_le_rpow_of_nonpos hx hxy hz

lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  Real.rpow_lt_rpow_iff_of_neg hx hy hz

lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  Real.rpow_le_rpow_iff_of_neg hx hy hz

lemma le_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y :=
  Real.le_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_le_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z :=
  Real.rpow_inv_le_iff_of_pos x.2 hy hz

lemma lt_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  Real.lt_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_lt_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  Real.rpow_inv_lt_iff_of_pos x.2 hy hz

lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  Real.le_rpow_inv_iff_of_neg hx hy hz

lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  Real.lt_rpow_inv_iff_of_neg hx hy hz

lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  Real.rpow_inv_lt_iff_of_neg hx hy hz

lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  Real.rpow_inv_le_iff_of_neg hx hy hz

end

@[gcongr] theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

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

theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz

theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz

theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz

theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz

theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz

theorem rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, inv_mul_cancel₀ hx, rpow_one]⟩

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

lemma rpow_right_inj {y z : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  rw [← pos_iff_ne_zero] at hx₀
  rify at *
  grind [Real.rpow_right_inj]

lemma rpow_eq_rpow_right_iff {y z : ℝ} :
    x ^ y = x ^ z ↔ y = z ∨ x = 1 ∨ (x = 0 ∧ (y = 0 ↔ z = 0)) := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · obtain rfl | hz := eq_or_ne z 0
    · simp [zero_rpow_def]
    · simp +contextual [hz]
  obtain rfl | hx₁ := eq_or_ne x 1
  · simp
  simpa [hx₀, hx₁] using rpow_right_inj (y := y) (z := z) hx₀ hx₁

@[simp]
lemma rpow_eq_left_iff {y : ℝ} : x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y ≠ 0) := by
  simpa [or_left_comm] using rpow_eq_rpow_right_iff (x := x) (y := y) (z := 1)

theorem eq_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz]

theorem rpow_inv_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz]

@[simp] lemma rpow_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul, mul_inv_cancel₀ hy, rpow_one]

@[simp] lemma rpow_inv_rpow {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul, inv_mul_cancel₀ hy, rpow_one]

@[simp]
lemma rpow_rpow_inv_eq_iff {y : ℝ} : (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1 := by
  grind only [rpow_rpow_inv, rpow_zero]

@[simp]
lemma rpow_inv_rpow_eq_iff {y : ℝ} : (x ^ y⁻¹) ^ y = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]

theorem pow_rpow_inv_natCast (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← NNReal.coe_inj, coe_rpow, NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn

theorem rpow_inv_natCast_pow (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← NNReal.coe_inj, NNReal.coe_pow, coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn

theorem _root_.Real.toNNReal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y := by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow, Real.toNNReal_coe]

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0 => x ^ z :=
  fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h]

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

theorem _root_.Real.nnnorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

end NNReal

namespace ENNReal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0

noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp]
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [← none_eq_top]

theorem rpow_zero_pos (x : ℝ≥0∞) : 0 < x ^ (0 : ℝ) := by rw [rpow_zero]; exact one_pos

theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl

@[simp]
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]

@[simp]
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [asymm h, ne_of_gt h]

@[simp]
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h]

theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ := by
  rcases lt_trichotomy (0 : ℝ) y with (H | rfl | H)
  · simp [H, zero_rpow_of_pos]
  · simp
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * (0 : ℝ≥0∞) ^ y = (0 : ℝ≥0∞) ^ y := by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

@[norm_cast]
theorem coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) : (↑(x ^ y) : ℝ≥0∞) = x ^ y := by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]

@[norm_cast]
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : ↑(x ^ y) = (x : ℝ≥0∞) ^ y := by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _

theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else ↑(x ^ y) :=
  rfl

theorem rpow_ofNNReal {M : ℝ≥0} {P : ℝ} (hP : 0 ≤ P) : (M : ℝ≥0∞) ^ P = ↑(M ^ P) := by
  rw [ENNReal.coe_rpow_of_nonneg _ hP, ← ENNReal.rpow_eq_pow]

@[simp]
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_gt

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 := by
  rw [← coe_one, ← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

lemma rpow_eq_zero_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = 0 ↔ x = 0 := by
  simp [hy, hy.not_gt]

@[simp]
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]

lemma rpow_lt_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y < ∞ ↔ x < ∞ := by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]

theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ := by
  simp +contextual [ENNReal.rpow_eq_top_iff, hy0.not_gt]

-- This is an unsafe rule since we want to try `rpow_ne_top_of_ne_zero` if `y < 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg'` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem rpow_ne_top_of_nonneg' {y : ℝ} {x : ℝ≥0∞} (hx : 0 < x) (hx' : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  fun h ↦ by simp [rpow_eq_top_iff, hx.ne', hx'] at h

theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem rpow_ne_top_of_ne_zero {x : ℝ≥0∞} {y : ℝ} (hx : x ≠ 0) (hx' : x ≠ ⊤) : x ^ y ≠ ⊤ := by
  simp [rpow_eq_top_iff, hx, hx']

theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z := by
  cases x with
  | top => exact (h'x rfl).elim
  | coe x =>
    have : x ≠ 0 := fun h => by simp [h] at hx
    simp [← coe_rpow_of_ne_zero this, NNReal.rpow_add this]

theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl | hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl | hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

lemma rpow_add_of_add_pos {x : ℝ≥0∞} (hx : x ≠ ⊤) (y z : ℝ) (hyz : 0 < y + z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  obtain (rfl | hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by linarith
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]

theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]

theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]

theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]

theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero, h, this, NNReal.rpow_mul]

@[simp, norm_cast]
theorem rpow_natCast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_ne_zero _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

@[simp]
lemma rpow_ofNat (x : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (OfNat.ofNat n) :=
  rpow_natCast x n

@[simp, norm_cast]
lemma rpow_intCast (x : ℝ≥0∞) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2

theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_gt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_ge hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_gt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x
  · rcases hz with hz | hz <;> simp [hz, top_unique hxy]
  induction y
  · rw [ne_eq, coe_eq_zero] at hx0
    rcases hz with hz | hz <;> simp [*]
  simp only [*]
  norm_cast at *
  rw [← coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_rpow]
  norm_cast

theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

@[norm_cast]
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = (x : ℝ≥0∞) ^ z * (y : ℝ≥0∞) ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z

theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i ∈ s, (f i : ℝ≥0∞) ^ r = ((∏ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_gt, mul_rpow_eq_ite]

theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_ne_top h2f

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_gt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_rpow]

theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z := by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`. -/
@[simps! apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]

theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]
  rfl

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁

theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le

theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt

lemma max_rpow {x y : ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) : max x y ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]

theorem le_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul, @rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]

theorem rpow_inv_lt_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

theorem lt_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, @rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]

theorem rpow_inv_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

@[gcongr]
theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (lt_trans zero_lt_one hx).ne',
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos] <;>
    linarith
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [← coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]

theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le

theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z := by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le

theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos

theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p := by
  rcases lt_or_ge 0 p with hp_pos | hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]

theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]

theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := by
  cases x
  · simp [top_rpow_of_neg hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]

theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

@[simp] lemma toNNReal_rpow (x : ℝ≥0∞) (z : ℝ) : (x ^ z).toNNReal = x.toNNReal ^ z := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt H)]

theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_rpow, ENNReal.toNNReal_rpow]

theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero, coe_inj, Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]

theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

@[simp] lemma rpow_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul, mul_inv_cancel₀ hy, rpow_one]

@[simp] lemma rpow_inv_rpow {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul, inv_mul_cancel₀ hy, rpow_one]

@[simp]
lemma rpow_rpow_inv_eq_iff {x : ℝ≥0∞} {y : ℝ} : (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_zero, rpow_rpow_inv]

@[simp]
lemma rpow_inv_rpow_eq_iff {x : ℝ≥0∞} {y : ℝ} : (x ^ y⁻¹) ^ y = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]

lemma pow_rpow_inv_natCast {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← rpow_natCast, ← rpow_mul, mul_inv_cancel₀ (by positivity), rpow_one]

lemma rpow_inv_natCast_pow {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← rpow_natCast, ← rpow_mul, inv_mul_cancel₀ (by positivity), rpow_one]

lemma rpow_natCast_mul (x : ℝ≥0∞) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_mul_natCast (x : ℝ≥0∞) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_intCast_mul (x : ℝ≥0∞) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_mul_intCast (x : ℝ≥0∞) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Injective fun y : ℝ≥0∞ ↦ y ^ x :=
  HasLeftInverse.injective ⟨fun y ↦ y ^ x⁻¹, rpow_rpow_inv hx⟩

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  HasRightInverse.surjective ⟨fun y ↦ y ^ x⁻¹, rpow_inv_rpow hx⟩

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

lemma _root_.Real.enorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x ^ y‖ₑ = ‖x‖ₑ ^ y := by simp [enorm, nnnorm_rpow_of_nonneg hx, coe_rpow_of_nonneg _ hy]

lemma add_rpow_le_two_rpow_mul_rpow_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := calc
  (a + b) ^ p ≤ (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [max_rpow hp]
  _ ≤ 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp

end ENNReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- section Tactics

-- /-!
-- ## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-- -/


-- namespace NormNum

-- theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, NNReal.rpow_natCast]

-- theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_natCast]

-- theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, ENNReal.rpow_natCast]

-- theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_natCast]

-- /-- Evaluate `NNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))

-- /-- Evaluate `ENNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))

-- /-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_nnrpow_ennrpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | _ => tactic.failed

-- end NormNum

-- namespace Tactic

-- namespace Positivity

-- private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
--   NNReal.rpow_pos ha

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals.
-- -/
-- unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   match strictness_a with
--     | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
--     | _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0`
-- private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
--   ENNReal.rpow_pos_of_nonneg ha hb.le

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of extended
-- nonnegative reals. -/
-- unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   let strictness_b ← core b
--   match strictness_a, strictness_b with
--     | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
--     | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
--     | _, _ => failed

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

-- end Tactic

-- end Tactics

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `NNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : ℝ≥0) ^ (_ : ℝ)]
meta def evalNNRealRpow : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(NNReal.rpow_zero_pos $a))
  | 0, ~q(ℝ≥0), ~q($a ^ ($b : ℝ)) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa =>
        pure (.positive q(NNReal.rpow_pos $pa))
    | _ => pure (.nonnegative q(zero_le (a := $e)))
  | _, _, _ => throwError "not NNReal.rpow"

private meta def isFiniteM? (x : Q(ℝ≥0∞)) : MetaM (Option Q($x ≠ (⊤ : ℝ≥0∞))) := do
  let mvar ← mkFreshExprMVar q($x ≠ (⊤ : ℝ≥0∞))
  let save ← saveState
  let (goals, _) ← Elab.runTactic mvar.mvarId! <|← `(tactic| finiteness)
  if goals.isEmpty then
    pure <| some <|← instantiateMVars mvar
  else
    restoreState save
    pure none

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `ENNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : ℝ≥0∞) ^ (_ : ℝ)]
meta def evalENNRealRpow : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(ENNReal.rpow_zero_pos $a))
  | 0, ~q(ℝ≥0∞), ~q($a ^ ($b : ℝ)) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    let rb ← catchNone <| core q(inferInstance) q(inferInstance) b
    assertInstancesCommute
    match ra, rb with
    | .positive pa, .positive pb =>
        pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa <| le_of_lt $pb))
    | .positive pa, .nonnegative pb =>
        pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa $pb))
    | .positive pa, _ =>
        let some ha ← isFiniteM? a | pure <| .nonnegative q(zero_le (a := $e))
        pure <| .positive q(ENNReal.rpow_pos $pa $ha)
    | _, _ => pure <| .nonnegative q(zero_le (a := $e))
  | _, _, _ => throwError "not ENNReal.rpow"

end Mathlib.Meta.Positivity

/-!
## NormNum extension for NNReal powers
-/

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

theorem IsNat.nnreal_rpow_eq_nnreal_pow {b : ℝ} {n : ℕ} (h : IsNat b n) (a : ℝ≥0) :
    a ^ b = a ^ n := by
  rw [h.1, NNReal.rpow_natCast]

theorem IsInt.nnreal_rpow_eq_inv_nnreal_pow {b : ℝ} {n : ℕ} (h : IsInt b (.negOfNat n)) (a : ℝ≥0) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1, NNReal.rpow_intCast, Int.negOfNat_eq, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast]

theorem IsNat.nnreal_rpow_isNNRat {a : ℝ≥0} {b : ℝ} {m n d r : ℕ} (ha : IsNat a m)
    (hb : IsNNRat b n d) (k : ℕ) (hr : r ^ d = k) (l : ℕ) (hm : m ^ n = l) (hkl : k = l) :
    IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d ≠ 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl, div_eq_mul_inv, NNReal.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
    Nat.cast_pow, NNReal.pow_rpow_inv_natCast]
  positivity

theorem IsNNRat.nnreal_rpow_isNNRat (a : ℝ≥0) (b : ℝ) (na da : ℕ) (ha : IsNNRat a na da)
    (nr dr : ℕ) (hnum : IsNat ((na : ℝ≥0) ^ b) nr) (hden : IsNat ((da : ℝ≥0) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : ℝ≥0) nr dr by
    simpa [ha.to_eq, NNReal.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  simp [← hden.1, ha.den_nz]

theorem nnreal_rpow_isRat_eq_inv_nnreal_rpow (a : ℝ≥0) (b : ℝ) (n d : ℕ)
    (hb : IsRat b (Int.negOfNat n) d) : a ^ b = (a⁻¹) ^ (n / d : ℝ) := by
  rw [NNReal.inv_rpow, ← NNReal.rpow_neg, hb.neg_to_eq rfl rfl]

open Lean

/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatNNRealRPowIsNNRat
    (a : Q(ℝ≥0)) (na : Q(ℕ)) (pa : Q(IsNat $a $na))
    (b : Q(ℝ)) (nb db : Q(ℕ)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (ℕ × Σ r : Q(ℕ), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(ℕ) := mkRawNatLit r
  -- avoid evaluating powers in kernel
  let .some ⟨c, pc⟩ ← liftM <| OptionT.run <| evalNatPow er db | failure
  let .some ⟨d, pd⟩ ← liftM <| OptionT.run <| evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.nnreal_rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a : ℝ≥0` and `b : ℝ`.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers.
-/
@[norm_num (_ : ℝ≥0) ^ (_ : ℝ)]
meta def evalNNRealRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(ℝ≥0), ~q(($a : ℝ≥0)^($b : ℝ)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.nnreal_rpow_eq_nnreal_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.nnreal_rpow_eq_inv_nnreal_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatNNRealRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.nnreal_rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : ℝ))
      assumeInstancesCommute
      return .eqTrans q(nnreal_rpow_isRat_eq_inv_nnreal_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum
