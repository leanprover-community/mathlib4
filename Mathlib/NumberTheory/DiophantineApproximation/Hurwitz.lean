/-
Copyright (c) 2026 Yuanxia Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanxia Xu
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime

/-!
# Hurwitz's Theorem in Diophantine Approximation

This file proves **Hurwitz's approximation theorem**: if $\xi$ is an irrational real number, then
there are infinitely many irreducible rationals $x/y$ such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{\sqrt{5}\,y^2} \,.$$

This strengthens the corresponding `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
(Dirichlet's Theorem) with constant $1$ proved in
`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`. In fact the constant $\sqrt 5$ is
best possible, with the golden ratio being a counterexample for larger constants.

The proof avoids continued fractions entirely, instead using *Farey brackets*, which are pairs of
rationals $\frac{p}{q} < \xi < \frac{r}{s}$ with $qr - ps = 1$. We can show that at least one of
$\frac{p}{q}$, $\frac{r}{s}$ and the mediant $\frac{p+r}{q+s}$ satisfies the bound, and by
repeatedly constructing smaller intervals around $\xi$, infinitude is achieved.

## Main definitions

* `Real.Hurwitz.IsFarey`, defining a Farey interval on 4 integers `p, q, r, s` such that `0 < q, s`
  and `p/q < ξ < r/s` with `q*r - p*s = 1`.

* `Real.Hurwitz.IsGoodApprox` defines a good approximation as one satisfying the Hurwitz bound
  without using division for simplicity.

## Main statements

* `Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational`, which states that
  for irrational `ξ` the set `{q : ℚ | |ξ - q| < 1/(√5 * q.den^2)}` is infinite.

## Implementation notes

We use the namespace `Real` for the main result and a secondary namespace `Real.Hurwitz` for the
technical auxiliary lemmas, and a further `IsFarey` namespace is used to contain theorems regarding
Farey brackets and mediants, following the pattern of `Real.ContfracLegendre` in
`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`.

Intermediate lemmas are stated in the division-free form `|y*ξ - x| * y * √5 < 1` rather than
`|ξ - x/y| < 1/(√5*y^2)`, which is substantially easier to manipulate. The two are related by
`Real.Hurwitz.isGoodApprox_div_bound`.

## References

* <https://en.wikipedia.org/wiki/Hurwitz%27s_theorem_(number_theory)>

## Tags

Diophantine approximation, Hurwitz's theorem, Farey sequence, Stern-Brocot tree, mediant
-/

@[expose] public section

namespace Real

variable {ξ : ℝ}

namespace Hurwitz

/-- `IsFarey ξ p q r s` means `p/q < ξ < r/s` with `q * r - p * s = 1`. The determinant/
unimodularity condition ensures the mediant `(p + r) / (q + s)` creates a valid interval
with each endpoint. -/
structure IsFarey (ξ : ℝ) (p q r s : ℤ) : Prop where
  /-- Left denominator is positive. -/
  q_pos : 0 < q
  /-- Right denominator is positive. -/
  s_pos : 0 < s
  /-- Unimodularity condition. -/
  det   : q * r - p * s = 1
  /-- p/q is a lower bound for ξ. -/
  left  : (p : ℝ) / q < ξ
  /-- r/s is an upper bound for ξ. -/
  right : ξ < (r : ℝ) / s

/-- Divisionless reformulation of Hurwitz bound |ξ - x/y| < 1/(√5y²). -/
def IsGoodApprox (ξ : ℝ) (x y : ℤ) : Prop :=
  0 < y ∧ |(y : ℝ) * ξ - x| * y * √5 < 1

-- Frequently used lemmas about sqrt 5
private lemma sq_sqrt_five : √5 ^ 2 = 5 := sq_sqrt (by norm_num)

private lemma two_lt_sqrt_five : 2 < √5 := by
  nlinarith [sq_sqrt_five, sqrt_nonneg 5]

private theorem irrational_sqrt_five : Irrational (√5) := by
  have h : Nat.Prime 5 := by norm_num
  exact h.irrational_sqrt

-- A lemma to bound the denominators of a Farey interval given both endpoints fail the Hurwitz bound
private theorem aux₀ {a b c d : ℤ}
    (hdet : b * c - a * d = 1)
    (hA : 1 ≤ √5 * b * ((b : ℝ) * ξ - a))
    (hB : 1 ≤ √5 * d * ((c : ℝ) - d * ξ)) :
    (b : ℝ) ^ 2 + (d : ℝ) ^ 2 ≤ √5 * (b * d) := by
  have hdetR : (b : ℝ) * c - a * d = 1 := mod_cast hdet
  have hdiff : (d : ℝ) * (b * ξ - a) + b * (c - d * ξ) = 1 := by linear_combination hdetR
  have H : (d : ℝ) ^ 2 * √5 * b * (b * ξ - a) +
            b ^ 2 * √5 * d * (c - d * ξ) = √5 * b * d := by
    linear_combination hdiff * (√5 * b * d)
  have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg (d : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hB (sq_nonneg (b : ℝ))
  linarith

/- Another lemma used to bound the denominators of a Farey interval given the first,
which can be used both ways to derive a contradiction -/
private theorem aux₁ {b d : ℝ}
    (hb : 0 < b) (h : b ^ 2 + d ^ 2 ≤ √5 * (b * d)) :
    (√5 - 1) * b ≤ 2 * d ∧ 2 * d ≤ (√5 + 1) * b := by
  have hprod : (2 * d - (√5 - 1) * b) * (2 * d - (√5 + 1) * b) ≤ 0 := by
    nlinarith [sq_sqrt_five, two_lt_sqrt_five]
  constructor <;> nlinarith

private theorem aux₁' {b d : ℝ}
    (hd : 0 < d) (h : b ^ 2 + d ^ 2 ≤ √5 * (b * d)) :
    (√5 - 1) * d ≤ 2 * b ∧ 2 * b ≤ (√5 + 1) * d := by
  apply aux₁ hd
  linarith

/-! ### Bridging `IsGoodApprox` to `aux₀` hypotheses -/

private lemma one_le_of_not_isGoodApprox {x y : ℤ} (hy : 0 < y) (h : ¬ IsGoodApprox ξ x y) :
    1 ≤ |(y : ℝ) * ξ - x| * y * √5 := by
  rw [IsGoodApprox, not_and, not_lt] at h
  exact h hy

private lemma sqrt_five_mul_le_of_not_isGoodApprox_left {a b : ℤ} (hb : 0 < b)
    (hlt : (a : ℝ) / b < ξ) (h : 1 ≤ |(b : ℝ) * ξ - a| * b * √5) :
    1 ≤ √5 * b * ((b : ℝ) * ξ - a) := by
  have hbR : 0 < (b : ℝ) := mod_cast hb
  have hpos: 0 < (b : ℝ) * ξ - a := by
    rw [div_lt_iff₀ hbR] at hlt
    linarith
  rw [abs_of_pos hpos] at h
  linarith

private lemma sqrt_five_mul_le_of_not_isGoodApprox_right {c d : ℤ} (hd : 0 < d)
    (hgt : ξ < (c : ℝ) / d) (h : 1 ≤ |(d : ℝ) * ξ - c| * d * √5) :
    1 ≤ √5 * d * ((c : ℝ) - d * ξ) := by
  have hdR : 0 < (d : ℝ) := mod_cast hd
  have hneg : (d : ℝ) * ξ - c < 0 := by
    rw [lt_div_iff₀ hdR] at hgt
    linarith
  rw [abs_of_neg hneg] at h
  linarith

/-! ### Important contradiction -/

private lemma two_mul_ne_sqrt_five_sub_one_mul {b d : ℤ} (hb : 0 < b)
    (h : 2 * (d : ℝ) = (√5 - 1) * b) : False := by
  refine irrational_sqrt_five ⟨(2 * d + b) / b, ?_⟩
  have hb0 : (b : ℝ) ≠ 0 := mod_cast (ne_of_gt hb)
  push_cast
  rw [div_eq_iff hb0]
  linear_combination h

/-! ### Mediant properties -/

private lemma sub_eq_one_div_mul {p q r s : ℤ} (hq : 0 < q) (hs : 0 < s)
    (hdet : q * r - p * s = 1) :
    (r : ℝ) / s - p / q = 1 / ((q : ℝ) * s) := by
  have hqR : (0 : ℝ) < q := mod_cast hq
  have hsR : (0 : ℝ) < s := mod_cast hs
  have hdetR : (q : ℝ) * r - p * s = 1 := mod_cast hdet
  field_simp
  linear_combination hdetR

private lemma left_lt_mediant {p q r s : ℤ} (hq : 0 < q) (hs : 0 < s)
    (hdet : q * r - p * s = 1) :
    (p : ℝ) / q < ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) := by
  have hqR : (0 : ℝ) < q := mod_cast hq
  have hsR : (0 : ℝ) < s := mod_cast hs
  have hqsR : (0 : ℝ) < q + s := by linarith
  have hdetR : (q : ℝ) * r - p * s = 1 := mod_cast hdet
  push_cast
  rw [div_lt_div_iff₀ hqR hqsR]
  linarith

private lemma mediant_lt_right {p q r s : ℤ} (hq : 0 < q) (hs : 0 < s)
    (hdet : q * r - p * s = 1) :
    ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) < (r : ℝ) / s := by
  have hqR : (0 : ℝ) < q := mod_cast hq
  have hsR : (0 : ℝ) < s := mod_cast hs
  have hqsR : (0 : ℝ) < q + s := by linarith
  have hdetR : (q : ℝ) * r - p * s = 1 := mod_cast hdet
  push_cast
  rw [div_lt_div_iff₀ hqsR hsR]
  linarith

private lemma ne_mediant (hξ : Irrational ξ) {p q r s : ℤ} :
    ξ ≠ ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) := by
  have hcast : ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ)
      = (((p + r : ℤ) / (q + s : ℤ) : ℚ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  exact hξ.ne_rat _


namespace IsFarey

private theorem of_lt_mediant {p q r s : ℤ} (h : IsFarey ξ p q r s)
    (hm : ξ < ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ)) :
    IsFarey ξ p q (p + r) (q + s) where
  q_pos := h.q_pos
  s_pos := add_pos h.q_pos h.s_pos
  det := by linear_combination h.det
  left := h.left
  right := hm

private theorem of_mediant_lt {p q r s : ℤ} (h : IsFarey ξ p q r s)
    (hm : ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) < ξ) :
    IsFarey ξ (p + r) (q + s) r s where
  q_pos := add_pos h.q_pos h.s_pos
  s_pos := h.s_pos
  det := by linear_combination h.det
  left := hm
  right := h.right


/-! ### Key step: one of three consecutive Farey endpoints is good -/

private theorem abs_sub_left_lt {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    |ξ - (p : ℝ) / q| < 1 / ((q : ℝ) * s) := by
  have hpos : ξ - (p : ℝ) / q > 0 := by linarith [h.left]
  rw [abs_of_pos hpos, ← sub_eq_one_div_mul h.q_pos h.s_pos h.det]
  linarith [h.right]

private theorem abs_sub_right_lt {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    |ξ - (r : ℝ) / s| < 1 / ((q : ℝ) * s) := by
  have hneg : ξ - (r : ℝ) / s < 0 := by linarith [h.right]
  rw [abs_of_neg hneg, ← sub_eq_one_div_mul h.q_pos h.s_pos h.det]
  linarith [h.left]

private theorem abs_sub_mediant_lt {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    |ξ - ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ)| < 1 / ((q : ℝ) * s) := by
  rw [abs_sub_lt_iff, ← sub_eq_one_div_mul h.q_pos h.s_pos h.det]
  constructor
  · linarith [h.right, left_lt_mediant h.q_pos h.s_pos h.det]
  · linarith [h.left, mediant_lt_right h.q_pos h.s_pos h.det]

/-- If `IsFarey ξ p q r s`, then at least one of `p/q`, `r/s`, and the mediant
`(p + r)/(q + s)` satisfies the Hurwitz bound. -/
theorem isGoodApprox_or (hξ : Irrational ξ) {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    IsGoodApprox ξ p q ∨ IsGoodApprox ξ r s ∨ IsGoodApprox ξ (p + r) (q + s) := by
  by_contra hcon
  push Not at hcon
  rcases hcon with ⟨h1, h2, h3⟩
  have hqs_pos : 0 < q + s := add_pos h.q_pos h.s_pos
  have hqR : 0 < (q : ℝ) := mod_cast h.q_pos
  have hsR : 0 < (s : ℝ) := mod_cast h.s_pos
  -- Inequalities
  have hn1 := one_le_of_not_isGoodApprox h.q_pos h1
  have hn2 := one_le_of_not_isGoodApprox h.s_pos h2
  have hn3 := one_le_of_not_isGoodApprox hqs_pos h3
  -- Hypotheses for aux₀
  have hA := sqrt_five_mul_le_of_not_isGoodApprox_left h.q_pos h.left hn1
  have hB := sqrt_five_mul_le_of_not_isGoodApprox_right h.s_pos h.right hn2
  have H1 := aux₀ h.det hA hB
  -- Split depending on mediant
  have hne : ξ ≠ ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) := ne_mediant hξ
  rcases hne.lt_or_gt with hm | hm
  · -- ξ < (p + r) / (q + s)
    have h' := h.of_lt_mediant hm
    obtain ⟨H2, _⟩ := aux₁ hqR H1
    have H1' := aux₀ h'.det hA (sqrt_five_mul_le_of_not_isGoodApprox_right hqs_pos h'.right hn3)
    obtain ⟨_, H2'⟩ := aux₁ hqR H1'
    push_cast at H2'
    have heq : 2 * s = (√5 - 1) * q := by linarith
    exact two_mul_ne_sqrt_five_sub_one_mul h.q_pos heq
  · -- (p + r) / (q + s) < ξ
    have h' := h.of_mediant_lt hm
    obtain ⟨H2, _⟩ := aux₁' hsR H1
    have H1' := aux₀ h'.det (sqrt_five_mul_le_of_not_isGoodApprox_left hqs_pos h'.left hn3) hB
    obtain ⟨_, H2'⟩ := aux₁' hsR H1'
    push_cast at H2'
    have heq : 2 * q = (√5 - 1) * s := by linarith
    exact two_mul_ne_sqrt_five_sub_one_mul h.s_pos heq

/-- If `IsFarey ξ p q r s`, then there exists a good approximation to `ξ` closer than the width of
the bracket. -/
theorem exists_isGoodApprox (hξ : Irrational ξ) {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    ∃ x y : ℤ, IsGoodApprox ξ x y ∧ |ξ - (x : ℝ) / y| < 1 / ((q : ℝ) * s) := by
  rcases h.isGoodApprox_or hξ with hg | hg | hg
  · exact ⟨p, q, hg, h.abs_sub_left_lt⟩
  · exact ⟨r, s, hg, h.abs_sub_right_lt⟩
  · exact ⟨p + r, q + s, hg, h.abs_sub_mediant_lt⟩

private theorem exists_next (hξ : Irrational ξ) {p q r s : ℤ} (h : IsFarey ξ p q r s) :
    ∃ p' q' r' s' : ℤ, IsFarey ξ p' q' r' s' ∧ q + s < q' + s' := by
  have hne : ξ ≠ ((p + r : ℤ) : ℝ) / ((q + s : ℤ) : ℝ) := ne_mediant hξ
  rcases hne.lt_or_gt with hm | hm
  · exact ⟨p, q, p + r, q + s, h.of_lt_mediant hm, by linarith [h.q_pos]⟩
  · exact ⟨p + r, q + s, r, s, h.of_mediant_lt hm, by linarith [h.s_pos]⟩

end IsFarey

/-! ### Generating brackets of arbitrarily large denominators -/

private theorem isFarey_floor (hξ : Irrational ξ) : IsFarey ξ ⌊ξ⌋ 1 (⌊ξ⌋ + 1) 1 where
  q_pos := one_pos
  s_pos := one_pos
  det := by ring
  left := by
    push_cast
    rw [div_one]
    exact ((hξ.ne_int _).symm).lt_of_le (Int.floor_le ξ)
  right := by
    push_cast
    rw [div_one]
    exact Int.lt_floor_add_one ξ

/-- Farey brackets around `ξ` with arbitrarily large denominator sum `q + s`
(and therefore arbitrarily small width) exist. -/
theorem exists_isFarey_large (hξ : Irrational ξ) (n : ℕ) :
    ∃ p q r s : ℤ, IsFarey ξ p q r s ∧ (n : ℤ) ≤ q + s := by
  induction n with
  | zero => exact ⟨⌊ξ⌋, 1, (⌊ξ⌋ + 1), 1, isFarey_floor hξ, by norm_num⟩
  | succ n ih =>
    obtain ⟨p, q, r, s, h, hn⟩ := ih
    obtain ⟨p', q', r', s', h', hlt⟩ := h.exists_next hξ
    exact ⟨p', q', r', s', h', by omega⟩


/-! ### From ℤ to ℚ, and infinitude -/

private lemma isGoodApprox_div_bound {x y : ℤ} (hg : IsGoodApprox ξ x y) :
    |ξ - (x : ℝ) / y| < 1 / (√5 * (y : ℝ) ^ 2) := by
  obtain ⟨hpos, hmul⟩ := hg
  have hposR : 0 < (y : ℝ) := mod_cast hpos
  have h : ξ - (x : ℝ) / y = ((y : ℝ) * ξ - x) / y := by field_simp
  rw [h, abs_div, abs_of_pos hposR, div_lt_div_iff₀ hposR (by positivity)]
  nlinarith

private lemma isGoodApprox_bound_rat {x y : ℤ} (hg : IsGoodApprox ξ x y) :
    |ξ - (((x : ℚ) / y : ℚ) : ℝ)| < 1 / (√5 * (((x : ℚ) / y : ℚ).den : ℝ) ^ 2) := by
  have ⟨hy_pos, _⟩ := hg
  set q : ℚ := (x : ℚ) / y with hq
  have hden_dvd : (q.den : ℤ) ∣ y := by
    rw [hq]
    norm_cast
    exact Rat.den_dvd x y
  have hden_le : (q.den : ℝ) ≤ (y : ℝ) := mod_cast (Int.le_of_dvd hy_pos hden_dvd)
  have hden_pos : 0 < (q.den : ℝ) := mod_cast q.pos
  have hcast : q = (x : ℝ) / y := by
    rw [hq]
    norm_cast
  rw [hcast]
  refine lt_of_lt_of_le (isGoodApprox_div_bound hg) ?_
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : (q.den : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ hden_pos.le hden_le
  have h5 : (0 : ℝ) < √5 := by linarith [two_lt_sqrt_five]
  nlinarith

private lemma add_le_two_mul_mul {q s : ℤ} (hq : 0 < q) (hs : 0 < s) :
    q + s ≤ 2 * (q * s) := by nlinarith

/-- Given any rational `t`, there is a rational `t'` satisfying the Hurwitz bound
that is strictly closer to `ξ` than `t` is. -/
theorem exists_rat_isGoodApprox_and_lt (hξ : Irrational ξ) (t : ℚ) :
    ∃ t' : ℚ, |ξ - t'| < 1 / (√5 * (t'.den : ℝ) ^ 2) ∧ |ξ - t'| < |ξ - t| := by
  have hpos := abs_pos.mpr (sub_ne_zero.mpr (hξ.ne_rat t))
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / |ξ - (t : ℝ)|)
  obtain ⟨p, q, r, s, hF, hqs⟩ := exists_isFarey_large hξ n
  obtain ⟨x, y, hgood, hbound⟩ := hF.exists_isGoodApprox hξ
  refine ⟨(x : ℚ) / (y : ℚ), isGoodApprox_bound_rat hgood, ?_⟩
  have hqs_ge : (q : ℝ) + s ≤ 2 * ((q : ℝ) * s) := mod_cast (add_le_two_mul_mul hF.q_pos hF.s_pos)
  have hcast : (n : ℝ) ≤ (q : ℝ) + s := mod_cast hqs
  have hn' : (2 : ℝ) < ((q : ℝ) + s) * |ξ - (t : ℝ)| := by
    have hn'' := hn.trans_le hcast
    rw [div_lt_iff₀ hpos] at hn''
    linarith
  have hcast' : ((((x : ℚ) / (y : ℚ)) : ℚ) : ℝ) = (x : ℝ) / (y : ℝ) := by norm_cast
  rw [hcast']
  have hqsR : 0 < (q : ℝ) * s := mod_cast (mul_pos hF.q_pos hF.s_pos)
  have hfinal : 1 / ((q : ℝ) * s) < |ξ - (t : ℝ)| := by
    rw [div_lt_iff₀ hqsR]
    nlinarith
  exact lt_trans hbound hfinal

end Hurwitz

/-- **Hurwitz's theorem.** For irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/(√5*q.den^2)}`
is infinite. -/
theorem infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational (hξ : Irrational ξ) :
    {t : ℚ | |ξ - t| < 1 / (√5 * (t.den : ℝ) ^ 2)}.Infinite := by
  have hne : {t : ℚ | |ξ - t| < 1 / (√5 * (t.den : ℝ) ^ 2)}.Nonempty := by
    obtain ⟨t', hgood', _⟩ := Hurwitz.exists_rat_isGoodApprox_and_lt hξ 0
    use t', hgood'
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨t₀, _, ht₀⟩ :=
    Set.exists_min_image _ (fun t : ℚ => |ξ - (t : ℝ)|) h hne
  obtain ⟨t, ht_good, hbetter⟩ := Hurwitz.exists_rat_isGoodApprox_and_lt hξ t₀
  exact lt_irrefl _ (lt_of_le_of_lt (ht₀ t ht_good) hbetter)

end Real
