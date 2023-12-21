/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Heather Macbeth
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

#align_import analysis.convex.specific_functions.basic from "leanprover-community/mathlib"@"8f9fea08977f7e450770933ee6abb20733b47c92"

/-!
# Collection of convex functions

In this file we prove that the following functions are convex or strictly convex:

* `strictConvexOn_exp` : The exponential function is strictly convex.
* `Even.convexOn_pow`: For an even `n : ℕ`, `fun x ↦ x ^ n` is convex.
* `convexOn_pow`: For `n : ℕ`, `fun x ↦ x ^ n` is convex on $[0, +∞)$.
* `convexOn_zpow`: For `m : ℤ`, `fun x ↦ x ^ m` is convex on $[0, +∞)$.
* `strictConcaveOn_log_Ioi`, `strictConcaveOn_log_Iio`: `Real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.
* `convexOn_rpow`, `strictConvexOn_rpow` : For `p : ℝ`, `fun x ↦ x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.

The proofs in this file are deliberately elementary, *not* by appealing to the sign of the second
derivative.  This is in order to keep this file early in the import hierarchy, since it is on the
path to Hölder's and Minkowski's inequalities and after that to Lp spaces and most of measure
theory.

## TODO

For `p : ℝ`, prove that `fun x ↦ x ^ p` is concave when `0 ≤ p ≤ 1` and strictly concave when
`0 < p < 1`.
-/

open Real Set BigOperators NNReal

/-- `Real.exp` is strictly convex on the whole real line.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
theorem strictConvexOn_exp : StrictConvexOn ℝ univ exp := by
  apply strictConvexOn_of_slope_strict_mono_adjacent convex_univ
  rintro x y z - - hxy hyz
  trans exp y
  · have h1 : 0 < y - x := by linarith
    have h2 : x - y < 0 := by linarith
    rw [div_lt_iff h1]
    calc
      exp y - exp x = exp y - exp y * exp (x - y) := by rw [← exp_add]; ring_nf
      _ = exp y * (1 - exp (x - y)) := by ring
      _ < exp y * -(x - y) := by gcongr; linarith [add_one_lt_exp_of_nonzero h2.ne]
      _ = exp y * (y - x) := by ring
  · have h1 : 0 < z - y := by linarith
    rw [lt_div_iff h1]
    calc
      exp y * (z - y) < exp y * (exp (z - y) - 1) := by
        gcongr _ * ?_
        linarith [add_one_lt_exp_of_nonzero h1.ne']
      _ = exp (z - y) * exp y - exp y := by ring
      _ ≤ exp z - exp y := by rw [← exp_add]; ring_nf; rfl
#align strict_convex_on_exp strictConvexOn_exp

/-- `Real.exp` is convex on the whole real line. -/
theorem convexOn_exp : ConvexOn ℝ univ exp :=
  strictConvexOn_exp.convexOn
#align convex_on_exp convexOn_exp

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
theorem convexOn_pow (n : ℕ) : ConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n := by
  induction' n with k IH
  · exact convexOn_const (1 : ℝ) (convex_Ici _)
  refine' ⟨convex_Ici _, _⟩
  rintro a (ha : 0 ≤ a) b (hb : 0 ≤ b) μ ν hμ hν h
  have H := IH.2 ha hb hμ hν h
  have : 0 ≤ (b ^ k - a ^ k) * (b - a) * μ * ν := by
    cases' le_or_lt a b with hab hab
    · have : a ^ k ≤ b ^ k := by gcongr
      have : 0 ≤ (b ^ k - a ^ k) * (b - a) := by nlinarith
      positivity
    · have : b ^ k ≤ a ^ k := by gcongr
      have : 0 ≤ (b ^ k - a ^ k) * (b - a) := by nlinarith
      positivity
  calc
    (μ * a + ν * b) ^ k.succ = (μ * a + ν * b) * (μ * a + ν * b) ^ k := pow_succ _ _
    _ ≤ (μ * a + ν * b) * (μ * a ^ k + ν * b ^ k) := by gcongr; exact H
    _ ≤ (μ * a + ν * b) * (μ * a ^ k + ν * b ^ k) + (b ^ k - a ^ k) * (b - a) * μ * ν := by linarith
    _ = (μ + ν) * (μ * a ^ k.succ + ν * b ^ k.succ) := by rw [Nat.succ_eq_add_one]; ring
    _ = μ * a ^ k.succ + ν * b ^ k.succ := by rw [h]; ring
#align convex_on_pow convexOn_pow

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
nonrec theorem Even.convexOn_pow {n : ℕ} (hn : Even n) :
    ConvexOn ℝ Set.univ fun x : ℝ => x ^ n := by
  refine' ⟨convex_univ, _⟩
  rintro a - b - μ ν hμ hν h
  obtain ⟨k, rfl⟩ := hn.exists_two_nsmul _
  -- Porting note: added type ascription to LHS
  have : (0 : ℝ) ≤ (a - b) ^ 2 * μ * ν := by positivity
  calc
    (μ * a + ν * b) ^ (2 * k) = ((μ * a + ν * b) ^ 2) ^ k := by rw [pow_mul]
    _ ≤ ((μ + ν) * (μ * a ^ 2 + ν * b ^ 2)) ^ k := by gcongr; linarith
    _ = (μ * a ^ 2 + ν * b ^ 2) ^ k := by rw [h]; ring
    _ ≤ μ * (a ^ 2) ^ k + ν * (b ^ 2) ^ k := ?_
    _ ≤ μ * a ^ (2 * k) + ν * b ^ (2 * k) := by ring_nf; rfl
  -- Porting note: `rw [mem_Ici]` was `dsimp`
  refine' (convexOn_pow k).2 _ _ hμ hν h <;> rw [mem_Ici] <;> positivity
#align even.convex_on_pow Even.convexOn_pow

open Int in
/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
theorem convexOn_zpow : ∀ m : ℤ, ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ m
  | (n : ℕ) => by
    simp_rw [zpow_ofNat]
    exact (convexOn_pow n).subset Ioi_subset_Ici_self (convex_Ioi _)
  | -[n+1] => by
    simp_rw [zpow_negSucc]
    refine' ⟨convex_Ioi _, _⟩
    rintro a (ha : 0 < a) b (hb : 0 < b) μ ν hμ hν h
    field_simp
    rw [div_le_div_iff]
    · -- Porting note: added type ascription to LHS
      calc
        (1 : ℝ) * (a ^ (n + 1) * b ^ (n + 1)) = ((μ + ν) ^ 2 * (a * b)) ^ (n + 1) := by rw [h]; ring
        _ ≤ ((μ * b + ν * a) * (μ * a + ν * b)) ^ (n + 1) := ?_
        _ = (μ * b + ν * a) ^ (n + 1) * (μ * a + ν * b) ^ (n + 1) := by rw [mul_pow]
        _ ≤ (μ * b ^ (n + 1) + ν * a ^ (n + 1)) * (μ * a + ν * b) ^ (n + 1) := ?_
      · -- Porting note: added type ascription to LHS
        gcongr (?_ : ℝ) ^ _
        have : (0 : ℝ) ≤ μ * ν * (a - b) ^ 2 := by positivity
        linarith
      · gcongr
        apply (convexOn_pow (n + 1)).2 hb.le ha.le hμ hν h
    · have : 0 < μ * a + ν * b := by cases le_or_lt a b <;> nlinarith
      positivity
    · positivity
#align convex_on_zpow convexOn_zpow

/- `Real.log` is strictly concave on $(0, +∞)$.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log := by
  apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi (0 : ℝ))
  rintro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  trans y⁻¹
  · have h : 0 < z - y := by linarith
    rw [div_lt_iff h]
    have hyz' : 0 < z / y := by positivity
    have hyz'' : z / y ≠ 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      log z - log y = log (z / y) := by rw [← log_div hz.ne' hy.ne']
      _ < z / y - 1 := (log_lt_sub_one_of_pos hyz' hyz'')
      _ = y⁻¹ * (z - y) := by field_simp
  · have h : 0 < y - x := by linarith
    rw [lt_div_iff h]
    have hxy' : 0 < x / y := by positivity
    have hxy'' : x / y ≠ 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      y⁻¹ * (y - x) = 1 - x / y := by field_simp
      _ < -log (x / y) := by linarith [log_lt_sub_one_of_pos hxy' hxy'']
      _ = -(log x - log y) := by rw [log_div hx.ne' hy.ne']
      _ = log y - log x := by ring
#align strict_concave_on_log_Ioi strictConcaveOn_log_Ioi

/-- **Bernoulli's inequality** for real exponents, strict version: for `1 < p` and `-1 ≤ s`, with
`s ≠ 0`, we have `1 + p * s < (1 + s) ^ p`. -/
theorem one_add_mul_self_lt_rpow_one_add {s : ℝ} (hs : -1 ≤ s) (hs' : s ≠ 0) {p : ℝ} (hp : 1 < p) :
    1 + p * s < (1 + s) ^ p := by
  rcases eq_or_lt_of_le hs with (rfl | hs)
  · have : p ≠ 0 := by positivity
    simpa [zero_rpow this]
  have hs1 : 0 < 1 + s := by linarith
  cases' le_or_lt (1 + p * s) 0 with hs2 hs2
  · exact hs2.trans_lt (rpow_pos_of_pos hs1 _)
  rw [rpow_def_of_pos hs1, ← exp_log hs2]
  apply exp_strictMono
  have hp : 0 < p := by positivity
  have hs3 : 1 + s ≠ 1 := by contrapose! hs'; linarith
  have hs4 : 1 + p * s ≠ 1 := by contrapose! hs'; nlinarith
  cases' lt_or_gt_of_ne hs' with hs' hs'
  · rw [← div_lt_iff hp, ← div_lt_div_right_of_neg hs']
    -- Porting note: previously we could write `zero_lt_one` inline,
    -- but now Lean doesn't guess we are talking about `1` fast enough.
    haveI : (1 : ℝ) ∈ Ioi 0 := zero_lt_one
    convert strictConcaveOn_log_Ioi.secant_strict_mono this hs2 hs1 hs4 hs3 _ using 1
    · field_simp
    · field_simp
    · nlinarith
  · rw [← div_lt_iff hp, ← div_lt_div_right hs']
    -- Porting note: previously we could write `zero_lt_one` inline,
    -- but now Lean doesn't guess we are talking about `1` fast enough.
    haveI : (1 : ℝ) ∈ Ioi 0 := zero_lt_one
    convert strictConcaveOn_log_Ioi.secant_strict_mono this hs1 hs2 hs3 hs4 _ using 1
    · field_simp
    · field_simp
    · nlinarith
#align one_add_mul_self_lt_rpow_one_add one_add_mul_self_lt_rpow_one_add

/-- **Bernoulli's inequality** for real exponents, non-strict version: for `1 ≤ p` and `-1 ≤ s`
we have `1 + p * s ≤ (1 + s) ^ p`. -/
theorem one_add_mul_self_le_rpow_one_add {s : ℝ} (hs : -1 ≤ s) {p : ℝ} (hp : 1 ≤ p) :
    1 + p * s ≤ (1 + s) ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le
#align one_add_mul_self_le_rpow_one_add one_add_mul_self_le_rpow_one_add

/- For `p : ℝ` with `1 < p`, `fun x ↦ x ^ p` is strictly convex on $[0, +∞)$.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
theorem strictConvexOn_rpow {p : ℝ} (hp : 1 < p) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ p := by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : ℝ))
  rintro x y z (hx : 0 ≤ x) (hz : 0 ≤ z) hxy hyz
  have hy : 0 < y := by linarith
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _
  have H1 : y ^ (p - 1 + 1) = y ^ (p - 1) * y := rpow_add_one hy.ne' _
  ring_nf at H1
  trans p * y ^ (p - 1)
  · have h3 : 0 < y - x := by linarith only [hxy]
    have hyx'' : x / y < 1 := by rwa [div_lt_one hy]
    have hyx''' : x / y - 1 < 0 := by linarith only [hyx'']
    have hyx'''' : 0 ≤ x / y := by positivity
    have hyx''''' : -1 ≤ x / y - 1 := by linarith only [hyx'''']
    have : 1 - (1 + (x / y - 1)) ^ p < -p * (x / y - 1) := by
      linarith [one_add_mul_self_lt_rpow_one_add hyx''''' hyx'''.ne hp]
    rw [div_lt_iff h3, ← div_lt_div_right hy']
    convert this using 1
    · have H : (x / y) ^ p = x ^ p / y ^ p := div_rpow hx hy.le _
      ring_nf at H ⊢
      field_simp at H ⊢
      linear_combination H
    · ring_nf at H1 ⊢
      field_simp
      linear_combination p * (-y + x) * H1
  · have hyz' : 0 < z - y := by linarith only [hyz]
    have hyz'' : 1 < z / y := by rwa [one_lt_div hy]
    have hyz''' : 0 < z / y - 1 := by linarith only [hyz'']
    have hyz'''' : -1 ≤ z / y - 1 := by linarith only [hyz'']
    have : p * (z / y - 1) < (1 + (z / y - 1)) ^ p - 1 := by
      linarith [one_add_mul_self_lt_rpow_one_add hyz'''' hyz'''.ne' hp]
    rw [lt_div_iff hyz', ← div_lt_div_right hy']
    convert this using 1
    · ring_nf at H1 ⊢
      field_simp at H1 ⊢
      linear_combination p * (y - z) * y ^ p * H1
    · have H : (z / y) ^ p = z ^ p / y ^ p := div_rpow hz hy.le _
      ring_nf at H ⊢
      field_simp at H ⊢
      linear_combination -H
#align strict_convex_on_rpow strictConvexOn_rpow

theorem convexOn_rpow {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ (Ici 0) fun x : ℝ => x ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simpa using convexOn_id (convex_Ici _)
  exact (strictConvexOn_rpow hp).convexOn
#align convex_on_rpow convexOn_rpow

theorem strictConcaveOn_log_Iio : StrictConcaveOn ℝ (Iio 0) log := by
  refine' ⟨convex_Iio _, _⟩
  rintro x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab
  have hx' : 0 < -x := by linarith
  have hy' : 0 < -y := by linarith
  have hxy' : -x ≠ -y := by contrapose! hxy; linarith
  calc
    a • log x + b • log y = a • log (-x) + b • log (-y) := by simp_rw [log_neg_eq_log]
    _ < log (a • -x + b • -y) := (strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab)
    _ = log (-(a • x + b • y)) := by congr 1; simp only [Algebra.id.smul_eq_mul]; ring
    _ = _ := by rw [log_neg_eq_log]

#align strict_concave_on_log_Iio strictConcaveOn_log_Iio
