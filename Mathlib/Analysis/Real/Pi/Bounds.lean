/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mario Carneiro
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Pi

This file contains lemmas which establish bounds on `Real.pi`.
Notably, these include `pi_gt_sqrtTwoAddSeries` and `pi_lt_sqrtTwoAddSeries`,
which bound `π` using series;
numerical bounds on `π` such as `pi_gt_d2` and `pi_lt_d2` (more precise versions are given, too).

See also `Mathlib/Analysis/Real/Pi/Leibniz.lean` and `Mathlib/Analysis/Real/Pi/Wallis.lean` for
infinite formulas for `π`.
-/

open scoped Real

namespace Real

theorem pi_gt_sqrtTwoAddSeries (n : ℕ) : 2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) < π := by
  have : √(2 - sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) < π := by
    rw [← lt_div_iff₀, ← sin_pi_over_two_pow_succ]
    focus
      apply sin_lt
      apply div_pos pi_pos
    all_goals apply pow_pos; norm_num
  refine lt_of_le_of_lt (le_of_eq ?_) this
  rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]; norm_num

theorem pi_lt_sqrtTwoAddSeries (n : ℕ) :
    π < 2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) + 1 / 4 ^ n := by
  have : π < (√(2 - sqrtTwoAddSeries 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * (2 : ℝ) ^ (n + 2) := by
    rw [← div_lt_iff₀ (by simp), ← sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
    calc
      π / 2 ^ (n + 2) - sin (π / 2 ^ (n + 2)) < (π / 2 ^ (n + 2)) ^ 3 / 4 :=
        sub_lt_comm.1 <| sin_gt_sub_cube (by positivity) <| div_le_one_of_le₀ ?_ (by positivity)
      _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by gcongr; exact pi_le_four
      _ = 1 / (2 ^ n) ^ 3 / 4 := by simp [add_comm n, pow_add, div_mul_eq_div_div]; norm_num
    calc
      π ≤ 4 := pi_le_four
      _ = 2 ^ (0 + 2) := by norm_num
      _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num
  refine lt_of_lt_of_le this (le_of_eq ?_); rw [add_mul]; congr 1
  · ring
  simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div, ← pow_add]
  rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm, mul_inv_eq_iff_eq_mul₀, ← pow_add]
  · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc, mul_comm n]
  all_goals norm_num

/-- From an upper bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`sqrtTwoAddSeries 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrtTwoAddSeries`. -/
theorem pi_lower_bound_start (n : ℕ) {a}
    (h : sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤ (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
    a < π := by
  refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries n); rw [mul_comm]
  refine (div_le_iff₀ (pow_pos (by norm_num) _)).mp (le_sqrt_of_sq_le ?_)
  rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by rw [Nat.cast_zero, zero_div]]

theorem sqrtTwoAddSeries_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ} (hz : sqrtTwoAddSeries (c / d) n ≤ z)
    (hb : 0 < b) (hd : 0 < d) (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
    sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
  refine le_trans ?_ hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  rw [sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
    add_div_eq_mul_add_div _ _ (ne_of_gt hb'), div_le_div_iff₀ hb' (pow_pos hd' _)]
  exact mod_cast h

/-- From a lower bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrtTwoAddSeries 0 n`, one can deduce the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrtTwoAddSeries`. -/
theorem pi_upper_bound_start (n : ℕ) {a}
    (h : (2 : ℝ) - ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
    (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) : π < a := by
  refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) ?_
  rw [← le_sub_iff_add_le, ← le_div_iff₀', sqrt_le_left, sub_le_comm]
  · rwa [Nat.cast_zero, zero_div] at h
  · exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt zero_lt_two) _)
  · exact pow_pos zero_lt_two _

theorem sqrtTwoAddSeries_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
    (hz : z ≤ sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd : 0 < d)
    (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrtTwoAddSeries (c / d) (n + 1) := by
  apply le_trans hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  apply le_sqrt_of_sq_le
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'), div_le_div_iff₀ (pow_pos hb' _) hd']
  exact mod_cast h

section Tactic

open Lean Elab Tactic Qq

/-- Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≥ a/2^(n+1)`. -/
elab "pi_lower_bound " "[" l:term,* "]" : tactic => do
  have els := l.getElems
  let n := quote els.size
  evalTactic (← `(tactic| apply pi_lower_bound_start $n))
  for l in els do
    let {num, den, ..} ← unsafe Meta.evalExpr ℚ q(ℚ) (← Term.elabTermAndSynthesize l (some q(ℚ)))
    evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_up $(quote num.toNat) $(quote den)))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals <| evalTactic (← `(tactic| norm_num1))

/-- Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≤ (a - 1/4^n) / 2^(n+1)`. -/
elab "pi_upper_bound " "[" l:term,* "]" : tactic => do
  have els := l.getElems
  let n := quote els.size
  evalTactic (← `(tactic| apply pi_upper_bound_start $n))
  for l in els do
    let {num, den, ..} ← unsafe Meta.evalExpr ℚ q(ℚ) (← Term.elabTermAndSynthesize l (some q(ℚ)))
    evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_down $(quote num.toNat) $(quote den)))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals <| evalTactic (← `(tactic| norm_num1))

end Tactic

/-!
The below witnesses were generated using the following Mathematica script:
```mathematica
bound[a_, Iters -> n_, Rounding -> extra_, Precision -> prec_] := Module[{r0, r, r2, diff, sign},
  On[Assert];
  sign = If[a >= \[Pi], Print["upper"]; 1, Print["lower"]; -1];
  r0 = 2 - ((a - (sign + 1)/2/4^n)/2^(n + 1))^2;
  r = Log[2 - NestList[#^2 - 2 &, N[r0, prec], n - 1]];
  diff = (r[[-1]] - Log[2 - Sqrt[2]])/(Length[r] + 1);
  If[sign diff <= 0, Return["insufficient iterations"]];
  r2 = Log[Rationalize[Exp[#], extra (Exp[#] - Exp[# - sign diff])] &
    /@ (r - diff Range[1, Length[r]])];
  Assert[sign (2 - Exp@r2[[1]] - r0) >= 0];
  Assert[And @@ Table[
    sign (Sqrt@(4 - Exp@r2[[i + 1]]) - (2 - Exp@r2[[i]])) >= 0, {i, 1, Length[r2] - 1}]];
  Assert[sign (Exp@r2[[-1]] - (2 - Sqrt[2])) >= 0];
  With[{s1 = ToString@InputForm[2 - #], s2 = ToString@InputForm[#]},
    If[StringLength[s1] <= StringLength[s2] + 2, s1, "2-" <> s2]] & /@ Exp@Reverse@r2
];
```
-/

theorem pi_gt_three : 3 < π := by
  -- bound[3, Iters -> 1, Rounding -> 2, Precision -> 3]
  pi_lower_bound [23 / 16]

theorem pi_lt_four : π < 4 := by
  -- bound[4, Iters -> 1, Rounding -> 1, Precision -> 1]
  pi_upper_bound [4 / 3]

theorem pi_gt_d2 : 3.14 < π := by
  -- bound[314*^-2, Iters -> 4, Rounding -> 1.5, Precision -> 8]
  pi_lower_bound [338 / 239, 704 / 381, 1940 / 989, 1447 / 727]

theorem pi_lt_d2 : π < 3.15 := by
  -- bound[315*^-2, Iters -> 4, Rounding -> 1.4, Precision -> 7]
  pi_upper_bound [41 / 29, 109 / 59, 865 / 441, 412 / 207]

theorem pi_gt_d4 : 3.1415 < π := by
  -- bound[31415*^-4, Iters -> 6, Rounding -> 1.1, Precision -> 10]
  pi_lower_bound [
    1970 / 1393, 3010 / 1629, 11689 / 5959, 10127 / 5088, 33997 / 17019, 23235 / 11621]

theorem pi_lt_d4 : π < 3.1416 := by
  -- bound[31416*^-4, Iters -> 9, Rounding -> .9, Precision -> 16]
  pi_upper_bound [
    4756/3363, 14965/8099, 21183/10799, 49188/24713, 2-53/22000, 2-71/117869, 2-47/312092,
    2-17/451533, 2-4/424971]

theorem pi_gt_d6 : 3.141592 < π := by
  -- bound[3141592*^-6, Iters -> 10, Rounding -> .8, Precision -> 16]
  pi_lower_bound [
    11482/8119, 7792/4217, 54055/27557, 2-623/64690, 2-337/139887, 2-208/345307, 2-167/1108925,
    2-64/1699893, 2-31/3293535, 2-48/20398657]

theorem pi_lt_d6 : π < 3.141593 := by
  -- bound[3141593*^-6, Iters -> 11, Rounding -> .5, Precision -> 17]
  pi_upper_bound [
    35839/25342, 49143/26596, 145729/74292, 294095/147759, 2-137/56868, 2-471/781921, 2-153/1015961,
    2-157/4170049, 2-28/2974805, 2-9/3824747, 2-7/11899211]

theorem pi_gt_d20 : 3.14159265358979323846 < π := by
  -- bound[314159265358979323846*^-20, Iters -> 34, Rounding -> .6, Precision -> 46]
  pi_lower_bound [
    671574048197/474874563549, 58134718954/31462283181, 3090459598621/1575502640777,
    2-7143849599/741790664068, 8431536490061/4220852446654, 2-2725579171/4524814682468,
    2-2494895647/16566776788806, 2-608997841/16175484287402, 2-942567063/100141194694075,
    2-341084060/144951150987041, 2-213717653/363295959742218, 2-71906926/488934711121807,
    2-29337101/797916288104986, 2-45326311/4931175952730065, 2-7506877/3266776448781479,
    2-5854787/10191338039232571, 2-4538642/31601378399861717, 2-276149/7691013341581098,
    2-350197/39013283396653714, 2-442757/197299283738495963, 2-632505/1127415566199968707,
    2-1157/8249230030392285, 2-205461/5859619883403334178, 2-33721/3846807755987625852,
    2-11654/5317837263222296743, 2-8162/14897610345776687857, 2-731/5337002285107943372,
    2-1320/38549072592845336201, 2-707/82588467645883795866, 2-53/24764858756615791675,
    2-237/442963888703240952920, 2-128/956951523274512100791, 2-32/956951523274512100783,
    2-27/3229711391051478340136]

theorem pi_lt_d20 : π < 3.14159265358979323847 := by
  -- bound[314159265358979323847*^-20, Iters -> 34, Rounding -> .5, Precision -> 46]
  pi_upper_bound [
    215157040700/152139002499, 936715022285/506946517009, 1760670193473/897581880893,
    2-6049918861/628200981455, 2-8543385003/3546315642356, 2-2687504973/4461606579043,
    2-1443277808/9583752057175, 2-546886849/14525765179168, 2-650597193/69121426717657,
    2-199969519/84981432264454, 2-226282901/384655467333100, 2-60729699/412934601558121,
    2-25101251/682708800188252, 2-7156464/778571703825145, 2-7524725/3274543383827551,
    2-4663362/8117442793616861, 2-1913009/13319781840326041, 2-115805/3225279830894912,
    2-708749/78957345705688293, 2-131255/58489233342660393, 2-101921/181670219085488669,
    2-44784/319302953916238627, 2-82141/2342610212364552264, 2-4609/525783249231842696,
    2-4567/2083967975041722089, 2-2273/4148770928197796067, 2-563/4110440884426500846,
    2-784/22895812812720260289, 2-1717/200571992854289218531, 2-368/171952226838388893139,
    2-149/278487845640434185590, 2-207/1547570041545500037992, 2-20/598094702046570062987,
    2-7/837332582865198088180]

end Real
