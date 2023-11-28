import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.ByApprox.Core

namespace Mathlib.Tactic.ByApprox

open Lean hiding Rat
open Qq Meta Real BigOperators Finset

private lemma exp_pos_lb (k : ℕ) (x : ℝ) (x_pos : x ≥ 0) :
    exp x ≥ ∑ m in range k, x ^ m / m.factorial := by
  unfold exp Complex.exp Complex.exp'
  rw [Complex.lim_eq_lim_im_add_lim_re, Complex.add_re]
  rw [Complex.mul_I_re, Complex.ofReal_im, Complex.ofReal_re]
  rw [neg_zero, add_zero]
  conv =>
    enter [1, 1, 1, 1, n, 2, m]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_nat_cast, ← Complex.ofReal_div]
  conv =>
    enter [1, 1, 1, 1, n]
    rw [← Complex.ofReal_sum]
  apply CauSeq.le_lim
  refine CauSeq.le_of_exists (α := ℝ) ⟨k, ?_⟩
  intro j jk
  unfold Subtype.val Complex.cauSeqRe
  simp
  conv =>
    enter [2, 2, m, 1]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  apply sum_le_sum_of_subset_of_nonneg
  simpa
  intro i _ _
  apply div_nonneg (pow_nonneg x_pos _) (Nat.cast_nonneg _)

--

private lemma factorial_ge_factorial_mul_pow (k : ℕ) (l : ℕ) (kl : k ≤ l) :
    l.factorial ≥ k.factorial * (k + 1) ^ (l - k) := by

  sorry


private lemma exp_pos_ub (k : ℕ) (x : ℝ) (k_pos : k > 0) (x_pos : x > 0) (x_le_one : x ≤ 1) :
    exp x ≤ ∑ m in range k, x ^ m / m.factorial + (1 + 1 / k) / k.factorial := by
  unfold exp Complex.exp Complex.exp'
  rw [Complex.lim_eq_lim_im_add_lim_re, Complex.add_re]
  rw [Complex.mul_I_re, Complex.ofReal_im, Complex.ofReal_re]
  rw [neg_zero, add_zero]
  conv =>
    enter [1, 1, 1, 1, n, 2, m]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_nat_cast, ← Complex.ofReal_div]
  conv =>
    enter [1, 1, 1, 1, n]
    rw [← Complex.ofReal_sum]
  rw [← add_neg_le_iff_le_add']
  rw [← CauSeq.lim_const (abv := abs) (- _), CauSeq.lim_add]
  apply CauSeq.lim_le
  refine CauSeq.le_of_exists ⟨k, ?_⟩
  intro j jk
  simp [Complex.cauSeqRe, -add_neg_le_iff_le_add]
  rw [← sub_eq_add_neg]
  conv =>
    enter [1, 1, 2, m, 1]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Finset.sum_range_sub_sum_range]
  trans ∑ m in filter (fun k_1 ↦ k ≤ k_1) (range j), 1 / ↑(Nat.factorial m)
  . apply sum_le_sum
    intro _ _
    gcongr
    . exact pow_le_one _ x_pos.le x_le_one
  trans ∑ m in filter (fun k_1 ↦ k ≤ k_1) (range j), 1 / ↑(Nat.factorial m)
  sorry
  sorry
  sorry

-- private lemma lower_bound_sqrt (t : ℝ) (lb t_lb : ℚ)
--     (h : lb * lb ≤ t_lb) (p_lb : t ≥ t_lb) : Real.sqrt t ≥ lb := by
--   apply Real.le_sqrt_of_sq_le
--   trans ↑t_lb
--   . rwa [← Rat.cast_pow, Rat.cast_le, pow_two]
--   . exact p_lb

-- private lemma upper_bound_sqrt (t : ℝ) (ub t_ub : ℚ) (ub_pos : ub ≥ 0)
--     (h : ub * ub ≥ t_ub) (p_ub : t ≤ t_ub) : Real.sqrt t ≤ ub := by
--   refine (Real.sqrt_le_left (Rat.cast_nonneg.mpr ub_pos)).mpr ?_
--   trans ↑t_ub
--   . exact p_ub
--   . rwa [← Rat.cast_pow, Rat.cast_le, pow_two]

/-- `by_approx` extension for `Real.exp` --/
@[by_approx exp _] def approxExp : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e) | throwError "not Real.sqrt"

  trace[ByApprox] "Approx exp with arg {a}"

  let ⟨lb, lb_prf, ub, ub_prf⟩ ← approximate precision proofs a

  -- todo these bounds are bad
  let multiplier := 4 ^ precision

  let new_lb := if lb < 0 then 0 else
    ((lb.num.toNat * multiplier).sqrt : ℚ) / ((lb.den * multiplier).sqrt + 1)

  -- todo consider upper bound
  let new_ub := ((ub.num.toNat * multiplier).sqrt + 1 : ℚ) / (ub.den * multiplier).sqrt

  -- if proofs then
  --   let (new_lb_prf) ← if lb < 0 then
  --     pure q(Real.sqrt_nonneg (0 : ℚ))
  --   else
  --     mkAppNormNum ``lower_bound_sqrt
  --       #[a, mkRatExpr new_lb, mkRatExpr lb, none, lb_prf]

  --   let new_ub_prf ← mkAppNormNum ``upper_bound_sqrt
  --       #[a, mkRatExpr new_ub, mkRatExpr ub, none, none, ub_prf]
  throwError "todo"
  --   -- return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩
  -- else
  --   -- return ⟨new_lb, none, new_ub, none⟩
  --   throwError "todo"
