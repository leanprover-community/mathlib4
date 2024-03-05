import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.ByApprox.Core
import Mathlib.Tactic.ByApprox.Util
import Mathlib.Tactic.GRW
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.BigOperators


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

private lemma exp_pos_ub (k : ℕ) (x : ℝ) (k_pos : k > 0) (x_pos : x ≥ 0) (x_le_one : x ≤ 1) :
    exp x ≤ ∑ m in range k, x ^ m / m.factorial + x ^ k * (k + 1) / (k.factorial * k) := by
  have abs_le : abs x ≤ 1
  . rwa [abs_of_nonneg x_pos]
  have := exp_bound (x := x) abs_le k_pos
  apply le_add_of_sub_left_le
  grw [le_abs_self (_ - _), this, abs_of_nonneg x_pos]
  simp [← mul_div_assoc]

private lemma exp_nat (t : ℕ) : exp t = (exp 1) ^ t := by
  induction t
  case zero => simp
  case succ t' ih => simp [exp_add, ih, pow_succ, mul_comm]

private lemma lower_bound_pos (k t : ℕ) (x : ℝ) (l x_l e_l : ℚ) (x_lb : x_l ≤ x)
    (e_lb : e_l ≤ exp 1) (e_l_pos : e_l > 0) (ht : t ≤ x_l)
    (h : l = e_l ^ t * ∑ m in range k, (x_l - t) ^ m / m.factorial) : exp x ≥ l := by
  rw [show x = (x - t) + t by simp, exp_add, h, exp_nat]
  simp
  have x_l_sub_t_pos : x_l - t ≥ (0 : ℝ)
  . rw [← Rat.cast_coe_nat, ← Rat.cast_sub]
    exact Rat.cast_nonneg.mpr (sub_nonneg.mpr ht)
  grw [e_lb, mul_comm, exp_pos_lb k (x - t), ← x_lb]
  . grw [← x_lb]
    exact x_l_sub_t_pos
  . grw [x_l_sub_t_pos]
    apply sum_nonneg
    intro i _
    apply div_nonneg
    . simp
    . simp

private lemma upper_bound_pos (k t : ℕ) (x : ℝ) (u x_u e_u : ℚ) (x_ub : x_u ≥ x)
    (e_ub : e_u ≥ exp 1) (ht : t ≤ x_u) (k_pos : k > 0) (hxt : x_u ≤ t + 1)
    (h : u = e_u ^ t * (∑ m in range k, (x_u - t) ^ m / m.factorial
      + (x_u - t) ^ k * (k + 1) / (k.factorial * k))) :
    exp x ≤ u := by
  rw [show x = (x - t) + t by simp, exp_add, h, exp_nat]
  simp
  have x_u_sub_t_pos : x_u - t ≥ (0 : ℝ)
  . rw [← Rat.cast_coe_nat, ← Rat.cast_sub]
    exact Rat.cast_nonneg.mpr (sub_nonneg.mpr ht)
  grw [e_ub, mul_comm, ← x_ub, exp_pos_ub k (x_u - t) k_pos]
  . grw [x_u_sub_t_pos]
  . rw [← Rat.cast_coe_nat, ← Rat.cast_sub, ← Rat.cast_one, Rat.cast_le]
    simpa [add_comm]
  . grw [x_u_sub_t_pos, zero_pow, zero_mul, zero_div, add_zero]
    apply sum_nonneg
    intro i _
    apply div_nonneg
    . simp
    . simp
    exact k_pos

private lemma lower_bound_neg (k t : ℕ) (x : ℝ) (l x_l e_u : ℚ) (x_lb : x_l ≤ x)
    (e_ub : e_u ≥ exp 1) (ht : - t ≤ x_l)
    (h : l = (e_u ^ t)⁻¹ * ∑ m in range k, (x_l + t) ^ m / m.factorial) : exp x ≥ l := by
  rw [show x = (x + t) - t by simp, exp_sub, h, exp_nat]
  simp
  have x_l_add_t_pos : x_l + t ≥ (0 : ℝ)
  . rw [← Rat.cast_coe_nat, ← Rat.cast_add]
    apply Rat.cast_nonneg.mpr
    grw [← ht]
    simp
  grw [e_ub, mul_comm, exp_pos_lb k (x + t), ← x_lb, div_eq_mul_inv]
  . grw [← x_lb]
    exact x_l_add_t_pos
  . grw [x_l_add_t_pos]
    apply sum_nonneg
    intro i _
    apply div_nonneg
    . simp
    . simp

private lemma upper_bound_neg (k t : ℕ) (x : ℝ) (u x_u e_l : ℚ) (x_ub : x_u ≥ x)
    (e_lb : e_l ≤ exp 1) (ht : - t ≤ x_u) (k_pos : k > 0) (hxt : x_u + t ≤ 1) (e_l_pos : 0 < e_l)
    (h : u = (e_l ^ t)⁻¹ * (∑ m in range k, (x_u + t) ^ m / m.factorial
      + (x_u + t) ^ k * (k + 1) / (k.factorial * k))) :
    exp x ≤ u := by
  rw [show x = (x + t) - t by simp, exp_sub, h, exp_nat]
  simp
  have x_u_add_t_pos : x_u + t ≥ (0 : ℝ)
  . rw [← Rat.cast_coe_nat, ← Rat.cast_add]
    apply Rat.cast_nonneg.mpr
    grw [← ht]
    simp
  grw [e_lb, mul_comm, ← x_ub, exp_pos_ub k (x_u + t) k_pos, div_eq_mul_inv]
  . grw [x_u_add_t_pos]
  . rw [← Rat.cast_coe_nat, ← Rat.cast_add, ← Rat.cast_one, Rat.cast_le]
    simpa [add_comm]
  . grw [x_u_add_t_pos, zero_pow, zero_mul, zero_div, add_zero]
    apply sum_nonneg
    intro i _
    apply div_nonneg
    . simp
    . simp
    exact k_pos


private lemma exp_one_lower_bound (k : ℕ) (a : ℚ) (h : a = ∑ m in range k, (1 : ℚ) / m.factorial) :
    a ≤ exp 1 := by
  rw [h]
  simp
  grw [exp_pos_lb k 1]
  simp
  exact zero_le_one

private lemma exp_one_upper_bound (k : ℕ) (k_pos : k > 0) (a : ℚ)
    (h : a = ∑ m in range k, (1 : ℚ) / m.factorial + (k + 1) / (k.factorial * k)) :
    a ≥ exp 1 := by
  rw [h]
  simp
  grw [exp_pos_ub k 1]
  . simp
  . exact k_pos
  . simp
  . simp


-- todo cache early values/proofs maybe?

private def approxExpOne (precision : ℕ) (proofs : Bool) : MetaM Bounds := do
  let k := precision + 1
  let lb := ∑ m in range k, (1 : ℚ) / m.factorial
  let ub := ∑ m in range k, (1 : ℚ) / m.factorial + ((k : ℚ) + 1) / (k.factorial * k)
  if proofs then
    let lb_prf ← mkAppNormNum ``exp_one_lower_bound #[toExpr k, mkRatExpr lb, none]
    let ub_prf ← mkAppNormNum ``exp_one_upper_bound #[toExpr k, none, mkRatExpr ub, none]
    return ⟨lb, lb_prf, ub, ub_prf⟩
  else
    return ⟨lb, none, ub, none⟩

/-- `by_approx` extension for `Real.exp` --/
@[by_approx exp _] def approxExp : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e) | throwError "not Real.sqrt"

  trace[ByApprox] "Approx exp with arg {a}"

  -- todo fast path for exp 1?

  let ⟨lb, lb_prf, ub, ub_prf⟩ ← approximate precision proofs a
  let ⟨e_lb, e_lb_prf, e_ub, e_ub_prf⟩ ← approxExpOne precision proofs
  let k := precision + 1

  let lb_t := lb.floor
  let lb_rem := lb - lb_t
  let ub_t := ub.floor
  let ub_rem := ub - ub_t

  let e_pow_lb := if lb_t ≥ 0 then e_lb ^ lb_t else e_ub ^ lb_t
  let e_pow_ub := if ub_t ≥ 0 then e_ub ^ ub_t else e_lb ^ ub_t

  let new_lb := e_pow_lb * (∑ m in range k, lb_rem ^ m / m.factorial)
  let new_ub := e_pow_ub * (∑ m in range k, ub_rem ^ m / m.factorial + ub_rem ^ k * (k + 1)
      / (k.factorial * k))

  if proofs then
    let lb_prf ← if lb_t ≥ 0 then
      mkAppNormNum ``lower_bound_pos #[toExpr k, toExpr lb_t.toNat, a,
        mkRatExpr new_lb, mkRatExpr lb, mkRatExpr e_lb, lb_prf, e_lb_prf, none, none, none]
    else
      mkAppNormNum ``lower_bound_neg #[toExpr k, toExpr (- lb_t).toNat, a,
        mkRatExpr new_lb, mkRatExpr lb, mkRatExpr e_ub, lb_prf, e_ub_prf, none, none]

    trace[ByApprox] "got lb prf"

    let ub_prf ← if ub_t ≥ 0 then
      mkAppNormNum ``upper_bound_pos #[toExpr k, toExpr ub_t.toNat, a,
        mkRatExpr new_ub, mkRatExpr ub, mkRatExpr e_ub, ub_prf, e_ub_prf, none, none, none, none]
    else
      mkAppNormNum ``upper_bound_neg #[toExpr k, toExpr (- ub_t).toNat, a, mkRatExpr new_ub,
        mkRatExpr ub, mkRatExpr e_lb, ub_prf, e_lb_prf, none, none, none, none, none]

    trace[ByApprox] "got ub prf"

    return ⟨new_lb, lb_prf, new_ub, ub_prf⟩
  else
    return ⟨new_lb, none, new_ub, none⟩
