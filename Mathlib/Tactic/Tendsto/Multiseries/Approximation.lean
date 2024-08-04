import Mathlib.Tactic.Tendsto.Multiseries.Basic

open Filter Asymptotics

theorem MS.isApproximation_self_aux {f : ℝ → ℝ} {deg : ℝ} (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (h_deg : 1 < deg)
    : f =o[Filter.atTop] ((f ·)^deg) := by
  simp [Asymptotics.IsLittleO]
  intro c hc
  simp only [Asymptotics.IsBigOWith, Real.norm_eq_abs, Pi.pow_apply, ge_iff_le]
  have h1 := Filter.Tendsto.eventually hf <| Filter.eventually_gt_atTop (c^(-1 / (deg - 1)))
  apply Filter.Eventually.mono h1
  intro x hx
  have h2 : 0 < f x := by
    apply lt_of_le_of_lt _ hx
    apply Real.rpow_nonneg
    exact hc.le
  rw [Real.abs_rpow_of_nonneg, abs_of_pos] <;> try linarith
  rw [← one_le_div]
  ring_nf
  rw [← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add]
  all_goals try linarith
  rw [← div_le_iff', one_div, ← Real.rpow_neg_one]
  have := mul_one (-1)
  conv =>
    lhs
    rhs
    rw [← mul_one (-1)]
    rhs
    rw [← div_self (a := deg - 1) (by linarith)]
  rw [← mul_comm_div, Real.rpow_mul]
  ring_nf
  apply Real.rpow_le_rpow
  · apply Real.rpow_nonneg (by linarith)
  · ring_nf at hx
    exact hx.le
  all_goals linarith

def MS.baseFun' {basis : List (ℝ → ℝ)} {n : ℕ} (hn1 : 0 < n) (hn2 : n ≤ basis.length) : MS basis.length :=
  (MS.baseFun hn1).lift hn2

example : (MS.baseFun' (basis := [Real.exp, id]) (n := 1) (by decide) (by decide)).val =
  PreMS.cons 0
    (PreMS.cons 1 (PreMS.const 1) PreMS.nil)
  PreMS.nil := by rfl

theorem MS.isApproximation_baseFun_self {n : ℕ} {basis : List (ℝ → ℝ)} (hn_1 : 0 < n)
    (hn_2 : n ≤ basis.length) : MS.baseFun' hn_1 hn_2 |>.isApproximation basis[n - 1] basis := by

  -- simp [isApproximation, PreMS.isApproximation]
  sorry -- use isApproximation_self_aux
