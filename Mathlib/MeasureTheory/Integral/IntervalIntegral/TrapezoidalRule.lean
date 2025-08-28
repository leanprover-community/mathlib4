/-
Copyright (c) 2025 P. Michael Kielstra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P. Michael Kielstra
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The trapezoidal rule

This file contains a definition of integration on `[[a, b]]` via the trapezoidal rule, along with
an error bound in terms of a bound on the second derivative of the integrand.

## Main results
- `trapezoidal_error_le`: the convergence theorem for the trapezoidal rule.

## References
We follow the proof on (Wikipedia)[https://en.wikipedia.org/wiki/Trapezoidal_rule].
-/

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using the trapezoidal rule with `N+1` total evaluations of
`f`.  (Note the off-by-one problem here: `N` counts the number of trapezoids, not the number of
evaluations.) -/
noncomputable def trapezoidal_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * ((f a + f b) / 2 + ∑ k ∈ range (N - 1), f (a + (k + 1) * (b - a) / N))

/-- The absolute error of trapezoidal integration. -/
noncomputable def trapezoidal_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  |(∫ x in a..b, f x) - (trapezoidal_integral f N a b)|

/-- Just like exact integration, the trapezoidal approximation retains the same magnitude but
changes sign when the endpoints are swapped. -/
theorem trapezoidal_integral_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    trapezoidal_integral f N a b = -(trapezoidal_integral f N b a) := by
  unfold trapezoidal_integral
  rw [neg_mul_eq_neg_mul, neg_div', neg_sub, add_comm (f b) (f a), ← sum_range_reflect]
  congr 2
  apply sum_congr rfl
  intro k hk
  norm_cast
  rw [tsub_tsub, add_comm 1, Nat.cast_add, Nat.cast_sub (mem_range.mp hk), Nat.cast_sub N_nonzero]
  apply congr_arg
  field_simp
  ring

/-- The absolute error of the trapezoidal rule does not change when the endpoints are swapped. -/
theorem trapezoidal_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    trapezoidal_error f N a b = trapezoidal_error f N b a := by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b, integral_symm, neg_sub_neg, abs_sub_comm]

/-- Just like exact integration, the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
theorem trapezoidal_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_integral f N a a = 0 := by
  simp [trapezoidal_integral]

/-- The error of the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
theorem trapezoidal_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_error f N a a = 0 := by
  simp [trapezoidal_error]

/-- The hard part of the trapezoidal rule error bound: proving it in the case of a non-empty closed
interval with ordered endpoints. -/
lemma trapezoidal_error_le_of_lt {f : ℝ → ℝ} {ζ : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (h_df : DifferentiableOn ℝ f (Icc a b))
    (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a b)
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ)
    {N : ℕ} (N_nonzero : 0 < N) :
    trapezoidal_error f N a b ≤ (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
  let h := (b - a) / N
  -- Make continuity of f explicit so that fun_prop can use it in a couple of places later on.
  have h_cf : ContinuousOn f (Icc a b) := DifferentiableOn.continuousOn h_df
  -- Make it explicit that 0 < h.
  have h_gt_zero : 0 < h := div_pos (sub_pos.mpr a_lt_b) (Nat.cast_pos.mpr N_nonzero)
  -- Let a_k (written ak k) be the k-th integration point for the trapezoidal rule, and define
  -- (g k)(t) to be the error of integrating from a_k to a_k + t using a linear approximation.
  let ak (k : ℕ) := a + k * h
  let g (k : ℕ) (t : ℝ) := (t / 2) * (f (ak k) + f (ak k + t)) - ∫ x in (ak k)..(ak k + t), f x
  -- Verify that [ak k, ak k + h] is still within the bounds of integration for sensible k.
  have ak_bound {k : ℕ} (hk: k < N) {t : ℝ} (ht: t ∈ Icc 0 h) : ak k + t ∈ Icc a b := by
    unfold ak h at *
    rw [Set.mem_Icc] at ht ⊢
    rw [← Nat.add_one_le_iff] at hk
    constructor
    · nlinarith
    · grw [add_assoc, ← le_sub_iff_add_le', ht.2, ← add_one_mul, ← Nat.cast_add_one, hk,
        mul_div_cancel₀ _ (by positivity)]
  -- We will mostly use ak_bound in these simplified forms.  (There is one use later on which does
  -- need it, so we do have prove it in full.)
  have a_lt_ak {k : ℕ} (hk: k < N): a ≤ ak k := by
    rw [← add_zero (ak k)]
    exact (ak_bound hk (left_mem_Icc.mpr (le_of_lt h_gt_zero))).left
  have ak_h_lt_b {k : ℕ} (hk: k < N) : ak k + h ≤ b := by
    exact (ak_bound (hk) (right_mem_Icc.mpr (le_of_lt h_gt_zero))).right
  -- We will differentiate g twice, find that g''(t) ≤ (ζ / 2) * t, and then integrate twice.
  have g_bound {k : ℕ} (hk : k < N) : |g k h| ≤ (ζ / 12) * h ^ 3 := by
    -- Hand-computed expressions for g' and g''.
    let dg (k : ℕ) (t : ℝ) :=
        (1 / 2) * (f (ak k) + f (ak k + t))
        + (t / 2) * (derivWithin f (Icc a b) (ak k + t)) - f (ak k + t)
    let ddg (k : ℕ) (t : ℝ) := (t / 2) * (iteratedDerivWithin 2 f (Icc a b) (ak k + t))
    -- This particular lemma will come in handy a couple of times.
    have comp_deriv {f : ℝ → ℝ} (h_df: DifferentiableOn ℝ f (Icc a b)) {y : ℝ}
        (hy: y ∈ Icc 0 h) : HasDerivWithinAt (fun x ↦ f (ak k + x))
        (derivWithin f (Icc a b) (ak k + y)) (Icc 0 h) y := by
      apply HasDerivWithinAt.mono (t := Icc (a - ak k) (b - ak k))
      pick_goal 2
      · apply Set.Icc_subset_Icc
        · exact tsub_nonpos.mpr (a_lt_ak hk)
        · exact le_tsub_of_add_le_left (ak_h_lt_b hk)
      have : derivWithin f (Icc a b) (ak k + y) =
          derivWithin (fun x ↦ f (ak k + x)) (Icc (a - ak k) (b - ak k)) y := by
        simp [derivWithin_comp_const_add f (ak k) (Icc (a - ak k) (b - ak k)) y]
      rw [this]
      apply DifferentiableWithinAt.hasDerivWithinAt
      apply DifferentiableWithinAt.comp (t := Icc a b)
      · exact h_df (ak k + y) (ak_bound hk hy)
      · fun_prop
      · intro x hx
        exact ⟨tsub_le_iff_left.mp hx.left, le_sub_iff_add_le'.mp hx.right⟩
    -- Compute g' by applying standard derivative identities.
    have h_dg (y : ℝ) (hy: y ∈ Icc 0 h) : HasDerivWithinAt (g k) (dg k y) (Icc 0 h) y := by
      refine fun_sub (fun_mul (div_const (hasDerivWithinAt_id _ _) _)
        (const_add _ (comp_deriv h_df hy))) ?_
      · nth_rewrite 1 [← add_zero (ak k)]
        simp_rw [← integral_comp_add_left f (ak k)]
        -- We now want to apply FToC and be done with it, but we'll need to prove that
        have h_cont : ContinuousOn (fun x ↦ f (ak k + x)) (Icc 0 h) :=
          h_cf.comp' (by fun_prop) fun t ↦ ak_bound hk
        have := Fact.mk hy -- Needed for integral_hasDerivWithinAt_right
        apply integral_hasDerivWithinAt_right
        · apply ContinuousOn.intervalIntegrable_of_Icc hy.left
          apply ContinuousOn.mono h_cont
          exact Set.Icc_subset_Icc (le_refl 0) hy.right
        · exact ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin h_cont measurableSet_Icc y
        · exact ContinuousOn.continuousWithinAt h_cont hy
    -- Compute g'', once again applying standard derivative identities.
    have h_ddg (y : ℝ) (hx: y ∈ Icc 0 h) : HasDerivWithinAt (dg k) (ddg k y) (Icc 0 h) y := by
      -- The eventual expression for g'' has several terms that cancel, which we have to undo here
      -- so that the various HasDerivWithinAt theorems will have everything they need.
      let dfaky := derivWithin f (Icc a b) (ak k + y)
      rw [(by ring: ddg k y = (1 / 2) * dfaky + ((1 / 2) * dfaky + ddg k y) - dfaky)]
      refine fun_sub (fun_add (const_mul _ (const_add _ (comp_deriv h_df hx)))
        (fun_mul (div_const (hasDerivWithinAt_id _ _) _) ?_)) (comp_deriv h_df hx)
      rw [iteratedDerivWithin_eq_iterate]
      exact comp_deriv h_ddf hx
    -- Technically this would work for all x ≥ 0, but we only need it for x ∈ Icc 0 h (and it makes
    -- more pure-mathematical sense that way).
    have bound_ddg : ∀ x ∈ Icc 0 h, |ddg k x| ≤ (ζ / 2) * (x ^ 1) := by
      intro x hx
      calc
        _ = |x / 2| * |iteratedDerivWithin 2 f (Icc a b) (ak k + x)| := abs_mul _ _
        _ ≤ |x / 2| * ζ := mul_le_mul_of_nonneg_left (fpp_bound _) (abs_nonneg _)
        _ = (x / 2) * ζ := by rw [abs_div, abs_two, abs_of_nonneg hx.left]
        _ = _ := by ring
    have subset_icc : ∀ t ∈ Icc 0 h, Icc 0 t ⊆ Icc 0 h := by
      intro _ ht
      exact Icc_subset_Icc_right ht.right
    -- Now that we have our bound on ddg, we want to turn that into a bound on g.  Our first lemma
    -- is a specialized Fundamental Theorem of Calculus.
    have integral_from_zero {r r': ℝ → ℝ}
        (h_deriv: ∀ x ∈ Icc 0 h, HasDerivWithinAt r (r' x) (Icc 0 h) x) (h_zero: r 0 = 0)
        (h_cont_r: ContinuousOn r (Icc 0 h))
        (h_int_r': IntervalIntegrable r' volume 0 h) :
        ∀ t ∈ Icc 0 h, ∫ x in (0)..t, r' x = r t := by
      intro t ht
      rw [(by rw [h_zero, sub_zero]: r t = r t - r 0)]
      apply integral_eq_sub_of_hasDerivAt_of_le ht.left
      · exact ContinuousOn.mono (h_cont_r) (subset_icc t ht)
      · intro x hx
        apply HasDerivWithinAt.hasDerivAt (s := Icc 0 t)
        · apply HasDerivWithinAt.mono (t := Icc 0 h)
          · exact h_deriv x (subset_icc t ht (mem_Icc_of_Ioo hx))
          · exact Icc_subset_Icc_right ht.right
        · exact Icc_mem_nhds_iff.mpr hx
      · apply IntervalIntegrable.mono h_int_r' ?_ (le_refl volume)
        rw [uIcc_of_le ht.left, uIcc_of_lt h_gt_zero]
        exact subset_icc t ht
    -- The second lemma exists largely to specialize an extremely general standard integral result:
    -- that the norm of the integral is bounded below by the integral of the norm.
    have abs_int_leq_int_abs {φ ψ : ℝ → ℝ} {t : ℝ} (ht: t ∈ Icc 0 h) (cont: ContinuousOn ψ [[0, h]])
        (abs_bound: ∀ x ∈ Icc 0 h, |φ x| ≤ ψ x) :
        |∫ (x : ℝ) in (0)..t, φ x| ≤ ∫ (x : ℝ) in (0)..t, ψ x := by
      have : ∀ x ∈ Ioc 0 t, ‖φ x‖ ≤ ψ x := by
        intro x hx
        rw [Real.norm_eq_abs]
        apply abs_bound x (mem_Icc_of_Ioc ?_)
        exact ⟨hx.left, le_trans hx.right ht.right⟩
      apply norm_integral_le_of_norm_le ht.left (ae_of_all _ this)
      apply ContinuousOn.intervalIntegrable_of_Icc ht.left
      apply ContinuousOn.mono cont (s := [[0, h]])
      field_simp
      grind
    -- Now we put all this together and do a bit more calculus: if |f' t| < c * t ^ n, then
    -- |f t| < c / (n + 1) * t ^ (n + 1).  The bound is phrased in this exact way, including
    -- universal quantifiers, so that it can be composed with itself.
    have power_bound {φ φ' : ℝ → ℝ} (h_int: ∀ t ∈ Icc 0 h, ∫ x in (0)..t, φ' x = φ t) {c: ℝ} {n : ℕ}
        (h_bound: ∀ t ∈ Icc 0 h, |φ' t| ≤ c * t ^ n) :
        ∀ t ∈ Icc 0 h, |φ t| ≤ c / (n + 1) * t ^ (n + 1) := by
      intro t ht
      rw [← h_int t ht]
      calc
        _ ≤ ∫ x in (0)..t, c * (x ^ n)  := abs_int_leq_int_abs ht (by fun_prop) h_bound
        _ = c * ∫ x in (0)..t, x ^ n    := integral_const_mul _ _
        _ = c * (t ^ (n + 1) / (n + 1)) := by simp
        _ = _                           := by ring_nf
    -- Finally, we run our `power_bound` logic twice, turning our bound on ddg into a bound on dg
    -- and then into a bound on g.  (This does require proving continuity of g and dg, which we can
    -- do straightforwardly by using our previous derivative results, and integrability of dg and
    -- ddg.  The first of these is also straightforward, while the second needs a little bit of
    -- work.)
    have gk_continuous : ContinuousOn (g k) (Icc 0 h) := by
      intro y hy
      apply HasDerivWithinAt.continuousWithinAt
      exact h_dg y hy
    have dgk_continuous : ContinuousOn (dg k) (Icc 0 h) := by
      intro y hy
      apply HasDerivWithinAt.continuousWithinAt
      exact h_ddg y hy
    have dgk_integrable : IntervalIntegrable (dg k) volume 0 h :=
      ContinuousOn.intervalIntegrable_of_Icc (le_of_lt h_gt_zero) dgk_continuous
    have ddgk_integrable : IntervalIntegrable (ddg k) volume 0 h := by
      apply IntervalIntegrable.continuousOn_mul
      · have : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume (ak k) (ak k + h) := by
          apply IntervalIntegrable.mono h_ddf_integrable _ (le_refl volume)
          rw [uIcc_of_lt a_lt_b, uIcc_of_lt (lt_add_of_pos_right (ak k) h_gt_zero)]
          exact Set.Icc_subset_Icc (a_lt_ak hk) (ak_h_lt_b hk)
        have := IntervalIntegrable.comp_add_left this (ak k)
        simpa
      · fun_prop
    have := power_bound (integral_from_zero h_ddg (by unfold dg; ring_nf: dg k 0 = 0)
      dgk_continuous ddgk_integrable) bound_ddg
    have := power_bound (integral_from_zero h_dg (by simp [g]: g k 0 = 0) gk_continuous
      dgk_integrable) this
    ring_nf at this
    ring_nf
    exact this h (right_mem_Icc.mpr (le_of_lt h_gt_zero))
  -- Each g represents a two-point trapezoidal integration error starting from ak k, so the sum of
  -- g k h over all k from 0 to N - 1 is exactly the error of the trapezoidal rule.  We'll prove
  -- that fact a little lower down; for now, let's use our bound from earlier to show that the sum
  -- is bounded by what we want.
  have sum_g_bound : |∑ k ∈ range N, g k h| ≤ (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
    calc
      _ ≤ ∑ k ∈ range N, |g k h|          := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N, (ζ / 12 * h ^ 3) := sum_le_sum fun i a ↦ g_bound (List.mem_range.mp a)
      _ = N * (ζ / 12 * h ^ 3)            := by simp [sum_const]
      _ = _                               := by unfold h; field_simp; ring
  -- The final stage of the proof is really just an exercise in combinatorics.  We have some sums
  -- made up of fairly arbitrary functions, and we want to show that they are equal to some other
  -- sums of other fairly arbitrary functions.  As a first step, we prove an equality that allows us
  -- to forget about the meaning of ak in terms of h and treat it as just something to be summed.
  have ak_cons (k : ℕ) : ak k + h = ak (k + 1) := by
    unfold ak; field_simp; ring
  -- Now we can embark on our combinatorial odyssey.
  have sum_g_trap_err : |∑ k ∈ range N, g k h| = trapezoidal_error f N a b := by
    unfold g
    rw [sum_sub_distrib]
    simp_rw [ak_cons]
    -- After splitting our sums, we're left with one sum of values of f and one sum of integrals.
    -- We deal with the first one first.
    have : ∑ x ∈ range N, h / 2 * (f (ak x) + f (ak (x + 1)))
        = trapezoidal_integral f N (ak 0) (ak N) := by
      unfold trapezoidal_integral h
      rw [← mul_sum, sum_add_distrib, (by unfold ak h; field_simp: ak N - ak 0 = b - a)]
      have (k : ℕ): ak 0 + (k + 1) * (b - a) / N = ak (k + 1) := by
        unfold ak h; field_simp
      simp_rw [this]
      field_simp
      left
      nth_rw 1 2 [← Nat.sub_one_add_one_eq_of_pos N_nonzero]
      rw [range_succ,
          sum_insert notMem_range_self,
          sum_insert notMem_range_self,
          Nat.sub_add_cancel N_nonzero]
      -- We now need a very specific rearrangement so that we can get exactly the right telescoping
      -- sum.  We could do this with add_comm and friends, but it's easier and more readable to
      -- just write it out specifically and let linarith do the hard work.  Here, after we unify
      -- with the actual target, s1 and s2 will be our sum expressions, fan will be f (ak N),
      -- fa0 will be f (ak 0), and fanm will be f (ak (N - 1)). -/
      have {s1 s2 fa0 fanm fan : ℝ} (_ : s2 - s1 = fanm - fa0):
        fanm + s1 + (fan + s2) = fa0 + fan + s2 * 2
        := by linarith
      apply this
      rw [← sum_sub_distrib, sum_range_sub (fun k ↦ f (ak k)) _]
    -- We now substitute back into the original equality, deal with the integral sum with a standard
    -- theorem, and clean up.
    rw [this,
        sum_integral_adjacent_intervals,
        (by ring: ak 0 = a),
        (by unfold ak h; field_simp: ak N = b)]
    · exact abs_sub_comm _ _
    -- We do need to check that the integrals we added up actually were all integrable.
    · intro k hk
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono h_cf
      intro x hx
      rw [← ak_cons k] at hx
      have : ak k ≤ ak k + h := le_add_of_nonneg_right (le_of_lt h_gt_zero)
      rw [uIcc_of_le this] at hx
      exact ⟨le_trans (a_lt_ak hk) hx.left, le_trans hx.right (ak_h_lt_b hk)⟩
  rwa [← sum_g_trap_err]

/-- The standard error bound for trapezoidal integration on the general interval `[[a, b]]`. -/
theorem trapezoidal_error_le {f : ℝ → ℝ} {a b : ℝ}
    (h_df : DifferentiableOn ℝ f [[a, b]])
    (h_ddf : DifferentiableOn ℝ (derivWithin f [[a, b]]) [[a, b]])
    (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f [[a, b]]) volume a b) {ζ : ℝ}
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ} (N_nonzero : 0 < N) :
    trapezoidal_error f N a b ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  -- Standard case: a < b
  · have : [[a, b]] = Icc a b := uIcc_of_lt h_lt
    rw [this] at h_df h_ddf h_ddf_integrable fpp_bound
    have : |b - a| = b - a := abs_of_pos (sub_pos.mpr h_lt)
    rw [this]
    exact trapezoidal_error_le_of_lt h_lt h_df h_ddf h_ddf_integrable fpp_bound N_nonzero
  -- Trivial case: a = b
  · simp [h_eq]
  -- Slightly trickier case: a > b (requires flipping the direction and sign of the true and
  -- approximate integrals)
  · have : [[a, b]] = Icc b a := uIcc_of_gt h_gt
    rw [this] at h_df h_ddf h_ddf_integrable fpp_bound
    have : |b - a| = a - b := by rw [abs_of_neg (sub_neg.mpr h_gt), neg_sub]
    rw [this]
    rw [trapezoidal_error_symm f N_nonzero a b]
    exact trapezoidal_error_le_of_lt h_gt h_df h_ddf (IntervalIntegrable.symm h_ddf_integrable)
            fpp_bound N_nonzero

/-- The error bound for trapezoidal integration in the slightly weaker, but very common, case where
`f` is `C^2`. -/
theorem trapezoidal_error_le_of_c2 {f : ℝ → ℝ} {a b : ℝ} (h_f_c2 : ContDiffOn ℝ 2 f [[a, b]])
    {ζ : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ}
    (N_nonzero : 0 < N) : trapezoidal_error f N a b ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  -- This use of rcases slightly duplicates effort from the proof of trapezoidal_error_le, but doing
  -- it any other way that I can think of would be worse.
  rcases eq_or_ne a b with h_eq | h_neq
  · simp [h_eq]
  -- Once we have a ≠ b, all the necessary assumptions on f follow pretty quickly from its being
  -- C^2.
  have ud : UniqueDiffOn ℝ [[a, b]] := uniqueDiffOn_Icc (inf_lt_sup.mpr h_neq)
  have h_df : DifferentiableOn ℝ f [[a, b]] := ContDiffOn.differentiableOn h_f_c2 one_le_two
  have h_ddf : DifferentiableOn ℝ (derivWithin f [[a, b]]) [[a, b]] := by
    have : derivWithin f [[a, b]] = iteratedDerivWithin 1 f [[a, b]] := by
      ext x
      rw [iteratedDerivWithin_one]
    rw [this]
    exact ContDiffOn.differentiableOn_iteratedDerivWithin h_f_c2 (by norm_cast) ud
  have h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f [[a, b]]) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ContDiffOn.continuousOn_iteratedDerivWithin h_f_c2 (le_refl 2) ud
  exact trapezoidal_error_le h_df h_ddf h_ddf_integrable fpp_bound N_nonzero
