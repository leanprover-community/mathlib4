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
  (trapezoidal_integral f N a b) - (∫ x in a..b, f x)

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
    trapezoidal_error f N a b = -trapezoidal_error f N b a := by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b, integral_symm, neg_sub_neg, neg_sub]

/-- Just like exact integration, the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
theorem trapezoidal_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_integral f N a a = 0 := by
  simp [trapezoidal_integral]

/-- The error of the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
theorem trapezoidal_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_error f N a a = 0 := by
  simp [trapezoidal_error]

@[simp]
theorem trapezoidal_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    trapezoidal_integral f 1 a b = (b - a) / 2 * (f a + f b) := by
  simp [trapezoidal_integral, mul_comm_div]

/-- A basic trapezoidal equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems are certainly possible, but many of them can be derived from repeated applications
of this one. -/
theorem sum_trapezoidal_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : N > 0) : ∑ i ∈ range N, trapezoidal_integral f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_integral f N a (a + N * h) := by
  simp only [trapezoidal_integral_one]
  unfold trapezoidal_integral
  simp only [add_sub_cancel_left]
  field_simp
  rw [sum_mul]
  field_simp
  have (x : ℕ) : (x + 1) * h - x * h = h := by ring
  simp_rw [this]
  have (x : ℕ) : (a * N + (x + 1) * (N * h)) / N = a + (x + 1) * h := by
    field_simp
    ring
  simp_rw [this]
  rw [← mul_sum, sum_add_distrib]
  congr 1
  let K := N - 1 -- We'll use an induction, so use K to allow us to start from 0, not 1.
  rw [((Nat.sub_eq_iff_eq_add N_nonzero).mp rfl : N = K + 1)]
  simp only [add_tsub_cancel_right]
  have : ∑ x ∈ range (K + 1), f (a + x * h) = f a + ∑ x ∈ range K, f (a + (x + 1) * h) := by
    induction' K with k hk
    · simp
    · rw [sum_range_succ]
      nth_rw 2 [sum_range_succ]
      rw [hk, add_assoc]
      norm_cast
  rw [this]
  have : ∑ x ∈ Finset.range (K + 1), f (a + (x + 1) * h)
      = f (a + (K + 1) * h) + ∑ x ∈ range K, f (a + (x + 1) * h) := by
    rw [sum_range_succ]
    ring
  rw [this]
  norm_cast
  ring

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
theorem trapezoidal_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : N > 0) :
    trapezoidal_integral f N a (a + N * h) + trapezoidal_integral f 1 (a + N * h) (a + (N + 1) * h)
      = trapezoidal_integral f (N + 1) a (a + (N + 1) * h) := by
  norm_cast
  rw [← sum_trapezoidal_integral_adjacent_intervals N_nonzero,
      ← sum_trapezoidal_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1),
      sum_range_succ]
  norm_cast

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and trapezoidal integration,
it's natural to combine them into a similar formula for the error.  This theorem is in particular
used in the proof of the general error bound. -/
theorem sum_trapezoidal_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : N > 0)
    (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i ∈ range N, trapezoidal_error f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_error f N a (a + N * h) := by
  unfold trapezoidal_error
  rw [sum_sub_distrib, sum_trapezoidal_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals (a := (a + · * h))]
  · simp
  · intro k hk
    apply IntervalIntegrable.mono h_f_int ?_ (le_refl volume)
    rcases lt_trichotomy h 0 with h_neg | h_zero | h_pos
    · field_simp
      have : N * h < 0 := mul_neg_of_pos_of_neg (Nat.cast_pos'.mpr N_nonzero) h_neg
      have : a > a + N * h := add_lt_iff_neg_left.mpr this
      have : [[a, a + N * h]] = Icc (a + N * h) a := uIcc_of_gt this
      rw [this]
      refine Icc_subset_Icc ?_ ?_
      · rw [add_le_add_iff_left, mul_le_mul_right_of_neg h_neg]
        norm_cast
      · nlinarith
    · grind
    · field_simp
      have : N * h > 0 := mul_pos (Nat.cast_pos'.mpr N_nonzero) h_pos
      have : a < a + N * h := lt_add_of_pos_right a this
      have : [[a, a + N * h]] = Icc a (a + N * h) := uIcc_of_lt this
      rw [this]
      refine Icc_subset_Icc ?_ ?_
      · nlinarith
      · rw [add_le_add_iff_left, mul_le_mul_iff_of_pos_right h_pos]
        norm_cast

/-- A special case of the error bound for trapeozidal integration. The vast majority of the calculus
in the proof is done here. The final bound is given in a slightly different form than usual (with
the `b-a` at the end rather than at the start) to make it easier to use in the full proof. -/
lemma trapezoidal_error_two_points {f : ℝ → ℝ} {ζ : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (h_df : DifferentiableOn ℝ f (Icc a b))
    (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a b)
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ) :
    |trapezoidal_error f 1 a b| ≤ ζ / 12 * (b - a) ^ 3 := by
  have h_cf : ContinuousOn f (Icc a b) := DifferentiableOn.continuousOn h_df
  let g (t : ℝ) := trapezoidal_error f 1 a (a + t)
  let h := b - a
  have h_gt_zero := sub_pos.mpr a_lt_b
  -- Hand-computed expressions for g' and g''. We will differentiate g twice, find that
  -- g''(t) ≤ (ζ / 2) * t, and then integrate twice.
  let dg (t : ℝ) :=
      (1 / 2) * (f a + f (a + t))
      + (t / 2) * (derivWithin f (Icc a b) (a + t)) - f (a + t)
  let ddg (t : ℝ) := (t / 2) * (iteratedDerivWithin 2 f (Icc a b) (a + t))
  -- This particular lemma will come in handy a couple of times.
  have comp_deriv {f : ℝ → ℝ} (h_df: DifferentiableOn ℝ f (Icc a b)) {y : ℝ}
      (hy: y ∈ Icc 0 h) : HasDerivWithinAt (fun x ↦ f (a + x))
      (derivWithin f (Icc a b) (a + y)) (Icc 0 h) y := by
    apply HasDerivWithinAt.mono (t := Icc (a - a) (b - a))
    pick_goal 2
    · apply Set.Icc_subset_Icc
      · linarith
      · exact le_tsub_of_add_le_left (by unfold h; linarith)
    have : derivWithin f (Icc a b) (a + y) =
        derivWithin (fun x ↦ f (a + x)) (Icc (a - a) (b - a)) y := by
      rw [derivWithin_comp_const_add f a (Icc (a - a) (b - a)) y]
      simp
    rw [this]
    apply DifferentiableWithinAt.hasDerivWithinAt
    apply DifferentiableWithinAt.comp (t := Icc a b)
    · have : a + y ∈ Icc a b := by
        constructor
        · exact (le_add_iff_nonneg_right _).mpr hy.left
        · exact le_sub_iff_add_le'.mp hy.right
      exact h_df _ this
    · fun_prop
    · intro x hx
      exact ⟨tsub_le_iff_left.mp hx.left, le_sub_iff_add_le'.mp hx.right⟩
  -- Compute g' by applying standard derivative identities.
  have h_dg (y : ℝ) (hy: y ∈ Icc 0 h) : HasDerivWithinAt g (dg y) (Icc 0 h) y := by
    unfold g trapezoidal_error trapezoidal_integral
    simp only [add_sub_cancel_left, Nat.cast_one, div_one, tsub_self, Finset.range_zero, sum_empty,
      add_zero]
    simp_rw [← mul_comm_div]
    refine fun_sub (fun_mul (div_const (hasDerivWithinAt_id _ _) _)
      (const_add _ (comp_deriv h_df hy))) ?_
    · nth_rewrite 1 [← add_zero a]
      simp_rw [← integral_comp_add_left f a]
      -- We now want to apply FToC and be done with it, but we'll need to prove that
      have h_cont : ContinuousOn (fun x ↦ f (a + x)) (Icc 0 h) :=
        have : MapsTo (HAdd.hAdd a) (Set.Icc 0 (b - a)) (Set.Icc a b) := by
          have := Monotone.mapsTo_Icc (f := HAdd.hAdd a) (a := 0) (b := b - a) add_left_mono
          simpa
        h_cf.comp' (by fun_prop) this
      have := Fact.mk hy -- Needed for integral_hasDerivWithinAt_right
      apply integral_hasDerivWithinAt_right
      · apply ContinuousOn.intervalIntegrable_of_Icc hy.left
        apply ContinuousOn.mono h_cont
        exact Set.Icc_subset_Icc (le_refl 0) hy.right
      · exact ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin h_cont measurableSet_Icc y
      · exact ContinuousOn.continuousWithinAt h_cont hy
  -- Compute g'', once again applying standard derivative identities.
  have h_ddg (y : ℝ) (hx: y ∈ Icc 0 h) : HasDerivWithinAt (dg) (ddg y) (Icc 0 h) y := by
    -- The eventual expression for g'' has several terms that cancel, which we have to undo here
    -- so that the various HasDerivWithinAt theorems will have everything they need.
    let dfaky := derivWithin f (Icc a b) (a + y)
    rw [(by ring: ddg y = (1 / 2) * dfaky + ((1 / 2) * dfaky + ddg y) - dfaky)]
    refine fun_sub (fun_add (const_mul _ (const_add _ (comp_deriv h_df hx)))
      (fun_mul (div_const (hasDerivWithinAt_id _ _) _) ?_)) (comp_deriv h_df hx)
    rw [iteratedDerivWithin_eq_iterate]
    exact comp_deriv h_ddf hx
  -- Technically this would work for all x ≥ 0, but we only need it for x ∈ Icc 0 h (and it makes
  -- more pure-mathematical sense that way).
  have bound_ddg : ∀ x ∈ Icc 0 h, |ddg x| ≤ (ζ / 2) * (x ^ 1) := by
    intro x hx
    calc
      _ = |x / 2| * |iteratedDerivWithin 2 f (Icc a b) (a + x)| := abs_mul _ _
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
  -- ddg.)
  have gk_continuous : ContinuousOn g (Icc 0 h) := by
    intro y hy
    apply HasDerivWithinAt.continuousWithinAt
    exact h_dg y hy
  have dgk_continuous : ContinuousOn dg (Icc 0 h) := by
    intro y hy
    apply HasDerivWithinAt.continuousWithinAt
    exact h_ddg y hy
  have dgk_integrable : IntervalIntegrable dg volume 0 h :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt h_gt_zero) dgk_continuous
  have ddgk_integrable : IntervalIntegrable ddg volume 0 h := by
    apply IntervalIntegrable.continuousOn_mul
    · have : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a (a + h) := by simpa [h]
      have := IntervalIntegrable.comp_add_left (this) a
      simpa
    · fun_prop
  have := power_bound (integral_from_zero h_ddg (by unfold dg; ring_nf: dg 0 = 0)
    dgk_continuous ddgk_integrable) bound_ddg
  have := power_bound (integral_from_zero h_dg (by simp [g]: g 0 = 0) gk_continuous
    dgk_integrable) this
  have := this h (right_mem_Icc.mpr (le_of_lt h_gt_zero))
  unfold g h at this
  ring_nf at this
  linarith

/-- The hard part of the trapezoidal rule error bound: proving it in the case of a non-empty closed
interval with ordered endpoints. -/
lemma trapezoidal_error_le_of_lt {f : ℝ → ℝ} {ζ : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (h_df : DifferentiableOn ℝ f (Icc a b))
    (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a b)
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ)
    {N : ℕ} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| ≤ (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
  let h := (b - a) / N
  -- Make continuity of f explicit so that fun_prop can use it in a couple of places later on.
  have h_cf : ContinuousOn f (Icc a b) := DifferentiableOn.continuousOn h_df
  -- Make it explicit that 0 < h.
  have h_gt_zero : 0 < h := div_pos (sub_pos.mpr a_lt_b) (Nat.cast_pos.mpr N_nonzero)
  -- Let a_k (written ak k) be the k-th integration point for the trapezoidal rule, and define
  -- (g k)(t) to be the error of integrating from a_k to a_k + t using a linear approximation.
  let ak (k : ℕ) := a + k * h
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
  -- We now want to use what should be a simple application of `trapezoidal_error_two_points`.
  -- However, this requires a little bit of extra work in order to handle the intervals: our axioms
  -- about `f` and its derivatives are all with respect to `Icc a b`, so bringing them into
  -- `Icc (ak k) (ak k + h)` is not trivial.
  have two_point_bound (k : ℕ) (h_range : k ∈ range N) :
      |trapezoidal_error f 1 (ak k) (ak (k + 1))| ≤ (ζ / 12) * h ^ 3 := by
    have h_k_le_n : k < N := List.mem_range.mp h_range
    have : ak (k + 1) = ak k + h := by unfold ak; field_simp; ring
    rw [this]
    have ak_interval : Icc (ak k) (ak k + h) ⊆ Icc a b :=
      Icc_subset_Icc (a_lt_ak h_k_le_n) (ak_h_lt_b h_k_le_n)
    have ak_uInt : [[ak k, ak k + h]] ⊆ [[a, b]] := by
      rwa [uIcc_of_lt a_lt_b, uIcc_of_lt (lt_add_of_pos_right _ h_gt_zero)]
    nth_rw 2 [← add_sub_cancel_left (ak k) h]
    have derivWithin_interval {g : ℝ → ℝ} (h_dg : DifferentiableOn ℝ g (Icc a b)) (x : ℝ)
        (hx : x ∈ Icc (ak k) (ak k + h)):
        derivWithin g (Icc (ak k) (ak k + h)) x = derivWithin g (Icc a b) x := by
      apply derivWithin_subset ak_interval ?_ (h_dg x (ak_interval hx))
      apply UniqueDiffOn.uniqueDiffWithinAt ?_ hx
      exact uniqueDiffOn_Icc (lt_add_of_pos_right _ h_gt_zero)
    have iteratedDerivWithin_interval (x : ℝ) (hx : x ∈ Icc (ak k) (ak k + h)) :
        iteratedDerivWithin 2 f (Icc (ak k) (ak k + h)) x
          = iteratedDerivWithin 2 f (Icc a b) x := by
        rw [iteratedDerivWithin_succ', iteratedDerivWithin_one,
            derivWithin_congr (derivWithin_interval h_df), derivWithin_interval h_ddf x hx]
        · rw [← iteratedDerivWithin_one, ← iteratedDerivWithin_succ']
        · exact derivWithin_interval h_df x hx
    apply trapezoidal_error_two_points
    · exact lt_add_of_pos_right _ h_gt_zero
    · exact h_df.mono ak_interval
    · apply DifferentiableOn.congr ?_ (derivWithin_interval h_df)
      exact h_ddf.mono ak_interval
    · have := h_ddf_integrable.mono ak_uInt (le_refl _)
      refine IntervalIntegrable.congr this ?_
      apply Filter.eventuallyEq_of_mem (s := Icc (ak k) (ak k + h))
      · rw [MeasureTheory.mem_ae_iff, MeasureTheory.Measure.restrict_apply]
        · have : Ι (ak k) (ak k + h) ⊆ Icc (ak k) (ak k + h) := by
            rw [uIoc_of_le (by grind)]
            exact Ioc_subset_Icc_self
          have : (Icc (ak k) (ak k + h))ᶜ ∩ Ι (ak k) (ak k + h) = ∅ := by grind
          rw [this]
          exact OuterMeasureClass.measure_empty volume
        · exact MeasurableSet.compl measurableSet_Icc
      · intro x hx
        exact Eq.symm (iteratedDerivWithin_interval x hx)
    · intro x
      rcases Classical.em (x ∈ Icc (ak k) (ak k + h)) with hx | _
      · rw [iteratedDerivWithin_interval x hx]
        exact fpp_bound x
      · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure]
        · calc
            _ = 0                             := abs_zero
            _ ≤ |iteratedDerivWithin 2 f _ 0| := abs_nonneg _
            _ ≤ _                             := fpp_bound 0
        · rwa [closure_Icc]
  have f_integrable : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt a_lt_b) h_cf
  have : b = a + N * h := by
    unfold h
    field_simp
  rw [this] at f_integrable
  nth_rw 1 [this, ← sum_trapezoidal_error_adjacent_intervals N_nonzero f_integrable]
  grw [abs_sum_le_sum_abs]
  unfold ak at two_point_bound
  norm_cast
  calc
    _ ≤ ∑ x ∈ range N, ζ / 12 * h ^ 3 := sum_le_sum two_point_bound
    _ = N * (ζ / 12 * h ^ 3)          := by simp [sum_const]
    _ = _                             := by unfold h; field_simp; ring

/-- The standard error bound for trapezoidal integration on the general interval `[[a, b]]`. -/
theorem trapezoidal_error_le {f : ℝ → ℝ} {a b : ℝ}
    (h_df : DifferentiableOn ℝ f [[a, b]])
    (h_ddf : DifferentiableOn ℝ (derivWithin f [[a, b]]) [[a, b]])
    (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f [[a, b]]) volume a b) {ζ : ℝ}
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
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
    rw [trapezoidal_error_symm f N_nonzero a b, abs_neg]
    exact trapezoidal_error_le_of_lt h_gt h_df h_ddf (IntervalIntegrable.symm h_ddf_integrable)
            fpp_bound N_nonzero

/-- The error bound for trapezoidal integration in the slightly weaker, but very common, case where
`f` is `C^2`. -/
theorem trapezoidal_error_le_of_c2 {f : ℝ → ℝ} {a b : ℝ} (h_f_c2 : ContDiffOn ℝ 2 f [[a, b]])
    {ζ : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ}
    (N_nonzero : 0 < N) : |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
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
