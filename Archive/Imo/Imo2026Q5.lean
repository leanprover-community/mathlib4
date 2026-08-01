/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# IMO 2026 Q5

Let `ℝ₊` be the set of positive real numbers. Determine all functions `f : ℝ₊ → ℝ₊` such that
`√((x ^ 2 + f y ^ 2) / 2) ≥ (f x + y) / 2 ≥ √(x * f y)`
for all `x, y ∈ ℝ₊`.

The solutions are the translations `f x = x + c`, where `c ≥ 0`.

## Solution

Write `d x = f x - x` for the displacement of `x`. Squaring the upper inequality bounds
`(f x + y) ^ 2 - (x + f y) ^ 2` by `(x - f y) ^ 2`, while squaring the lower inequality gives
the same bound for its negation. Factoring the difference of squares gives the key estimate
`|d x - d y| * (f x + y + x + f y) ≤ (x - f y) ^ 2`.

Substituting `x = f y` into the original inequalities shows that `d (f y) = d y`. Consequently,
the iterates of `f` form the arithmetic progression `f^[n] x = x + n * d x`. Since all these
iterates are positive, `d x` cannot be negative.

Next suppose that `a = d x` and `b = d y` are both positive but unequal. Choose `n` sufficiently
large and set `m = ⌊(f^[n + 1] y - x) / a⌋`. Since `f^[m] x = x + m * a`, the definition of the
floor ensures `0 ≤ f^[n + 1] y - f^[m] x < a`. Applying the key estimate to `f^[m] x` and
`f^[n] y` now makes its right-hand side less than `a ^ 2`; the choice of `n` makes its left-hand
side greater than `a ^ 2`, a contradiction. Thus all positive displacements have the same value.

Finally, the key estimate shows that a point with positive displacement `a` has distance at least
`a` from every point with zero displacement. Hence the displacement is locally constant on the
positive reals. Since the positive reals are connected, the displacement is constant, giving
`f x = x + c` with `c ≥ 0`. A direct calculation verifies that every such translation is a
solution.
-/

namespace Imo2026Q5

/-- The pair of inequalities in the problem. Positivity of `f` on positive inputs is kept as a
separate hypothesis because `f` is represented as a function on all of `ℝ`. -/
def IsSolution (f : ℝ → ℝ) : Prop :=
  ∀ x > 0, ∀ y > 0, √((x ^ 2 + f y ^ 2) / 2) ≥ (f x + y) / 2 ∧ (f x + y) / 2 ≥ √(x * f y)

variable {f : ℝ → ℝ} {x y : ℝ}

/-- The key estimate: the two inequalities in the problem control the difference between the
displacements at two positive inputs. -/
lemma displacement_control (hf : ∀ x > 0, 0 < f x) (h : IsSolution f) (hx : 0 < x) (hy : 0 < y) :
    |(f x - x) - (f y - y)| * (f x + y + x + f y) ≤ (x - f y) ^ 2 := by
  rcases h x hx y hy with ⟨hupper, hlower⟩
  obtain ⟨hfx, hfy⟩ : 0 < f x ∧ 0 < f y := ⟨hf x hx, hf y hy⟩
  have hmid_nonneg : 0 ≤ (f x + y) / 2 := by positivity
  have hupper_sq : ((f x + y) / 2) ^ 2 ≤ (x ^ 2 + f y ^ 2) / 2 := by grind [sq_le_sq₀, Real.sq_sqrt]
  have hlower_sq : x * f y ≤ ((f x + y) / 2) ^ 2 := by
    rw [← Real.sq_sqrt (show 0 ≤ x * f y by positivity)]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hmid_nonneg).2 hlower
  have habs_sq : |(f x + y) ^ 2 - (x + f y) ^ 2| ≤ (x - f y) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [← abs_of_pos (show 0 < f x + y + x + f y by positivity), ← abs_mul]
  rwa [show ((f x - x) - (f y - y)) * (f x + y + x + f y) = (f x + y) ^ 2 - (x + f y) ^ 2 by ring]

/-- Every iterate of a positive input remains positive. -/
lemma iterate_pos (hf : ∀ x > 0, 0 < f x) (hx : 0 < x) (n : ℕ) : 0 < f^[n] x := by
  induction n with
  | zero => simpa
  | succ n ih => simpa [Function.iterate_succ_apply'] using hf _ ih

/-- The iterates of a positive input form an arithmetic progression whose common difference is
`f x - x`. -/
lemma iterate_eq_add_mul_displacement (hf : ∀ x > 0, 0 < f x) (h : IsSolution f)
    (hx : 0 < x) (n : ℕ) : f^[n] x = x + n * (f x - x) := by
  have hstep {y : ℝ} (hy : 0 < y) : f (f y) - f y = f y - y := by
    rcases h (f y) (hf y hy) y hy with ⟨hupper, hlower⟩
    simp [Real.sqrt_sq (hf y hy).le, Real.sqrt_mul_self (hf y hy).le] at hupper hlower
    nlinarith
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (hf x hx), hstep hx]
    push_cast
    ring

/-- The displacement `f x - x` is nonnegative at every positive input. -/
lemma displacement_nonneg (hf : ∀ x > 0, 0 < f x) (h : IsSolution f) (hx : 0 < x) : 0 ≤ f x - x := by
  by_contra! hneg
  obtain ⟨n, hn_large⟩ := exists_nat_gt (x / (x - f x))
  have hiter_pos := iterate_pos hf hx n
  rw [iterate_eq_add_mul_displacement hf h hx n] at hiter_pos
  nlinarith [(div_lt_iff₀ (by linarith : 0 < x - f x)).1 hn_large]

/-- The displacement is constant along the forward orbit of a positive input. -/
lemma displacement_iterate_eq (hf : ∀ x > 0, 0 < f x) (h : IsSolution f)
    (hx : 0 < x) (n : ℕ) : f (f^[n] x) - f^[n] x = f x - x := by
  rw [show f (f^[n] x) = f^[n.succ] x by simp [Function.iterate_succ_apply']]
  have hsucc := iterate_eq_add_mul_displacement hf h hx n.succ
  push_cast at hsucc
  nlinarith [iterate_eq_add_mul_displacement hf h hx n]

/-- Any two strictly positive displacements are equal. -/
lemma displacement_eq_of_pos (hf : ∀ x > 0, 0 < f x) (h : IsSolution f)
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 < f x - x) (hfy : 0 < f y - y) : f x - x = f y - y := by
  set a := f x - x
  set b := f y - y
  obtain ⟨ha, hb⟩ : 0 < a ∧ 0 < b := ⟨hfx, hfy⟩
  by_contra hne
  have habs_pos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn_large⟩ := exists_nat_gt (max (x / b) (a ^ 2 / (|a - b| * b)))
  have hy_succ : f (f^[n] y) = y + ((n : ℝ) + 1) * b := by
    simpa [Function.iterate_succ_apply', Nat.cast_succ] using
      iterate_eq_add_mul_displacement hf h hy n.succ
  set m := Nat.floor ((f (f^[n] y) - x) / a)
  have hcontra : a ^ 2 < a ^ 2 := calc
    _ < n * (|a - b| * b) := by
      rw [← div_lt_iff₀ (mul_pos habs_pos hb)]
      grind
    _ < |a - b| * f (f^[n] y) := by nlinarith
    _ < |a - b| * (f (f^[m] x) + f^[n] y + f^[m] x + f (f^[n] y)) := by
      apply mul_lt_mul_of_pos_left _ habs_pos
      linarith [hf _ (iterate_pos hf hx m), iterate_pos hf hx m, iterate_pos hf hy n]
    _ ≤ (f (f^[n] y) - f^[m] x) ^ 2 := by
      have hcontrol :=
        displacement_control hf h (iterate_pos hf hx m) (iterate_pos hf hy n)
      rw [displacement_iterate_eq hf h hx m, displacement_iterate_eq hf h hy n] at hcontrol
      nlinarith
    _ < _ := by
      have hxn : x < (n : ℝ) * b := (div_lt_iff₀ hb).1 (by grind)
      apply (sq_lt_sq₀ ?_ ha.le).2
      · rw [iterate_eq_add_mul_displacement hf h hx m]
        have hlt : (f (f^[n] y) - x) / a < (m : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        linarith [(div_lt_iff₀ ha).1 hlt]
      · rw [iterate_eq_add_mul_displacement hf h hx m]
        have hnonneg : 0 ≤ (f (f^[n] y) - x) / a :=
          div_nonneg (by rw [hy_succ]; nlinarith) ha.le
        nlinarith [(le_div_iff₀ ha).1 (Nat.floor_le hnonneg)]
  exact (lt_self_iff_false (a ^ 2)).mp hcontra

/-- A point with positive displacement `a` is at least distance `a` from every point with zero
displacement. -/
lemma displacement_le_dist_of_eq_zero (hf : ∀ x > 0, 0 < f x) (h : IsSolution f)
    {p q a : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hp' : f p - p = a) (hq' : f q - q = 0) : a ≤ dist p q := by
  by_contra! hdist
  have hcontrol := displacement_control hf h hp hq
  rw [hp', hq', sub_zero, abs_of_pos ha] at hcontrol
  nlinarith [(sq_lt_sq₀ (abs_nonneg (p - q)) ha.le).2 hdist, sq_abs (p - q)]

/-- The displacement `f x - x` is constant on the positive reals. -/
lemma displacement_eq (hf : ∀ x > 0, 0 < f x) (h : IsSolution f) (hx : 0 < x) (hy : 0 < y) :
    f x - x = f y - y := by
  have hnonneg {t : ℝ} (ht : 0 < t) : 0 ≤ f t - t := displacement_nonneg hf h ht
  by_cases hex : ∃ z : ℝ, 0 < z ∧ 0 < f z - z
  · obtain ⟨z, hz, hfz⟩ := hex
    have hzero_or_eq {t : ℝ} (ht : 0 < t) :
        f t - t = 0 ∨ f t - t = f z - z := by
      grind [displacement_eq_of_pos hf h]
    set d : Set.Ioi (0 : ℝ) → ℝ := fun t ↦ f t - t
    have hnear (p q : Set.Ioi (0 : ℝ)) (hpq : dist p q < f z - z) : d p = d q := by
      have hpq_sep :=
        displacement_le_dist_of_eq_zero hf h p.property q.property hfz
      have hqp_sep :=
        displacement_le_dist_of_eq_zero hf h q.property p.property hfz
      rcases hzero_or_eq p.property with hp₀ | hp₁ <;>
      rcases hzero_or_eq q.property with hq₀ | hq₁
      all_goals grind [Subtype.dist_eq, dist_comm]
    have hloc : IsLocallyConstant d := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro p
      filter_upwards [Metric.ball_mem_nhds p hfz] with q hq using hnear q p hq
    have : PreconnectedSpace (Set.Ioi (0 : ℝ)) := Subtype.preconnectedSpace isPreconnected_Ioi
    exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  · grind

/-- The solutions to IMO 2026 Q5 are precisely the nonnegative translations on `ℝ₊`. -/
theorem imo2026_q5 (hf : ∀ x > 0, 0 < f x) : IsSolution f ↔ ∃ c ≥ 0, ∀ x > 0, f x = x + c := by
  constructor
  · intro hcond
    refine ⟨f 1 - 1, displacement_nonneg hf hcond zero_lt_one, fun x hx ↦ ?_⟩
    linarith [displacement_eq hf hcond hx zero_lt_one]
  · rintro ⟨c, hc, htrans⟩
    intro x hx y hy
    rw [htrans x hx, htrans y hy]
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (x - y - c)])
    · exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith [sq_nonneg (x - y - c)]⟩

end Imo2026Q5
