/-
Copyright (c) 2026 Allen Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Goodman
-/
module

public import Mathlib.Topology.Algebra.Ring.Real -- shake: keep (public API boundary)

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bisection method

This file formalizes finite iteration and convergence of the bisection method for a real-valued
function defined on a fixed closed interval `[a, b]`.

The endpoints of every intermediate interval have type `Set.Icc a b`, so the algorithm never
evaluates the function outside its domain. A state brackets `f` when the product of its endpoint
values is nonpositive. Starting from a bracketed state, each step retains a half with the same
property, so one approximation sequence handles both endpoint-sign orientations without negating
the function. Every `Bisection.State` includes a proof that its endpoints are ordered, so nesting
and width results need no separate endpoint-order hypotheses.

The core `Bisection.State` API accepts functions of type `Set.Icc a b → ℝ`. This makes domain
safety explicit and supports functions that are defined only on the starting interval. For
convenience, the real-facing API accepts functions of type `ℝ → ℝ` and delegates to the core
API after restricting them with `Set.domRestrict`.

This is an exact, noncomputable real-number iteration rather than a floating-point implementation.
Degenerate intervals with `a = b` are supported. If the midpoint is already a root,
`Bisection.State.step` retains the left half with that root as its right endpoint and continues
instead of stopping early. The iteration and its convergence theory need neither continuity nor an
initial bracket. An initial nonpositive endpoint-value product is preserved by iteration, and
continuity is additionally required for root-existence and root-identification results.

## Main definitions

* `Bisection.State`: the endpoints of the current subinterval.
* `Bisection.State.Brackets`: the nonpositive endpoint-value product invariant.
* `Bisection.State.leftHalf` and `Bisection.State.rightHalf`: the two halves of a state.
* `Bisection.State.step`: one bisection step.
* `Bisection.State.iterate`: a finite number of bisection steps.
* `Bisection.State.approximation`: the midpoint after finitely many steps.
* `Bisection.State.limit`: the canonical limit of the midpoint approximations.
* `Bisection.approximation`: the real-valued midpoint approximation for a function `ℝ → ℝ`.
* `Bisection.limit`: the canonical real-valued limit of the midpoint approximations.

## Main results

* `Bisection.State.Brackets.iterate`: finite iteration preserves the nonpositive endpoint-value
  product.
* `Bisection.State.width_iterate` and `Bisection.State.Icc_iterate_antitone`: after `n` steps the
  width is divided by `2 ^ n`, and the iterated closed intervals are nested.
* `Bisection.State.forall_mem_Icc_iterate_iff_eq_limit` and
  `Bisection.State.existsUnique_forall_mem_Icc_iterate`: the canonical limit is the unique point
  common to all the nested intervals.
* `Bisection.State.tendsto_approximation_limit` and
  `Bisection.State.dist_approximation_limit_le`: the midpoint approximations converge to the
  canonical limit with the standard error bound.
* `Bisection.State.Brackets.apply_limit_eq_zero`: for a continuous function, its value at the
  canonical limit is zero.
* `Bisection.approximation_congr`, `Bisection.limit_congr`, `Bisection.approximation_neg`, and
  `Bisection.limit_neg`: the real-facing approximations and limit depend only on the function on
  `[a, b]` and are unchanged by negation.
* `Bisection.tendsto_approximation_limit` and `Bisection.dist_approximation_limit_le`: the
  real-valued approximations converge to the real-valued canonical limit with the standard error
  bound.
* `Bisection.apply_limit_eq_zero_of_continuousWithinAt` and
  `Bisection.apply_limit_eq_zero`: continuity within the starting interval at the canonical limit
  suffices to identify it as a root; continuity on the whole interval is a convenient corollary.
* `Bisection.exists_root_tendsto_approximation`: for a continuous real function with a
  nonpositive endpoint-value product, the approximations converge to a root in `[a, b]` with the
  standard error bound.

## Example

The functions `x ↦ x - 1` and `x ↦ 1 - x` have opposite endpoint-sign orientations on `[0, 2]`.
The theorem `Bisection.approximation_neg` shows that their entire approximation sequences agree.
The second example applies the main real-facing theorem to `x ↦ x ^ 2 - 2` on `[1, 2]`, where the
root is not the initial midpoint, to obtain convergence and the standard error bound.

```lean
open Filter Set Topology

example :
    Bisection.approximation (a := 0) (b := 2) (by norm_num) (fun x : ℝ ↦ 1 - x) =
      Bisection.approximation (a := 0) (b := 2) (by norm_num) (fun x : ℝ ↦ x - 1) := by
  funext n
  simpa [neg_sub] using
    Bisection.approximation_neg (a := 0) (b := 2) (by norm_num) (fun x : ℝ ↦ x - 1) n

example :
    ∃ x ∈ Icc (1 : ℝ) 2, x ^ 2 - 2 = 0 ∧
      Tendsto
        (Bisection.approximation (a := 1) (b := 2) (by norm_num)
          (fun x : ℝ ↦ x ^ 2 - 2))
        atTop (𝓝 x) ∧
      ∀ n,
        dist
            (Bisection.approximation (a := 1) (b := 2) (by norm_num)
              (fun x : ℝ ↦ x ^ 2 - 2) n)
            x ≤ (2 - 1) / (2 : ℝ) ^ (n + 1) := by
  simpa using
    Bisection.exists_root_tendsto_approximation
      (a := 1) (b := 2) (f := fun x : ℝ ↦ x ^ 2 - 2)
      (by norm_num) (by fun_prop) (by norm_num)
```
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace Bisection

/-! ### Bisection states and one-step operations -/

/-- The endpoints of a subinterval of the fixed interval `[a, b]`. -/
@[ext]
structure State (a b : ℝ) where
  /-- The left endpoint of the current subinterval. -/
  left : Icc a b
  /-- The right endpoint of the current subinterval. -/
  right : Icc a b
  /-- The left endpoint does not exceed the right endpoint. -/
  left_le_right : left ≤ right

namespace State

variable {a b : ℝ}

/-- The state corresponding to the whole interval `[a, b]`. -/
def initial (hab : a ≤ b) : State a b :=
  ⟨⟨a, left_mem_Icc.mpr hab⟩, ⟨b, right_mem_Icc.mpr hab⟩, hab⟩

/-- The left endpoint of the initial state is `a`. -/
@[simp]
theorem initial_left (hab : a ≤ b) :
    (initial hab).left = ⟨a, left_mem_Icc.mpr hab⟩ :=
  rfl

/-- The right endpoint of the initial state is `b`. -/
@[simp]
theorem initial_right (hab : a ≤ b) :
    (initial hab).right = ⟨b, right_mem_Icc.mpr hab⟩ :=
  rfl

/-- The midpoint of a bisection state. -/
def midpoint (s : State a b) : Icc a b :=
  ⟨((s.left : ℝ) + (s.right : ℝ)) / 2, by
    constructor
    · linarith [s.left.property.1, s.right.property.1]
    · linarith [s.left.property.2, s.right.property.2]⟩

/-- The coercion of a bisection midpoint to `ℝ`. -/
@[simp]
theorem coe_midpoint (s : State a b) :
    (s.midpoint : ℝ) = ((s.left : ℝ) + (s.right : ℝ)) / 2 :=
  rfl

/-- The width of a bisection state. -/
def width (s : State a b) : ℝ :=
  (s.right : ℝ) - (s.left : ℝ)

/-- The width of a bisection state is nonnegative. -/
theorem width_nonneg (s : State a b) : 0 ≤ s.width := by
  rw [width, sub_nonneg]
  exact s.left_le_right

/-- The endpoint values of a state have nonpositive product for `f`. -/
def Brackets (s : State a b) (f : Icc a b → ℝ) : Prop :=
  f s.left * f s.right ≤ 0

/-- Negating a function does not change whether a state brackets it. -/
@[simp]
theorem brackets_neg (s : State a b) (f : Icc a b → ℝ) :
    s.Brackets (fun x ↦ -f x) ↔ s.Brackets f := by
  simp [Brackets]

/-- The midpoint lies between the endpoints of a bisection state. -/
theorem midpoint_mem_Icc (s : State a b) :
    s.midpoint ∈ Icc s.left s.right := by
  change (s.left : ℝ) ≤ ((s.left : ℝ) + (s.right : ℝ)) / 2 ∧
    ((s.left : ℝ) + (s.right : ℝ)) / 2 ≤ (s.right : ℝ)
  have h := s.left_le_right
  change (s.left : ℝ) ≤ (s.right : ℝ) at h
  constructor <;> linarith

/-- The left half of a bisection state. -/
def leftHalf (s : State a b) : State a b :=
  ⟨s.left, s.midpoint, (midpoint_mem_Icc s).1⟩

/-- The right half of a bisection state. -/
def rightHalf (s : State a b) : State a b :=
  ⟨s.midpoint, s.right, (midpoint_mem_Icc s).2⟩

/-- The left endpoint of the left half is unchanged. -/
@[simp]
theorem leftHalf_left (s : State a b) : s.leftHalf.left = s.left :=
  rfl

/-- The right endpoint of the left half is the midpoint. -/
@[simp]
theorem leftHalf_right (s : State a b) : s.leftHalf.right = s.midpoint :=
  rfl

/-- The left endpoint of the right half is the midpoint. -/
@[simp]
theorem rightHalf_left (s : State a b) : s.rightHalf.left = s.midpoint :=
  rfl

/-- The right endpoint of the right half is unchanged. -/
@[simp]
theorem rightHalf_right (s : State a b) : s.rightHalf.right = s.right :=
  rfl

/-- Taking the left half halves the width. -/
@[simp]
theorem width_leftHalf (s : State a b) : s.leftHalf.width = s.width / 2 := by
  simp [leftHalf, width]
  ring

/-- Taking the right half halves the width. -/
@[simp]
theorem width_rightHalf (s : State a b) : s.rightHalf.width = s.width / 2 := by
  simp [rightHalf, width]
  ring

/-- Retain the left half when its endpoint-value product is nonpositive, and otherwise the right
half. -/
def step (s : State a b) (f : Icc a b → ℝ) : State a b :=
  if f s.left * f s.midpoint ≤ 0 then s.leftHalf else s.rightHalf

/-- A nonpositive left-endpoint/midpoint product makes a step retain the left half. -/
@[simp]
theorem step_of_mul_nonpos {s : State a b} {f : Icc a b → ℝ}
    (h : f s.left * f s.midpoint ≤ 0) : s.step f = s.leftHalf := by
  simp [step, h]

/-- A positive left-endpoint/midpoint product makes a step retain the right half. -/
@[simp]
theorem step_of_mul_pos {s : State a b} {f : Icc a b → ℝ}
    (h : 0 < f s.left * f s.midpoint) : s.step f = s.rightHalf := by
  simp [step, not_le.mpr h]

/-- Negating a function does not change a bisection step. -/
@[simp]
theorem step_neg (s : State a b) (f : Icc a b → ℝ) :
    s.step (fun x ↦ -f x) = s.step f := by
  simp [step]

/-! ### Finite iteration -/

/-- Apply `n` bisection steps to `s`. -/
def iterate (s : State a b) (f : Icc a b → ℝ) : ℕ → State a b
  | 0 => s
  | n + 1 => (s.iterate f n).step f

/-- The midpoint after applying `n` bisection steps. -/
def approximation (s : State a b) (f : Icc a b → ℝ) (n : ℕ) : Icc a b :=
  (s.iterate f n).midpoint

/-- Applying zero bisection steps leaves a state unchanged. -/
@[simp]
theorem iterate_zero (s : State a b) (f : Icc a b → ℝ) : s.iterate f 0 = s :=
  rfl

/-- Applying one more bisection step steps the state after the preceding iterations. -/
@[simp]
theorem iterate_succ (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.iterate f (n + 1) = (s.iterate f n).step f :=
  rfl

/-- Splitting a number of bisection steps at `m` gives the same iterated state. -/
theorem iterate_add (s : State a b) (f : Icc a b → ℝ) (m n : ℕ) :
    s.iterate f (m + n) = (s.iterate f m).iterate f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, iterate_succ, iterate_succ, ih]

/-- Negating a function does not change any finite bisection iterate. -/
@[simp]
theorem iterate_neg (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.iterate (fun x ↦ -f x) n = s.iterate f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterate_succ, ih, step_neg]

/-- The zero-step approximation is the state's midpoint. -/
@[simp]
theorem approximation_zero (s : State a b) (f : Icc a b → ℝ) :
    s.approximation f 0 = s.midpoint :=
  rfl

/-- One more approximation is the midpoint of the state produced by one more step. -/
@[simp]
theorem approximation_succ (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.approximation f (n + 1) = ((s.iterate f n).step f).midpoint :=
  rfl

/-- Negating a function does not change any midpoint approximation. -/
@[simp]
theorem approximation_neg (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.approximation (fun x ↦ -f x) n = s.approximation f n := by
  simp [approximation, iterate_neg]

/-- The initial state's width is the width of the fixed interval. -/
@[simp]
theorem width_initial (hab : a ≤ b) : (initial hab).width = b - a :=
  rfl

/-- One bisection step preserves a nonpositive endpoint-value product. -/
theorem Brackets.step {s : State a b} {f : Icc a b → ℝ} (h : s.Brackets f) :
    (s.step f).Brackets f := by
  unfold Brackets at h ⊢
  by_cases hmid : f s.left * f s.midpoint ≤ 0
  · simp [State.step, hmid, leftHalf]
  · simp only [State.step, ite_eq_right hmid, rightHalf]
    rcases (mul_pos_iff.mp (lt_of_not_ge hmid)) with ⟨hleft, hmid⟩ | ⟨hleft, hmid⟩
    · exact mul_nonpos_of_nonneg_of_nonpos hmid.le (nonpos_of_mul_nonpos_right h hleft)
    · exact mul_nonpos_of_nonpos_of_nonneg hmid.le (nonneg_of_mul_nonpos_right h hleft)

/-- The interval retained by one bisection step is contained in the preceding interval. -/
theorem Icc_step_subset {s : State a b} (f : Icc a b → ℝ) :
    Icc (s.step f).left (s.step f).right ⊆ Icc s.left s.right := by
  intro x hx
  by_cases hmid : f s.left * f s.midpoint ≤ 0
  · simp only [step, ite_eq_left hmid, leftHalf] at hx
    exact ⟨hx.1, hx.2.trans (midpoint_mem_Icc s).2⟩
  · simp only [step, ite_eq_right hmid, rightHalf] at hx
    exact ⟨(midpoint_mem_Icc s).1.trans hx.1, hx.2⟩

/-- One bisection step halves the width. -/
@[simp]
theorem width_step (s : State a b) (f : Icc a b → ℝ) :
    (s.step f).width = s.width / 2 := by
  rw [step]
  split <;> simp

/-- One bisection step moves the midpoint by one quarter of the width. -/
theorem dist_midpoint_step_midpoint (s : State a b) (f : Icc a b → ℝ) :
    dist s.midpoint (s.step f).midpoint = s.width / 4 := by
  have h := s.left_le_right
  change (s.left : ℝ) ≤ s.right at h
  by_cases hmid : f s.left * f s.midpoint ≤ 0
  · simp only [step, ite_eq_left hmid, leftHalf]
    rw [Subtype.dist_eq, Real.dist_eq]
    change
      |((s.left : ℝ) + s.right) / 2 -
          (((s.left : ℝ) + ((s.left : ℝ) + s.right) / 2) / 2)| =
        (s.right - (s.left : ℝ)) / 4
    rw [abs_of_nonneg (by linarith)]
    ring
  · simp only [step, ite_eq_right hmid, rightHalf]
    rw [Subtype.dist_eq, Real.dist_eq]
    change
      |((s.left : ℝ) + s.right) / 2 -
          ((((s.left : ℝ) + s.right) / 2 + s.right) / 2)| =
        (s.right - (s.left : ℝ)) / 4
    rw [abs_of_nonpos (by linarith)]
    ring

/-- Every finite number of bisection steps preserves a nonpositive endpoint-value product. -/
theorem Brackets.iterate {s : State a b} {f : Icc a b → ℝ} (h : s.Brackets f) (n : ℕ) :
    (s.iterate f n).Brackets f := by
  induction n with
  | zero => simpa
  | succ n ih => simpa using ih.step

/-- Every midpoint approximation lies in its current bisection interval. -/
theorem approximation_mem_Icc_iterate (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.approximation f n ∈ Icc (s.iterate f n).left (s.iterate f n).right := by
  exact midpoint_mem_Icc (s.iterate f n)

/-- The left endpoints of the iterated bisection intervals form a monotone sequence. -/
theorem left_iterate_monotone (s : State a b) (f : Icc a b → ℝ) :
    Monotone fun n => (s.iterate f n).left := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [iterate_succ]
  exact (Icc_step_subset f (left_mem_Icc.mpr ((s.iterate f n).step f).left_le_right)).1

/-- The right endpoints of the iterated bisection intervals form an antitone sequence. -/
theorem right_iterate_antitone (s : State a b) (f : Icc a b → ℝ) :
    Antitone fun n => (s.iterate f n).right := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [iterate_succ]
  exact (Icc_step_subset f (right_mem_Icc.mpr ((s.iterate f n).step f).left_le_right)).2

/-- The closed intervals produced by iterated bisection form an antitone sequence. -/
theorem Icc_iterate_antitone (s : State a b) (f : Icc a b → ℝ) :
    Antitone fun n => Icc (s.iterate f n).left (s.iterate f n).right := by
  intro m n hmn x hx
  have hleft := left_iterate_monotone s f hmn
  exact ⟨hleft.trans hx.1,
    hx.2.trans (right_iterate_antitone s f hmn)⟩

/-- Every iterated bisection interval is contained in the starting interval. -/
theorem Icc_iterate_subset (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    Icc (s.iterate f n).left (s.iterate f n).right ⊆ Icc s.left s.right := by
  simpa using Icc_iterate_antitone s f (Nat.zero_le n)

/-- After `n` bisection steps, the width is divided by `2 ^ n`. -/
theorem width_iterate (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    (s.iterate f n).width = s.width / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ, width_step, ih, pow_succ]
      ring

/-! ### Convergence -/

/-- The widths of the iterated bisection intervals converge to zero. -/
theorem tendsto_width_iterate_zero (s : State a b) (f : Icc a b → ℝ) :
    Tendsto (fun n => (s.iterate f n).width) atTop (𝓝 0) := by
  simpa [width_iterate] using
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- The distance between successive midpoint approximations decreases geometrically. -/
theorem dist_approximation_succ {s : State a b} {f : Icc a b → ℝ}
    (n : ℕ) :
    dist (s.approximation f n) (s.approximation f (n + 1)) =
      s.width / (2 : ℝ) ^ (n + 2) := by
  rw [approximation, approximation, iterate_succ,
    dist_midpoint_step_midpoint, width_iterate]
  rw [pow_add]
  norm_num
  ring

/-- The sequence of midpoint approximations is Cauchy. -/
theorem cauchySeq_approximation (s : State a b) (f : Icc a b → ℝ) :
    CauchySeq (s.approximation f) := by
  apply cauchySeq_of_le_geometric_two (C := s.width / 2)
  intro n
  rw [dist_approximation_succ, pow_add]
  norm_num
  ring_nf
  exact le_rfl

/-- The canonical limit of the midpoint approximations. -/
noncomputable def limit (s : State a b) (f : Icc a b → ℝ) : Icc a b :=
  letI : Nonempty (Icc a b) := ⟨s.left⟩
  limUnder atTop (s.approximation f)

/-- The midpoint approximations converge to their canonical limit. -/
theorem tendsto_approximation_limit (s : State a b) (f : Icc a b → ℝ) :
    Tendsto (s.approximation f) atTop (𝓝 (s.limit f)) := by
  rw [limit]
  exact (cauchySeq_approximation s f).tendsto_limUnder

/-- Negating a function does not change the canonical limit of its midpoint approximations. -/
@[simp]
theorem limit_neg (s : State a b) (f : Icc a b → ℝ) :
    s.limit (fun x ↦ -f x) = s.limit f := by
  rw [limit, limit]
  congr 1
  funext n
  exact approximation_neg s f n

/-- The canonical limit belongs to every iterated bisection interval. -/
theorem limit_mem_Icc_iterate (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    s.limit f ∈ Icc (s.iterate f n).left (s.iterate f n).right := by
  refine isClosed_Icc.mem_of_tendsto (tendsto_approximation_limit s f) ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  exact Icc_iterate_antitone s f hm (approximation_mem_Icc_iterate s f m)

private theorem tendsto_of_mem_Icc_iterate {s : State a b} {f : Icc a b → ℝ}
    {u : ℕ → Icc a b} {x : Icc a b}
    (hu : ∀ n, u n ∈ Icc (s.iterate f n).left (s.iterate f n).right)
    (hx : ∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right) :
    Tendsto u atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) (tendsto_width_iterate_zero s f)
  rw [Subtype.dist_eq]
  exact Real.dist_le_of_mem_Icc (hu n) (hx n)

/-- The left endpoints converge to any point common to all the iterated intervals. -/
theorem tendsto_left_iterate {s : State a b} {f : Icc a b → ℝ}
    {x : Icc a b} (hx : ∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right) :
    Tendsto (fun n => (s.iterate f n).left) atTop (𝓝 x) := by
  exact tendsto_of_mem_Icc_iterate
    (fun n ↦ left_mem_Icc.mpr (s.iterate f n).left_le_right) hx

/-- The right endpoints converge to any point common to all the iterated intervals. -/
theorem tendsto_right_iterate {s : State a b} {f : Icc a b → ℝ}
    {x : Icc a b} (hx : ∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right) :
    Tendsto (fun n => (s.iterate f n).right) atTop (𝓝 x) := by
  exact tendsto_of_mem_Icc_iterate
    (fun n ↦ right_mem_Icc.mpr (s.iterate f n).left_le_right) hx

/-- The midpoint approximations converge to any point common to all the iterated intervals. -/
theorem tendsto_approximation {s : State a b} {f : Icc a b → ℝ}
    {x : Icc a b} (hx : ∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right) :
    Tendsto (s.approximation f) atTop (𝓝 x) := by
  exact tendsto_of_mem_Icc_iterate (approximation_mem_Icc_iterate s f) hx

/-- A point belongs to every iterated bisection interval exactly when it is the canonical limit. -/
theorem forall_mem_Icc_iterate_iff_eq_limit {s : State a b} {f : Icc a b → ℝ}
    {x : Icc a b} :
    (∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right) ↔ x = s.limit f := by
  constructor
  · intro hx
    exact tendsto_nhds_unique (tendsto_approximation hx) (tendsto_approximation_limit s f)
  · rintro rfl
    exact limit_mem_Icc_iterate s f

/-- The iterated bisection intervals have a unique common point. -/
theorem existsUnique_forall_mem_Icc_iterate (s : State a b) (f : Icc a b → ℝ) :
    ∃! x, ∀ n, x ∈ Icc (s.iterate f n).left (s.iterate f n).right := by
  refine ⟨s.limit f, limit_mem_Icc_iterate s f, ?_⟩
  intro y hy
  exact forall_mem_Icc_iterate_iff_eq_limit.mp hy

/-- The left endpoints converge to the canonical limit. -/
theorem tendsto_left_iterate_limit (s : State a b) (f : Icc a b → ℝ) :
    Tendsto (fun n => (s.iterate f n).left) atTop (𝓝 (s.limit f)) :=
  tendsto_left_iterate (limit_mem_Icc_iterate s f)

/-- The right endpoints converge to the canonical limit. -/
theorem tendsto_right_iterate_limit (s : State a b) (f : Icc a b → ℝ) :
    Tendsto (fun n => (s.iterate f n).right) atTop (𝓝 (s.limit f)) :=
  tendsto_right_iterate (limit_mem_Icc_iterate s f)

/-! ### Roots and error bounds -/

/-- A continuous function whose endpoint values have nonpositive product has a root in the state
interval. -/
theorem Brackets.exists_eq_zero {s : State a b} {f : Icc a b → ℝ} (h : s.Brackets f)
    (hf : ContinuousOn f (Icc s.left s.right)) : ∃ x ∈ Icc s.left s.right, f x = 0 := by
  have hpre : IsPreconnected (Icc s.left s.right : Set (Icc a b)) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    simpa using (isPreconnected_Icc : IsPreconnected (Icc (s.left : ℝ) s.right))
  rcases (mul_nonpos_iff.mp h) with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hzero : (0 : ℝ) ∈ Icc (f s.right) (f s.left) := ⟨hright, hleft⟩
    exact hpre.intermediate_value (right_mem_Icc.mpr s.left_le_right)
      (left_mem_Icc.mpr s.left_le_right) hf hzero
  · have hzero : (0 : ℝ) ∈ Icc (f s.left) (f s.right) := ⟨hleft, hright⟩
    exact hpre.intermediate_value (left_mem_Icc.mpr s.left_le_right)
      (right_mem_Icc.mpr s.left_le_right) hf hzero

/-- The midpoint is at most half the width away from any point in the state interval. -/
theorem dist_midpoint_le_half_width {s : State a b} {x : Icc a b}
    (hx : x ∈ Icc s.left s.right) : dist s.midpoint x ≤ s.width / 2 := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [midpoint, width]
  change (s.left : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (s.right : ℝ) at hx
  rw [abs_le]
  constructor
  · change -(((s.right : ℝ) - (s.left : ℝ)) / 2) ≤
      ((s.left : ℝ) + (s.right : ℝ)) / 2 - (x : ℝ)
    linarith [hx.2]
  · change ((s.left : ℝ) + (s.right : ℝ)) / 2 - (x : ℝ) ≤
      ((s.right : ℝ) - (s.left : ℝ)) / 2
    linarith [hx.1]

/-- The midpoint after `n` steps is within `width / 2 ^ (n + 1)` of any point in the current
iterated interval. -/
theorem dist_approximation_le {s : State a b} {f : Icc a b → ℝ} {x : Icc a b} (n : ℕ)
    (hx : x ∈ Icc (s.iterate f n).left (s.iterate f n).right) :
    dist (s.approximation f n) x ≤ s.width / (2 : ℝ) ^ (n + 1) := by
  calc
    dist (s.approximation f n) x ≤ (s.iterate f n).width / 2 :=
      dist_midpoint_le_half_width hx
    _ = s.width / (2 : ℝ) ^ (n + 1) := by
      rw [width_iterate, pow_succ]
      ring

/-- The midpoint after `n` steps is within `width / 2 ^ (n + 1)` of the canonical limit. -/
theorem dist_approximation_limit_le (s : State a b) (f : Icc a b → ℝ) (n : ℕ) :
    dist (s.approximation f n) (s.limit f) ≤ s.width / (2 : ℝ) ^ (n + 1) :=
  dist_approximation_le n (limit_mem_Icc_iterate s f n)

/-- After `n` steps, the midpoint is within `width / 2 ^ (n + 1)` of some root. -/
theorem Brackets.exists_root_dist_approximation_le {s : State a b} {f : Icc a b → ℝ}
    (h : s.Brackets f) (hf : ContinuousOn f (Icc s.left s.right)) (n : ℕ) :
    ∃ x ∈ Icc (s.iterate f n).left (s.iterate f n).right,
      f x = 0 ∧ dist (s.approximation f n) x ≤ s.width / (2 : ℝ) ^ (n + 1) := by
  have hn := h.iterate n
  obtain ⟨x, hx, hfx⟩ := hn.exists_eq_zero (hf.mono (Icc_iterate_subset s f n))
  exact ⟨x, hx, hfx, dist_approximation_le n hx⟩

/-- If a function with a nonpositive endpoint-value product is continuous within the state interval
at the canonical limit, then that limit is a root. -/
theorem Brackets.apply_limit_eq_zero_of_continuousWithinAt {s : State a b}
    {f : Icc a b → ℝ}
    (h : s.Brackets f)
    (hf : ContinuousWithinAt f (Icc s.left s.right) (s.limit f)) : f (s.limit f) = 0 := by
  have hleft_mem (n : ℕ) : (s.iterate f n).left ∈ Icc s.left s.right :=
    Icc_iterate_subset s f n (left_mem_Icc.mpr (s.iterate f n).left_le_right)
  have hright_mem (n : ℕ) : (s.iterate f n).right ∈ Icc s.left s.right :=
    Icc_iterate_subset s f n (right_mem_Icc.mpr (s.iterate f n).left_le_right)
  have hleft_within :
      Tendsto (fun n => (s.iterate f n).left) atTop (𝓝[Icc s.left s.right] (s.limit f)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_left_iterate_limit s f, Filter.Eventually.of_forall hleft_mem⟩
  have hright_within :
      Tendsto (fun n => (s.iterate f n).right) atTop (𝓝[Icc s.left s.right] (s.limit f)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_right_iterate_limit s f, Filter.Eventually.of_forall hright_mem⟩
  have hleft : Tendsto (fun n => f (s.iterate f n).left) atTop (𝓝 (f (s.limit f))) :=
    hf.tendsto.comp hleft_within
  have hright : Tendsto (fun n => f (s.iterate f n).right) atTop (𝓝 (f (s.limit f))) :=
    hf.tendsto.comp hright_within
  have hprod :
      Tendsto
        (fun n => f (s.iterate f n).left * f (s.iterate f n).right)
        atTop (𝓝 (f (s.limit f) * f (s.limit f))) :=
    hleft.mul hright
  have hsq_nonpos : f (s.limit f) * f (s.limit f) ≤ 0 :=
    le_of_tendsto' hprod fun n => h.iterate n
  exact mul_self_eq_zero.mp (le_antisymm hsq_nonpos (mul_self_nonneg _))

/-- For a continuous function with a nonpositive endpoint-value product, the canonical limit is a
root. -/
theorem Brackets.apply_limit_eq_zero {s : State a b} {f : Icc a b → ℝ} (h : s.Brackets f)
    (hf : ContinuousOn f (Icc s.left s.right)) : f (s.limit f) = 0 := by
  apply h.apply_limit_eq_zero_of_continuousWithinAt
  exact hf (s.limit f) (by simpa using limit_mem_Icc_iterate s f 0)

end State

/-! ### Real-facing API -/

/-- The midpoint after `n` bisection steps for a real function on `[a, b]`. -/
noncomputable def approximation {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((State.initial hab).approximation ((Icc a b).domRestrict f) n : ℝ)

/-- The zero-step approximation is the midpoint of `[a, b]`. -/
@[simp]
theorem approximation_zero {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    approximation hab f 0 = (a + b) / 2 :=
  rfl

/-- Every real-valued bisection approximation belongs to the starting interval. -/
theorem approximation_mem_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (n : ℕ) :
    approximation hab f n ∈ Icc a b :=
  ((State.initial hab).approximation ((Icc a b).domRestrict f) n).property

/-- Every approximation on a degenerate interval equals its sole endpoint. -/
@[simp]
theorem approximation_self (a : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    approximation (a := a) (b := a) le_rfl f n = a := by
  simpa [Icc_self, mem_singleton_iff] using
    approximation_mem_Icc (a := a) (b := a) le_rfl f n

/-- Bisection gives the same approximations for functions that agree on the starting interval. -/
theorem approximation_congr {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hfg : EqOn f g (Icc a b)) (n : ℕ) : approximation hab f n = approximation hab g n := by
  unfold approximation
  rw [Set.domRestrict_eq_domRestrict_iff.mpr hfg]

/-- Negating a real function does not change any of its bisection approximations. -/
@[simp]
theorem approximation_neg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (n : ℕ) :
    approximation hab (fun x ↦ -f x) n = approximation hab f n := by
  unfold approximation
  exact congrArg Subtype.val
    (State.approximation_neg (State.initial hab) ((Icc a b).domRestrict f) n)

/-- The canonical limit of the real-valued bisection approximations. -/
noncomputable def limit {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : ℝ :=
  ((State.initial hab).limit ((Icc a b).domRestrict f) : ℝ)

/-- Bisection gives the same canonical limit for functions that agree on the starting interval. -/
theorem limit_congr {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hfg : EqOn f g (Icc a b)) :
    limit hab f = limit hab g := by
  unfold limit
  rw [Set.domRestrict_eq_domRestrict_iff.mpr hfg]

/-- Negating a real function does not change the canonical limit of its bisection approximations. -/
@[simp]
theorem limit_neg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    limit hab (fun x ↦ -f x) = limit hab f := by
  unfold limit
  exact congrArg Subtype.val
    (State.limit_neg (State.initial hab) ((Icc a b).domRestrict f))

/-- The canonical real-valued bisection limit belongs to the starting interval. -/
theorem limit_mem_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : limit hab f ∈ Icc a b :=
  ((State.initial hab).limit ((Icc a b).domRestrict f)).property

/-- The canonical limit on a degenerate interval equals its sole endpoint. -/
@[simp]
theorem limit_self (a : ℝ) (f : ℝ → ℝ) : limit (a := a) (b := a) le_rfl f = a := by
  simpa [Icc_self, mem_singleton_iff] using
    limit_mem_Icc (a := a) (b := a) le_rfl f

/-- The real-valued bisection approximations converge to their canonical limit. -/
theorem tendsto_approximation_limit {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    Tendsto (approximation hab f) atTop (𝓝 (limit hab f)) := by
  change Tendsto (fun n =>
    (((State.initial hab).approximation ((Icc a b).domRestrict f) n : Icc a b) : ℝ))
      atTop
      (𝓝 (((State.initial hab).limit ((Icc a b).domRestrict f) : Icc a b) : ℝ))
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (State.tendsto_approximation_limit (State.initial hab) ((Icc a b).domRestrict f))

/-- The real-valued bisection approximations form a Cauchy sequence. -/
theorem cauchySeq_approximation {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    CauchySeq (approximation hab f) :=
  (tendsto_approximation_limit hab f).cauchySeq

/-- The `n`th real-valued approximation is within `(b - a) / 2 ^ (n + 1)` of the canonical
limit. -/
theorem dist_approximation_limit_le {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (n : ℕ) :
    dist (approximation hab f n) (limit hab f) ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  simpa [approximation, limit, State.width_initial, Subtype.dist_eq] using
    State.dist_approximation_limit_le
      (State.initial hab) ((Icc a b).domRestrict f) n

/-- If a real function with a nonpositive endpoint-value product is continuous within `[a, b]` at
the canonical bisection limit, then that limit is a root. -/
theorem apply_limit_eq_zero_of_continuousWithinAt {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousWithinAt f (Icc a b) (limit hab f))
    (hbracket : f a * f b ≤ 0) : f (limit hab f) = 0 := by
  let g := (Icc a b).domRestrict f
  let s := State.initial hab
  let y := s.limit g
  have h : s.Brackets g := by
    simpa [s, g, State.Brackets] using hbracket
  have hy_cont : ContinuousAt g y := by
    apply (continuousWithinAt_iff_continuousAt_domRestrict f y.property).mp
    simpa [limit, s, g, y] using hf
  simpa [limit, s, g, y] using
    h.apply_limit_eq_zero_of_continuousWithinAt hy_cont.continuousWithinAt

/-- For a continuous real function whose endpoint values have nonpositive product, the canonical
bisection limit is a root. -/
theorem apply_limit_eq_zero {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hbracket : f a * f b ≤ 0) : f (limit hab f) = 0 := by
  exact apply_limit_eq_zero_of_continuousWithinAt hab
    (hf (limit hab f) (limit_mem_Icc hab f)) hbracket

/-- After `n` bisection steps for a continuous real function on `[a, b]` whose endpoint values have
nonpositive product, the approximation is within `(b - a) / 2 ^ (n + 1)` of a root in `[a, b]`. -/
theorem exists_root_dist_approximation_le {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hbracket : f a * f b ≤ 0) (n : ℕ) :
    ∃ x ∈ Icc a b, f x = 0 ∧
      dist (approximation hab f n) x ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  exact ⟨limit hab f, limit_mem_Icc hab f, apply_limit_eq_zero hab hf hbracket,
    dist_approximation_limit_le hab f n⟩

/-- The bisection approximations for a continuous real function on `[a, b]` whose endpoint values
have nonpositive product converge to a root and satisfy the standard error bound. -/
theorem exists_root_tendsto_approximation {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hbracket : f a * f b ≤ 0) :
    ∃ x ∈ Icc a b, f x = 0 ∧ Tendsto (approximation hab f) atTop (𝓝 x) ∧
      ∀ n, dist (approximation hab f n) x ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  exact ⟨limit hab f, limit_mem_Icc hab f, apply_limit_eq_zero hab hf hbracket,
    tendsto_approximation_limit hab f, dist_approximation_limit_le hab f⟩

end Bisection
