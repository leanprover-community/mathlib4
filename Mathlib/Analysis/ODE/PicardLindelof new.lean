/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting

-- remember to fix copyright

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

We prove the (local) existence of integral curves and flows to time-dependent vector fields. We also
show that if the vector field is $C^n$, then the integral curve is also $C^n$.

Let `f : ℝ → E → E` be a time-dependent (local) vector field on a Banach space, and let `t₀ : ℝ`
and `x₀ : E`. If `f` is Lipschitz continuous in `x` within a closed ball around `x₀` of radius
`a ≥ 0` at every `t` and continuous in `t` at every `x`, then there exists a (local) solution
`α : ℝ → E` to the initial value problem `α t₀ = x₀` and `deriv α t = f t (α t)` for all
`t ∈ Icc tmin tmax`, where `t₀ - a / L ≤ tmin ≤ t₀ ≤ tmax ≤ t₀ + a / L`.

We actually prove a more general version of this theorem for the existence of local flows. If there
is some `r ≥ 0` such that `L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, then for every
`x ∈ closedBall x₀ r`, there exists a (local) solution `α x` with the initial condition `α t₀ = x`.
In other words, there exists a local flow `α : E → ℝ → E` defined on `closedBall x₀ r` and
`Icc tmin tmax`.

The proof relies on demonstrating the existence of a solution `α` to the following integral
equation:
$$\alpha(t) = x_0 + \int_{t_0}^t f(\tau, \alpha(\tau))\,\mathrm{d}\tau.$$
This is done via the contraction mapping theorem, applied to the space of Lipschitz continuous
functions from a closed interval to a Banach space. The needed contraction map is constructed by
repeated applications of the right hand side of the the above equation.

We then show that the local flow is Lipschitz continuous in the

## Main definitions and results

* `integrate f t₀ x₀ α t`: the right hand side of the integral equation, applied to the curve `α`.
* `contDiffOn_enat_Ioo_of_hasDerivAt`: if `f` is $C^n$ and `α` is continuous, then `α` is also
  $C^n`.
* `IsPicardLindelof`: the structure holding the assumptions of the Picard-Lindelöf theorem.
* `IsPicardLindelof.exists_eq_hasDerivWithinAt`: the existence theorem for local solutions to
  time-dependent ODEs.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_Icc`: the existence theorem for
  local flows to time-dependent vector fields.

## Implementation notes

* The structure `FunSpace` and theorems within this namespace are implementation details of the
  proof of the Picard-Lindelöf theorem and are not intended to be used outside of this file.
* Some sources, such as Lang, define `FunSpace` as the space of continuous functions from a closed
  interval to a closed ball. The Lipschitz condition used in `FunSpace` here is sufficient for
  proving the theorem, it has better properties when formalised, and it allows us to postpone the
  usage of the completeness condition on the space `E` until the application of the contraction
  mapping theorem.
* We have chosen to formalise many of the real constants as `ℝ≥0`, so that the non-negativity of
  certain quantities constructed from them can be shown more easily. When subtraction is involved,
  especially note whether it is the usual subtraction between two reals or the truncated subtraction
  between two non-negative reals.
* We only prove the existence of a solution in this file. For uniqueness, see `ODE_solution_unique`
  and related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation, dynamical system, initial value problem

-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

-- generalise
lemma abs_sub_le_max_sub {a b c : ℝ} (hac : a ≤ b) (hcd : b ≤ c) (d : ℝ) :
    |b - d| ≤ (c - d) ⊔ (d - a) := by
  rcases le_total d b with h | h
  · rw [abs_of_nonneg <| sub_nonneg_of_le h]
    exact le_max_of_le_left <| sub_le_sub_right hcd _
  · rw [abs_of_nonpos <| sub_nonpos_of_le h, neg_sub]
    exact le_max_of_le_right <| sub_le_sub_left hac _

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation and show that it
is equivalent to the initial value problem defined by `f`. The smoothness class of `f` is
transferred to solutions of the integral equation.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

/-- The main integral expression on which the Picard-Lindelöf theorem is built. It will be shown
that if `α : ℝ → E` and `integral f t₀ x₀ α` agree on an interval containing `t₀`, then `α` is a
solution to `f` with `α t₀ = x₀`. -/
noncomputable def integrate (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma integrate_apply {x₀ : E} {t : ℝ} :
    integrate f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

-- use `MapsTo`?
/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl -- abstract?
  rw [this]
  apply hf.comp <| contDiffOn_id.prod hα
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

/-- Special case of `contDiffOn_comp` when `n = 0`. -/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem

variable [CompleteSpace E]

/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `integrate f t₀ x₀ α`. -/
lemma hasDerivAt_integrate_of_isOpen
    (hs : IsOpen s)
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : uIcc t₀ t ⊆ s) :
    HasDerivAt (integrate f t₀ x₀ α) (f t (α t)) t := by
  apply HasDerivAt.const_add
  have ht' : t ∈ s := by -- missing lemmas `mem_Icc_right` etc?
    apply mem_of_mem_of_subset _ ht
    rw [mem_uIcc]
    simp only [le_refl, and_true, true_and]
    exact le_rfl.le_or_le _
  exact intervalIntegral.integral_hasDerivAt_right -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.mono ht |>.intervalIntegrable)
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter hs _ ht')
    (continuousOn_comp hf hα hmem _ ht' |>.continuousAt <| hs.mem_nhds ht')

-- also works for open sets and `Ici` and `Iic`; generalise?
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `integrate f t₀ x₀ α`. -/
lemma hasDerivWithinAt_integrate_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (integrate f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_comp hf hα hmem |>.mono
  by_cases h : t < t₀
  · rw [uIcc_of_gt h]
    exact Icc_subset_Icc ht.1 ht₀.2
  · rw [uIcc_of_le (not_lt.mp h)]
    exact Icc_subset_Icc ht₀.1 ht.2

/-- Converse of `hasDerivWithinAt_integrate_Icc`: if `f` is the derivative along `α`, then `α`
satisfies the integral equation. -/
lemma integrate_eq_of_hasDerivAt {t : ℝ}
    (hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u))
    (hα : ∀ t' ∈ uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t')
    (hmap : MapsTo α (uIcc t₀ t) u) : -- need `Icc` for `uIcc_subset_Icc`
    integrate f t₀ (α t₀) α t = α t :=
  calc
    _ = α t₀ + (α t - α t₀) := by
      rw [integrate_apply, integral_eq_sub_of_hasDeriv_right]
      · intro t' ht'
        exact hα t' ht' |>.continuousWithinAt
      · intro t' ht'
        apply HasDerivAt.hasDerivWithinAt
        exact hα t' (Ioo_subset_Icc_self ht') |>.hasDerivAt <| Icc_mem_nhds ht'.1 ht'.2
      · apply ContinuousOn.intervalIntegrable -- kind of repeated later
        apply continuousOn_comp hf _ hmap
        intro t' ht' -- repeat
        exact hα t' ht' |>.continuousWithinAt
    _ = α t := add_sub_cancel _ _

-- `n = ω`?
-- also works for `Ioi` and `Iio` but not intervals with a closed end due to non-unique diff there
/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`. -/
lemma contDiffOn_nat_integrate_Ioo
    (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = integrate f t₀ x₀ α t) :
    ContDiffOn ℝ n (integrate f t₀ x₀ α) (Ioo tmin tmax) := by
  have ht' {t} (ht : t ∈ Ioo tmin tmax) : uIcc t₀ t ⊆ Ioo tmin tmax := by -- missing lemma?
    rw [uIcc_eq_union]
    exact union_subset (Icc_subset_Ioo ht₀.1 ht.2) (Icc_subset_Ioo ht.1 ht₀.2)
  have {t} (ht : t ∈ Ioo tmin tmax) :=
    hasDerivAt_integrate_of_isOpen isOpen_Ioo hf.continuousOn hα hmem x₀ (ht' ht)
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, contDiffOn_zero] at *
    exact fun _ ht ↦ this ht |>.continuousAt.continuousWithinAt
  | succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] -- check this for generalisation to `ω`
    refine ⟨fun _ ht ↦ HasDerivAt.differentiableAt (this ht) |>.differentiableWithinAt, by simp, ?_⟩
    have hα' : ContDiffOn ℝ n α (Ioo tmin tmax) := ContDiffOn.congr (hn hf.of_succ) heqon
    exact contDiffOn_comp hf.of_succ hα' hmem |>.congr fun _ ht ↦ HasDerivAt.deriv (this ht)

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$.This version works for `n : ℕ∞`. -/
lemma contDiffOn_enat_integrate_Ioo
    (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = integrate f t₀ x₀ α t) :
    ContDiffOn ℝ n (integrate f t₀ x₀ α) (Ioo tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    intro k
    exact contDiffOn_nat_integrate_Ioo ht₀ (hf k) hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_integrate_Ioo ht₀ hf hα hmem x₀ heqon

/-- Solutions to ODEs defined by $C^n$ vector fields are also $C^n$. -/
theorem contDiffOn_enat_Ioo_of_hasDerivAt
    {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (hα : ∀ t ∈ Ioo tmin tmax, HasDerivAt α (f t (α t)) t)
    (hmem : MapsTo α (Ioo tmin tmax) u) :
    ContDiffOn ℝ n α (Ioo tmin tmax) := by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ ∈ Ioo tmin tmax := ⟨by linarith, by linarith⟩
    have : ∀ t ∈ Ioo tmin tmax, α t = integrate f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t ⊆ Ioo tmin tmax := by
        rw [uIcc_eq_union]
        exact union_subset (Icc_subset_Ioo ht₀.1 ht.2) (Icc_subset_Ioo ht.1 ht₀.2)
      rw [integrate_eq_of_hasDerivAt (hf.continuousOn.mono _)]
      · intro t' ht'
        apply hα t' (this ht') |>.hasDerivWithinAt
      · apply hmem.mono_left this
      · -- missing `left/right` lemmas for `prod_subset_prod_iff`
        rw [prod_subset_prod_iff]
        apply Or.inl ⟨this, subset_rfl⟩
    exact contDiffOn_enat_integrate_Ioo ht₀ hf
      (fun t ht ↦ hα t ht |>.continuousAt.continuousWithinAt) hmem (α t₀) this |>.congr this
  · rw [Ioo_eq_empty hlt, ContDiffOn, forall_mem_empty]
    simp

end

-- move?
lemma continuousOn_uncurry_of_lipschitzOnWith_continuousOn
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {s : Set ℝ} {u : Set E}
    {K : ℝ≥0} (hlip : ∀ t ∈ s, LipschitzOnWith K (f t) u)
    (hcont : ∀ x ∈ u, ContinuousOn (f · x) s) :
    ContinuousOn (uncurry f) (s ×ˢ u) :=
  have : ContinuousOn (uncurry (flip f)) (u ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hcont hlip
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset

/-- Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K` means that the time-dependent vector field `f` satisfies the
conditions to admit an integral curve `α : ℝ → E` to `f` defined on `Icc tmin tmax` with the
initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Note that the initial point `x` is allowed
to differ from the point `x₀` about which the conditions on `f` are stated. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz in with constant `K` within a closed ball. -/
  lipschitz : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

namespace IsPicardLindelof

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- The special case where the vector field is independent of time. -/
lemma mk_of_time_independent
    {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hb : ∀ x ∈ closedBall x₀ a, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a))
    (hm : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    (IsPicardLindelof (fun _ ↦ f) t₀ x₀ a r L K) where
  lipschitz := fun _ _ ↦ hl
  continuousOn := fun _ _ ↦ continuousOn_const
  norm_le := fun _ _ ↦ hb
  mul_max_le := hm

-- add comments to explain the choice of constants
-- statement seems a little funky
lemma mk_of_contDiffAt_one [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
  -- obtain ball of radius `a` within area in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, hss⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by
    apply add_pos_of_nonneg_of_pos _ zero_lt_one
    apply add_nonneg _ (norm_nonneg _)
    exact mul_nonneg K.2 (le_of_lt ha)
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ = ‖f x - 0‖ := by simp
      _ ≤ ‖f x - f x₀‖ + ‖f x₀ - 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        rw [sub_zero]
        apply add_le_add_right
        rw [← dist_eq_norm, ← dist_eq_norm]
        apply hl.dist_le_mul x _ x₀ (mem_of_mem_nhds hs)
        apply subset_trans _ hss hx
        exact closedBall_subset_ball <| half_lt_self ha -- this is where we need `a / 2`
      _ ≤ K * a + ‖f x₀‖ := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ K.2
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := half_pos <| half_pos <| div_pos ha hL0
  refine ⟨ε, hε0,
    ⟨a / 2, le_of_lt <| half_pos ha⟩, ⟨a / 2, le_of_lt <| half_pos ha⟩ / 2,
    ⟨L, le_of_lt hL0⟩, K, half_pos <| half_pos ha, ?_⟩
  apply mk_of_time_independent hb
  · apply hl.mono
    apply subset_trans _ hss
    exact closedBall_subset_ball <| half_lt_self ha -- repeat
  · rw [NNReal.coe_mk, add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_div,
      NNReal.coe_two, NNReal.coe_mk, mul_comm, ← le_div_iff₀ hL0, sub_half, div_right_comm (a / 2),
      div_right_comm a]

/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
lemma mk_of_contDiffAt_one₀ [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a L K : ℝ≥0), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a 0 L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := mk_of_contDiffAt_one hf t₀
  refine ⟨ε, hε, a, L, K, ?_⟩
  refine ⟨hpl.lipschitz, hpl.continuousOn, hpl.norm_le, ?_⟩
  apply le_trans hpl.mul_max_le
  apply sub_le_sub_left
  rw [NNReal.coe_le_coe]
  exact le_of_lt hr

-- show that `IsPicardLindelof` implies the assumptions in `hasDerivWithinAt_integrate_Icc`,
-- particularly the continuity of `uncurry f`

lemma continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a)) :=
  continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn




-- anything else here?
-- special cases of `IsPicardLindelof` for `x = x₀` and `b = 0`?



end IsPicardLindelof

/-! ## Space of Lipschitz functions on a closed interval -/

/-
Plan for Corollary 1.2:
* We need a complete space of functions whose type does not refer to the initial point, so that we
  can state the distance between two functions with different initial conditions.
* Move the dependence on intial point `x` to the definition of `next`.
* Show that `next .. x` is a contraction map on the space of Lipschitz functions (without any
  initial condition), and that the fixed point is a solution with initial point `x`.
* `next .. x` applied to a Lipschitz function (with any initial point `x'`) repeatedly will
  converge to the fixed point, which has initial point `x`.

-/

/-- The space of `L`-Lipschitz functions `α : Icc tmin tmax → E`.

This will be shown to be a complete metric space on which `integrate` is a contracting map, leading
to a fixed point that will serve as the solution to the ODE. The domain is a closed interval in
order to easily inherit the sup metric from continuous maps on compact spaces. We cannot use
functions `ℝ → E` with junk values outside the domain, as solutions will not be unique outside the
domain, and the contracting map will thus fail to have a fixed point. -/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (r L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  lipschitz : LipschitzWith L toFun
  mem_closedBall₀ : toFun t₀ ∈ closedBall x₀ r

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {r L : ℝ≥0}

-- need `toFun_eq_coe`?

instance : CoeFun (FunSpace t₀ x₀ r L) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- The constant map -/
instance : Inhabited (FunSpace t₀ x₀ r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken (zero_le _), mem_closedBall_self r.2⟩

@[congr]
lemma congr {α β : FunSpace t₀ x₀ L r} (h : α = β) (t : Icc tmin tmax) : α t = β t := by congr

@[ext]
lemma ext {α β : FunSpace t₀ x₀ L r} (h : ∀ t, α t = β t) : α = β := by
  cases α
  cases β
  congr
  ext t
  exact h t

protected lemma continuous (α : FunSpace t₀ x₀ L r) : Continuous α := α.lipschitz.continuous

/-- The embedding of `FunSpace` into the space of continuous maps. -/
def toContinuousMap : FunSpace t₀ x₀ r L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

@[simp]
lemma toContinuousMap_apply_eq_apply (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    α.toContinuousMap t = α t := rfl

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace t₀ x₀ r L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x₀ r L ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap : range (fun α : FunSpace t₀ x₀ r L ↦ α.toContinuousMap) =
    { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α t₀ ∈ closedBall x₀ r } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x₀ r L) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_setOf_lipschitzWith L |>.preimage continuous_coeFun |>.inter
  simp_rw [mem_closedBall_iff_norm]
  apply isClosed_le _ continuous_const
  apply continuous_norm.comp
  apply continuous_sub_right _ |>.comp
  exact continuous_eval_const _

end

/-! ### Contracting map on the space of curves -/

variable {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x y : E} {a r L K : ℝ≥0}

lemma comp_projIcc_mem_closedBall (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (α : FunSpace t₀ x₀ r L) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (α ∘ projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2)) t ∈ closedBall x₀ a := by
  rw [comp_apply, mem_closedBall, dist_eq_norm, projIcc_of_mem _ ht]
  calc
    ‖_‖ ≤ ‖_ - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ L * |t - t₀| + r := by
      apply add_le_add _ (mem_closedBall_iff_norm.mp α.mem_closedBall₀)
      rw [← dist_eq_norm]
      exact α.lipschitz.dist_le_mul ⟨t, ht⟩ t₀
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) + r := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ L.2
      exact abs_sub_le_max_sub ht.1 ht.2 _
    _ ≤ a - r + r := by
      apply add_le_add_right
      exact hf.mul_max_le
    _ = a := sub_add_cancel _ _

variable [NormedSpace ℝ E]

/-- The integrand in `next` is continuous. -/
lemma continuousOn_comp_projIcc (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) :
    ContinuousOn (fun τ ↦ f τ ((α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2)) τ)) (Icc tmin tmax) := by
  apply continuousOn_comp
  · exact continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn
  · exact α.continuous.comp continuous_projIcc |>.continuousOn -- abstract?
  · intro t ht
    exact comp_projIcc_mem_closedBall hf _ ht

/-- The map on `FunSpace` defined by `integrate`, some `n`-th interate of which will be a
contracting map -/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := integrate f t₀ x (α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2)) t
  lipschitz := LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, integrate_apply, integrate_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left]
    · rw [Subtype.dist_eq, Real.dist_eq]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
      exact hf.norm_le _ ht _ <| comp_projIcc_mem_closedBall hf _ ht
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ <| uIcc_subset_Icc t₀.2 t₁.2
      exact continuousOn_comp_projIcc hf _
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ <| uIcc_subset_Icc t₀.2 t₂.2
      exact continuousOn_comp_projIcc hf _
  mem_closedBall₀ := by simp [hx]

@[simp]
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} :
    next hf hx α t = integrate f t₀ x (α ∘ (projIcc _ _ (le_trans t₀.2.1 t₀.2.2))) t := rfl

lemma next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x := by simp

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    -- instead of `t : Icc tmin tmax` to simplify usage
    (α β : FunSpace t₀ x₀ r L)
    (h : dist ((next hf hx)^[n] α ⟨t, ht⟩) ((next hf hx)^[n] β ⟨t, ht⟩) ≤
      (K * |t - t₀.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf hx)^[n] α ⟨t, ht⟩)) (f t ((next hf hx)^[n] β ⟨t, ht⟩)) ≤
      K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist ((next hf hx)^[n] α ⟨t, ht⟩)
        ((next hf hx)^[n] β ⟨t, ht⟩) := by
      apply hf.lipschitz t ht |>.dist_le_mul
      · -- missing lemma here?
        rw [← projIcc_val (le_trans t₀.2.1 t₀.2.2) ⟨t, ht⟩]
        exact comp_projIcc_mem_closedBall hf _ ht
      · rw [← projIcc_val (le_trans t₀.2.1 t₀.2.2) ⟨t, ht⟩]
        exact comp_projIcc_mem_closedBall hf _ ht
    _ ≤ K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ K.2
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two
curves -/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, integrate_apply, integrate_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub]
    · calc
        _ ≤ ∫ τ in Ι t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
          rw [intervalIntegral.norm_intervalIntegral_eq] -- need because it's ∫ - ∫
          apply norm_integral_le_of_norm_le <| Continuous.integrableOn_uIoc (by fun_prop)
          apply ae_restrict_mem measurableSet_Ioc |>.mono
          intro t' ht'
          -- duplicated
          have ht' : t' ∈ Icc tmin tmax :=
            subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₀.2 t.2) ht'
          rw [← dist_eq_norm, comp_apply, comp_apply, projIcc_of_mem _ ht']
          exact dist_comp_iterate_next_le hf hx _ ht' _ _ (hn _)
        _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
          apply le_of_abs_le
          -- critical: `integral_pow_abs_sub_uIoc`
          rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
            abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
            abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
            ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]
    · -- so much duplication
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ (uIcc_subset_Icc t₀.2 t.2)
      apply continuousOn_comp
        (continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn)
        _ (fun _ ht' ↦ comp_projIcc_mem_closedBall hf _ ht')
      exact FunSpace.continuous _ |>.comp_continuousOn continuous_projIcc.continuousOn
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ (uIcc_subset_Icc t₀.2 t.2)
      apply continuousOn_comp
        (continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn)
        _ (fun _ ht' ↦ comp_projIcc_mem_closedBall hf _ ht')
      exact FunSpace.continuous _ |>.comp_continuousOn continuous_projIcc.continuousOn

/-- The `n`-th iterate of `next` has Lipschitz with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist ((next hf hx)^[n] α) ((next hf hx)^[n] β) ≤
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  have (α' β' : FunSpace t₀ x₀ r L) :
    dist α' β' = dist α'.toContinuousMap β'.toContinuousMap := by rfl -- how to remove this?
  rw [this, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le hf hx α β n t
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ <| mul_nonneg K.2 (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (abs_sub_le_max_sub t.2.1 t.2.2 _) K.2
  · apply mul_nonneg _ dist_nonneg
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply pow_nonneg
    apply mul_nonneg K.2
    apply le_max_of_le_left
    exact sub_nonneg_of_le t₀.2.2

/-- Some `n`-th iterate of `next` is a contracting map. -/
lemma exists_contractingWith_iterate_next' (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! :=
    div_nonneg (pow_nonneg (mul_nonneg K.2 (le_max_iff.2 <| Or.inl <| sub_nonneg.2 t₀.2.2)) _)
      (Nat.cast_nonneg _)
  exact ⟨n, ⟨_, this⟩, hn, LipschitzWith.of_dist_le_mul fun α β ↦
    dist_iterate_next_iterate_next_le hf hx α β n⟩

/-- Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz constant is
independent of the initial point. -/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ∀ (x : E) (hx : x ∈ closedBall x₀ r),
      ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! :=
    div_nonneg (pow_nonneg (mul_nonneg K.2 (le_max_iff.2 <| Or.inl <| sub_nonneg.2 t₀.2.2)) _)
      (Nat.cast_nonneg _)
  refine ⟨n, ⟨_, this⟩, fun x hx ↦ ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β ↦ dist_iterate_next_iterate_next_le hf hx α β n⟩

-- consider flipping the equality
/-- The map `FunSpace.iterate` has a fixed point. This will be used to construct the solution
`α : ℝ → E` to the ODE. -/
lemma exists_funSpace_next_eq [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : FunSpace t₀ x₀ r L, next hf hx α = α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
  ⟨_, h x hx |>.isFixedPt_fixedPoint_iterate⟩

/-! ### Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^n α`.
-/

@[simp]
lemma dist_next_next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (hy : y ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) :
    dist (next hf hx α) (next hf hy α) = dist x y := by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
  have (α' β' : FunSpace t₀ x₀ r L) :
    dist α' β' = dist α'.toContinuousMap β'.toContinuousMap := by rfl -- repeated
  rw [this, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm]
  simp_rw [ContinuousMap.sub_apply, toContinuousMap_apply_eq_apply, next_apply, integrate_apply,
    add_sub_add_right_eq_sub]
  rw [ciSup_const, dist_eq_norm]

lemma dist_next_le_of_isFixedPt (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    {α : FunSpace t₀ x₀ r L} (hα : IsFixedPt (next hf α.mem_closedBall₀) α) :
    dist α (next hf hx α) = dist (α t₀) x := by
  nth_rw 1 [← hα]
  rw [dist_next_next]

lemma dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist α ((next hf hx)^[n] α) ≤
      (∑ i ∈ Finset.range n, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !)
        * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (f := next hf hx) (x := α)]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le hf hx _ _ i

lemma dist_iterate_iterate_next_le_of_lipschitzWith (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {m : ℕ} {C : ℝ≥0}
    (hm : LipschitzWith C (next hf hx)^[m]) (n : ℕ) :
    dist α ((next hf hx)^[m]^[n] α) ≤
      (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) *
        (∑ i ∈ Finset.range n, (C : ℝ) ^ i) * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (f := (next hf hx)^[m]) (x := α)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next hf hx)^[m]^[i] α) n
  intro i hi
  rw [iterate_succ_apply]
  apply le_trans <| hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc, mul_comm ((C : ℝ) ^ i), ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg C.2 _)
  exact dist_iterate_next_le hf hx α m

-- bug in the unused variable linter?
/-- The pointwise distance between any two integral curves `α` and `β` over their domains is bounded
by a constant `L'` times the distance between their respective initial points. -/
lemma exists_forall_closedBall_funSpace_dist_le_mul [CompleteSpace E]
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ L' : ℝ≥0, ∀ (x y : E) (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r)
      (α β : FunSpace t₀ x₀ r L) (hα : IsFixedPt (next hf hx) α) (hβ : IsFixedPt (next hf hy) β),
      dist α β ≤ L' * dist x y := by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 ≤ L' := by
    apply mul_nonneg _ (NNReal.coe_nonneg _)
    apply Finset.sum_nonneg'
    intro
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply pow_nonneg
    apply mul_nonneg K.2
    apply le_max_of_le_left
    exact sub_nonneg_of_le t₀.2.2
  refine ⟨⟨L', hL'⟩, fun x y hx hy α β hα hβ ↦ ?_⟩
  rw [NNReal.coe_mk]
  apply le_of_tendsto_of_tendsto' (b := Filter.atTop)
    (f := fun n ↦ dist α ((next hf hy)^[m]^[n] α))
    (g := fun n ↦ (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) *
      (∑ i ∈ Finset.range n, (C : ℝ) ^ i) * dist α (next hf hy α)) _ _
    (dist_iterate_iterate_next_le_of_lipschitzWith hf hy α (h y hy).2)
  · change Filter.Tendsto ((dist α ·) ∘ fun n ↦ (next hf hy)^[m]^[n] α) Filter.atTop (𝓝 (dist α β))
    apply Filter.Tendsto.comp (y := 𝓝 β) (tendsto_const_nhds.dist Filter.tendsto_id)
    convert h y hy |>.tendsto_iterate_fixedPoint α
    exact h y hy |>.fixedPoint_unique (hβ.iterate m)
  · nth_rw 1 [← hα, dist_next_next]
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.const_mul
    convert hasSum_geometric_of_lt_one C.2 (h y hy).1 |>.tendsto_sum_nat
    -- consider changing definition of `L'` to move this part to the proof of `hL'`
    rw [NNReal.coe_inv]
    congr
    rw [NNReal.coe_sub <| le_of_lt (h y hy).1, NNReal.coe_one, NNReal.val_eq_coe]

end FunSpace

/-! ## Existence of a solution to an ODE -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsPicardLindelof

variable  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem, integral form. This version shows the existence of a
local solution whose initial point `x` may be be different from the centre `x₀` of the closed ball
within which the properties of the vector field hold. -/
theorem exists_eq_integrate_eq
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t = integrate f t₀ x α t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_funSpace_next_eq hf hx
  refine ⟨(FunSpace.next hf hx α) ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2), by simp, fun t ht ↦ ?_⟩
  rw [comp_apply, FunSpace.next_apply, hα, projIcc_of_mem _ ht]

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem, differential form. This version shows the existence
of a local solution whose initial point `x` may be be different from the centre `x₀` of the closed
ball within which the properties of the vector field hold. -/
theorem exists_eq_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_funSpace_next_eq hf hx
  refine ⟨α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2),
    by rw [comp_apply, projIcc_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_integrate_Icc t₀.2 hf.continuousOn_uncurry
    (α.continuous.comp continuous_projIcc |>.continuousOn) -- duplicate!
    (fun _ ht' ↦ FunSpace.comp_projIcc_mem_closedBall hf _ ht')
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [comp_apply, FunSpace.next_apply, projIcc_of_mem _ ht']

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem, differential form. -/
theorem exists_eq_hasDerivWithinAt₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  exists_eq_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

open Classical in
/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem, differential form. This version shows the existence
of a local flow. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t := by
  have (x) (hx : x ∈ closedBall x₀ r) := exists_eq_hasDerivWithinAt hf hx
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then choose (this x hx) else 0 with hα
  refine ⟨α, fun x hx ↦ ?_⟩
  have ⟨h1, h2⟩ := choose_spec (this x hx)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

-- get previous from this to avoid repeating proofs?
-- need to get `α` directly from `FunSpace` because we do not have global uniqueness of solution yet
open Classical in
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_funSpace_next_eq hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2) else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    dsimp only
    rw [dif_pos hx, comp_apply, projIcc_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    dsimp only
    rw [dif_pos hx, comp_apply]
    apply hasDerivWithinAt_integrate_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous.comp continuous_projIcc |>.continuousOn) -- duplicate!
      (fun _ ht' ↦ FunSpace.comp_projIcc_mem_closedBall hf _ ht')
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [comp_apply, FunSpace.next_apply, projIcc_of_mem _ ht']
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    rw [hα']
    dsimp only
    rw [dif_pos hx, dif_pos hy, comp_apply, comp_apply, projIcc_of_mem _ ht,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

-- `uncurry α` is continuous

end IsPicardLindelof

/-! ### $C^1$ vector field -/

section

variable {f : E → E} {x₀ : E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on a closed interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_eq_hasDerivWithinAt_Icc_of_contDiffAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.mk_of_contDiffAt_one hf t₀
  refine ⟨r, hr, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := hpl.exists_eq_hasDerivWithinAt hx
  exact ⟨α, hα1, ε, hε, hα2⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_eq_hasDerivAt_Ioo_of_contDiffAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have ⟨r, hr, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  refine ⟨r, hr, fun x hx ↦ ?_⟩
  have ⟨α, hα1, ε, hε, hα2⟩ := H x hx
  refine ⟨α, hα1, ε, hε, fun _ ht ↦ hα2 _ (Ioo_subset_Icc_self ht) |>.mono Ioo_subset_Icc_self
    |>.hasDerivAt (Ioo_mem_nhds ht.1 ht.2)⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on a closed interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_hasDerivWithinAt_Icc_of_contDiffAt₀
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc (t₀ - ε) (t₀ + ε)) t :=
  have ⟨_, hr, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  H x₀ (mem_closedBall_self (le_of_lt hr))

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_hasDerivAt_Ioo_of_contDiffAt₀
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  have ⟨_, hr, H⟩ := exists_eq_hasDerivAt_Ioo_of_contDiffAt hf t₀
  H x₀ (mem_closedBall_self (le_of_lt hr))

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on a closed domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_Icc
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt (α x) (f (α x t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  obtain ⟨r, hr, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then choose (H x hx) else 0 with hα
  refine ⟨r, hr, α, fun x hx ↦ ?_⟩
  have ⟨h1, ε, hε, h2⟩ := choose_spec (H x hx)
  refine ⟨?_, ε, hε, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_forall_mem_closedBall_eq_hasDerivAt_Ioo
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (α x) (f (α x t)) t := by
  obtain ⟨r, hr, H⟩ := exists_eq_hasDerivAt_Ioo_of_contDiffAt hf t₀
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then choose (H x hx) else 0 with hα
  refine ⟨r, hr, α, fun x hx ↦ ?_⟩
  have ⟨h1, ε, hε, h2⟩ := choose_spec (H x hx)
  refine ⟨?_, ε, hε, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

end

/-! ### $C^n$ vector field -/

section

variable {f : E → E} {x₀ : E} {n : ℕ∞}

-- get previous from this to avoid repeating proofs?
theorem exists_eq_hasDerivAt_Ioo_contDiffOn_of_contDiffAt
    (hf : ContDiffAt ℝ n f x₀) (hn : 1 ≤ n) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∃ ε > (0 : ℝ), (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t) ∧
      ContDiffOn ℝ n α (Ioo (t₀ - ε) (t₀ + ε)) := by
  -- need to extract a neighbourhood in which `f` is `ContDiffOn`
  -- shrink `a`, `ε` in `IsPicardLindelof`
  -- use `prodMap` composed with `snd` for `uncurry`
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.mk_of_contDiffAt_one
    (hf.of_le <| WithTop.coe_le_coe.mpr hn) t₀
  refine ⟨r, hr, fun x hx ↦ ?_⟩
  obtain ⟨α, hα⟩ := FunSpace.exists_funSpace_next_eq hpl hx
  refine ⟨α ∘ projIcc _ _ (by linarith), ?_, ε, hε, fun t ht ↦ ?_, ?_⟩
  · rw [← hα, comp_apply, projIcc_of_mem _ ⟨by linarith, by linarith⟩, FunSpace.next_apply₀]
  · have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
    apply hasDerivWithinAt_integrate_Icc ht₀ hpl.continuousOn_uncurry
      (α.continuous.comp continuous_projIcc |>.continuousOn) -- duplicate!
      (fun _ ht' ↦ FunSpace.comp_projIcc_mem_closedBall hpl _ ht')
      x (Ioo_subset_Icc_self ht) |>.congr_of_mem _ (Ioo_subset_Icc_self ht) |>.mono
      Ioo_subset_Icc_self |>.hasDerivAt (Ioo_mem_nhds ht.1 ht.2)
    intro t' ht'
    nth_rw 1 [← hα]
    rw [comp_apply, FunSpace.next_apply, projIcc_of_mem _ ht']
  · apply contDiffOn_enat_Ioo_of_hasDerivAt (f := fun t ↦ f) (u := closedBall x₀ a)
    · -- time independent to time dependent; abstract?
      sorry
    · sorry
    · sorry

end

end ODE
