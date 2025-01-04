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
is some `b` such that `L * max (tmax - t₀) (t₀ - tmin) ≤ b < a`, then for every
`x ∈ closedBall x₀ (a - b)`, there exists a (local) solution `α x` with the initial condition
`α t₀ = x`. In other words, there exists a local flow `α : E → ℝ → E` defined on
`closedBall x₀ (a - b)` and `Icc tmin tmax`.

The proof relies on demonstrating the existence of a solution `α` to the following integral
equation:
$$\alpha(t) = x_0 + \int_{t_0}^t f(\tau, \alpha(\tau))\,\mathrm{d}\tau.$$
This is done via the contraction mapping theorem, applied to the space of Lipschitz continuous
functions from a closed interval to a Banach space. The needed contraction map is constructed by
repeated applications of the right hand side of the the above equation.

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
  certain quantities constructed from them can be shown more easily. However, this leads to a
  potential confusion in the meaning of `a - b`. The (vacuous) validity of the existence theorem
  `IsPicardLindelof.exists_eq_hasDerivWithinAt` when `a < b` crucially relies on `(a - b) : ℝ`
  meaning `(a : ℝ) - (b : ℝ)`, which is negative. With this understanding, the condition `a < b`
  does not need to be stated as part of `IsPicardLindelof`.
* We only prove the existence of a solution in this file. For uniqueness, see `ODE_solution_unique`
  and related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation, dynamical system, initial value problem

-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology
#synth Sub ℝ≥0
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
    (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (hα : ∀ t ∈ Ioo tmin tmax, HasDerivAt α (f t (α t)) t)
    (hmem : MapsTo α (Ioo tmin tmax) u) :
    ContDiffOn ℝ n α (Ioo tmin tmax) := by
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
`IsPicardLindelof f t₀ x₀ a b L K` means that the time-dependent vector field `f` satisfies the
conditions to admit an integral curve `α : ℝ → E` to `f` defined on `Icc tmin tmax` with the
initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ a - b`. Note that the initial point `x` is allowed
to differ from the point `x₀` about which the conditions on `f` are stated. The theorem is only
meaningful when `b ≤ a` but is true vacuously otherwise. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a b L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz in with constant `K` within a closed ball. -/
  lipschitz : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ b

namespace IsPicardLindelof

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a b L K : ℝ≥0}

/-- The special case where the vector field is independent of time. -/
lemma mk_of_time_independent
    {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a b L K : ℝ≥0}
    (hb : ∀ x ∈ closedBall x₀ a, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a))
    (hm : L * max (tmax - t₀) (t₀ - tmin) ≤ b) :
    (IsPicardLindelof (fun _ ↦ f) t₀ x₀ a b L K) where
  lipschitz := fun _ _ ↦ hl
  continuousOn := fun _ _ ↦ continuousOn_const
  norm_le := fun _ _ ↦ hb
  mul_max_le := hm

-- statement seems a little funky
lemma mk_of_contDiffOn_one [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a b L K : ℝ≥0) (_ : b < a), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a b L K := by
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
  set ε := a / L / 2 / 2 with hε
  have hε0 : 0 < ε := half_pos <| half_pos <| div_pos ha hL0
  refine ⟨ε, hε0,
    ⟨a / 2, le_of_lt <| half_pos ha⟩, ⟨a / 2, le_of_lt <| half_pos ha⟩ / 2,
    ⟨L, le_of_lt hL0⟩, K, half_lt_self <| half_pos ha, ?_⟩
  apply mk_of_time_independent hb
  · apply hl.mono
    apply subset_trans _ hss
    exact closedBall_subset_ball <| half_lt_self ha -- repeat
  · rw [NNReal.coe_mk, add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_div,
      NNReal.coe_two, NNReal.coe_mk, mul_comm, ← le_div_iff₀ hL0, div_right_comm (a / 2),
      div_right_comm a]

-- generalise this to `a ≠ b` for flows
/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
lemma mk_of_contDiffOn_one' [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a L K : ℝ≥0), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a a L K := by
  obtain ⟨L, s, hs, hlip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨R₁, hR₁ : 0 < R₁, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨R₂, hR₂ : 0 < R₂, hbdd⟩ := Metric.continuousAt_iff.mp hf.continuousAt.norm 1 zero_lt_one
  have hbdd' : ∀ x ∈ Metric.ball x₀ R₂, ‖f x‖ ≤ 1 + ‖f x₀‖ := fun _ hx ↦
    sub_le_iff_le_add.mp <| le_of_lt <| lt_of_abs_lt <| Real.dist_eq _ _ ▸ hbdd hx
  set ε := min R₁ R₂ / 2 / (1 + ‖f x₀‖) with hε
  have hε0 : 0 < ε := hε ▸ div_pos (half_pos <| lt_min hR₁ hR₂)
    (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _))
  refine ⟨ε, hε0, ⟨min R₁ R₂ / 2, by positivity⟩, ⟨1 + ‖f x₀‖, by positivity⟩, L, ?_⟩
  apply mk_of_time_independent
  · intro x hx
    apply hbdd' x
    apply mem_of_mem_of_subset hx
    apply (closedBall_subset_ball <| half_lt_self <| lt_min hR₁ hR₂).trans
    apply (Metric.ball_subset_ball <| min_le_right _ _).trans
    exact subset_refl _
  · apply hlip.mono
    apply (closedBall_subset_ball <| half_lt_self <| lt_min hR₁ hR₂).trans
    apply (Metric.ball_subset_ball <| min_le_left _ _).trans
    exact hball
  · rw [add_sub_cancel_left, sub_sub_cancel, max_self, hε, mul_div_left_comm,
      NNReal.coe_mk _ (by positivity), NNReal.coe_mk _ (by positivity), div_self, mul_one]
    exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| norm_nonneg _


-- show that `IsPicardLindelof` implies the assumptions in `hasDerivWithinAt_integrate_Icc`,
-- particularly the continuity of `uncurry f`

lemma continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a b L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a)) :=
  continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn




-- anything else here?
-- special cases of `IsPicardLindelof` for `x = x₀` and `b = 0`?



end IsPicardLindelof

/-! ## Space of curves -/

/-- The space of `L`-Lipschitz functions `α : Icc tmin tmax → E` satisfying the initial condition
`α t₀ = x`.

This will be shown to be a complete metric space on which `integrate` is a contracting map, leading
to a fixed point that will serve as the solution to the ODE. The domain is a closed interval in
order to easily inherit the sup metric from continuous maps on compact spaces. We cannot use
functions `ℝ → E` with junk values outside the domain, as solutions will not be unique outside the
domain, and the contracting map will fail to have a fixed point. -/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x : E) (L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  initial : toFun t₀ = x
  lipschitz : LipschitzWith L toFun

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x : E} {L : ℝ≥0}

-- need `toFun_eq_coe`?

instance : CoeFun (FunSpace t₀ x L) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- The constant map -/
instance : Inhabited (FunSpace t₀ x L) :=
  ⟨fun _ ↦ x, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩

@[congr]
lemma congr {α β : FunSpace t₀ x L} (h : α = β) (t : Icc tmin tmax) : α t = β t := by congr

protected lemma continuous (α : FunSpace t₀ x L) : Continuous α := α.lipschitz.continuous

/-- The embedding of `FunSpace` into the space of continuous maps. -/
def toContinuousMap : FunSpace t₀ x L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace t₀ x L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x L ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap : range (fun α : FunSpace t₀ x L ↦ α.toContinuousMap) =
    { α : C(Icc tmin tmax, E) | α t₀ = x ∧ LipschitzWith L α } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x L) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_eq (continuous_eval_const _) continuous_const |>.inter
  exact isClosed_setOf_lipschitzWith L |>.preimage continuous_coeFun

end

/-! ### Contracting map on the space of curves -/

variable {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a b L K : ℝ≥0}

lemma comp_projIcc_mem_closedBall (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (α : FunSpace t₀ x L) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (α ∘ projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2)) t ∈ closedBall x₀ a := by
  rw [comp_apply, mem_closedBall, dist_eq_norm, projIcc_of_mem _ ht]
  calc
    ‖_‖ ≤ ‖_ - x‖ + ‖x - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ = ‖_ - α t₀‖ + ‖x - x₀‖ := by rw [α.initial]
    _ ≤ L * |t - t₀| + (a - b) := by
      apply add_le_add _ (mem_closedBall_iff_norm.mp hx)
      rw [← dist_eq_norm]
      exact α.lipschitz.dist_le_mul ⟨t, ht⟩ t₀
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) + (a - b) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ L.2
      exact abs_sub_le_max_sub ht.1 ht.2 _
    _ ≤ b + (a - b) := by
      apply add_le_add_right
      exact hf.mul_max_le
    _ = a := add_sub_cancel _ _

variable [NormedSpace ℝ E]

/-- The integrand in `next` is continuous. -/
lemma continuousOn_comp_projIcc (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (α : FunSpace t₀ x L) :
    ContinuousOn (fun τ ↦ f τ ((α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2)) τ)) (Icc tmin tmax) := by
  apply continuousOn_comp
  · exact continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn
  · exact α.continuous.comp continuous_projIcc |>.continuousOn -- abstract?
  · intro t ht
    exact comp_projIcc_mem_closedBall hf hx _ ht

/-- The map on `FunSpace` defined by `integrate`, some `n`-th interate of which will be a
contracting map -/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (α : FunSpace t₀ x L) : FunSpace t₀ x L where
  toFun t := integrate f t₀ x (α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2)) t
  initial := by simp only [ContinuousMap.toFun_eq_coe, comp_apply, integrate_apply,
      intervalIntegral.integral_same, add_zero]
  lipschitz := LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, integrate_apply, integrate_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left]
    · rw [Subtype.dist_eq, Real.dist_eq]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
      exact hf.norm_le _ ht _ <| comp_projIcc_mem_closedBall hf hx _ ht
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ <| uIcc_subset_Icc t₀.2 t₁.2
      exact continuousOn_comp_projIcc hf hx _
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ <| uIcc_subset_Icc t₀.2 t₂.2
      exact continuousOn_comp_projIcc hf hx _

@[simp]
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a b L K) (hx : x ∈ closedBall x₀ (a - b))
    (α : FunSpace t₀ x L) {t : Icc tmin tmax} :
    α.next hf hx t = integrate f t₀ x (α ∘ (projIcc _ _ (le_trans t₀.2.1 t₀.2.2))) t := rfl

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    -- instead of `t : Icc tmin tmax` to simplify usage
    (α β : FunSpace t₀ x L)
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
        exact comp_projIcc_mem_closedBall hf hx _ ht
      · rw [← projIcc_val (le_trans t₀.2.1 t₀.2.2) ⟨t, ht⟩]
        exact comp_projIcc_mem_closedBall hf hx _ ht
    _ ≤ K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ K.2
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two
curves -/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (α β : FunSpace t₀ x L) (n : ℕ) (t : Icc tmin tmax) :
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
        _ (fun _ ht' ↦ comp_projIcc_mem_closedBall hf hx _ ht')
      exact FunSpace.continuous _ |>.comp_continuousOn continuous_projIcc.continuousOn
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono _ (uIcc_subset_Icc t₀.2 t.2)
      apply continuousOn_comp
        (continuousOn_uncurry_of_lipschitzOnWith_continuousOn hf.lipschitz hf.continuousOn)
        _ (fun _ ht' ↦ comp_projIcc_mem_closedBall hf hx _ ht')
      exact FunSpace.continuous _ |>.comp_continuousOn continuous_projIcc.continuousOn

/-- The `n`-th iterate of `next` has Lipschitz with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
lemma dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) (α β : FunSpace t₀ x L) (n : ℕ) :
    dist ((next hf hx)^[n] α) ((next hf hx)^[n] β) ≤
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  have (α' β' : FunSpace t₀ x L) :
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
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! :=
    div_nonneg (pow_nonneg (mul_nonneg K.2 (le_max_iff.2 <| Or.inl <| sub_nonneg.2 t₀.2.2)) _)
      (Nat.cast_nonneg _)
  exact ⟨n, ⟨_, this⟩, hn, LipschitzWith.of_dist_le_mul fun α β ↦
    dist_iterate_next_le hf hx α β n⟩

-- consider flipping the equality
/-- The map `FunSpace.iterate` has a fixed point. This will be used to construct the solution
`α : ℝ → E` to the ODE. -/
lemma exists_funSpace_integrate_eq [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a b L K)
    (hx : x ∈ closedBall x₀ (a - b)) :
    ∃ α : FunSpace t₀ x L, next hf hx α = α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf hx
  ⟨_, h.isFixedPt_fixedPoint_iterate⟩

end FunSpace

/-! ## Existence of a solution to an ODE -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsPicardLindelof

variable  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a b L K : ℝ≥0}

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. This version shows the existence of a local solution
whose initial point `x` may be be different from the centre `x₀` of the closed ball within which the
properties of the vector field hold. This theorem is only meaningful when `b ≤ a`. -/
theorem exists_eq_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a b L K) (hx : x ∈ closedBall x₀ (a - b)) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  have ⟨α, hα⟩ := FunSpace.exists_funSpace_integrate_eq hf hx
  refine ⟨α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2),
    by rw [comp_apply, projIcc_val, α.initial], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_integrate_Icc t₀.2 hf.continuousOn_uncurry
    (α.continuous.comp continuous_projIcc |>.continuousOn) -- duplicate!
    (fun _ ht' ↦ FunSpace.comp_projIcc_mem_closedBall hf hx _ ht')
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  rw [comp_apply, projIcc_of_mem _ ht', ← FunSpace.congr hα ⟨t', ht'⟩, FunSpace.next_apply]

theorem exists_eq_hasDerivWithinAt₀
    (hf : IsPicardLindelof f t₀ x₀ a a L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  have hx : x₀ ∈ closedBall x₀ (a - a) := by simp
  have ⟨α, hα⟩ := FunSpace.exists_funSpace_integrate_eq hf hx
  refine ⟨α ∘ projIcc _ _ (le_trans t₀.2.1 t₀.2.2),
    by rw [comp_apply, projIcc_val, α.initial], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_integrate_Icc t₀.2 hf.continuousOn_uncurry
    (α.continuous.comp continuous_projIcc |>.continuousOn) -- duplicate!
    (fun _ ht' ↦ FunSpace.comp_projIcc_mem_closedBall hf hx _ ht')
    x₀ ht |>.congr_of_mem _ ht
  intro t' ht'
  rw [comp_apply, projIcc_of_mem _ ht', ← FunSpace.congr hα ⟨t', ht'⟩, FunSpace.next_apply]

open Classical in
/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. This version shows the existence of a local flow. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a b L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ (a - b), α x t₀ = x ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t := by
  have (x) (hx : x ∈ closedBall x₀ (a - b)) := exists_eq_hasDerivWithinAt hf hx
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ (a - b) then choose (this x hx) else 0 with hα
  refine ⟨α, fun x hx ↦ ?_⟩
  have ⟨h1, h2⟩ := choose_spec (this x hx)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

end IsPicardLindelof

/-! ### $C^1$ vector field -/

-- collect variables

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on a closed interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_eq_hasDerivWithinAt_Icc_of_contDiffAt {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  have ⟨ε, hε, a, b, _, _, hab, hpl⟩ := IsPicardLindelof.mk_of_contDiffOn_one hf t₀
  refine ⟨a - b, sub_pos_of_lt hab, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := hpl.exists_eq_hasDerivWithinAt hx
  exact ⟨α, hα1, hα2⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_eq_hasDerivAt_Ioo_of_contDiffAt {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have ⟨r, hr, ε, hε, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := H x hx
  refine ⟨α, hα1, fun _ ht ↦ hα2 _ (Ioo_subset_Icc_self ht) |>.mono Ioo_subset_Icc_self
    |>.hasDerivAt (Ioo_mem_nhds ht.1 ht.2)⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on a closed interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_hasDerivWithinAt_Icc_of_contDiffAt₀ {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc (t₀ - ε) (t₀ + ε)) t :=
  have ⟨_, hr, ε, hε, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  have ⟨α, hα⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨ε, hε, α, hα⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_hasDerivAt_Ioo_of_contDiffAt₀ {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  have ⟨_, hr, ε, hε, H⟩ := exists_eq_hasDerivAt_Ioo_of_contDiffAt hf t₀
  have ⟨α, hα⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨ε, hε, α, hα⟩

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on a closed domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_Icc {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt (α x) (f (α x t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  obtain ⟨r, hr, ε, hε, H⟩ := exists_eq_hasDerivWithinAt_Icc_of_contDiffAt hf t₀
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then choose (H x hx) else 0 with hα
  refine ⟨r, hr, ε, hε, α, fun x hx ↦ ?_⟩
  have ⟨h1, h2⟩ := choose_spec (H x hx)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_Ioo {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (α x) (f (α x t)) t := by
  obtain ⟨r, hr, ε, hε, H⟩ := exists_eq_hasDerivAt_Ioo_of_contDiffAt hf t₀
  set α := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then choose (H x hx) else 0 with hα
  refine ⟨r, hr, ε, hε, α, fun x hx ↦ ?_⟩
  have ⟨h1, h2⟩ := choose_spec (H x hx)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp_rw [hα, dif_pos hx, h1]
  · simp_rw [hα, dif_pos hx, h2 t ht]

end

end ODE
