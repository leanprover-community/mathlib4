/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

We prove the (local) existence of integral curves and flows to time-dependent vector fields.

Let `f : ℝ → E → E` be a time-dependent (local) vector field on a Banach space, and let `t₀ : ℝ`
and `x₀ : E`. If `f` is Lipschitz continuous in `x` within a closed ball around `x₀` of radius
`a ≥ 0` at every `t` and continuous in `t` at every `x`, then there exists a (local) solution
`α : ℝ → E` to the initial value problem `α t₀ = x₀` and `deriv α t = f t (α t)` for all
`t ∈ Icc tmin tmax`, where `L * max (tmax - t₀) (t₀ - tmin) ≤ a`.

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
repeated applications of the right-hand side of this equation.

## Main definitions and results

* `picard f t₀ x₀ α t`: the Picard iteration, applied to the curve `α`
* `IsPicardLindelof`: the structure holding the assumptions of the Picard-Lindelöf theorem
* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`: the existence theorem for local
  solutions to time-dependent ODEs
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`: the existence
  theorem for local flows to time-dependent vector fields
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`: there exists
  a local flow to time-dependent vector fields, and it is Lipschitz-continuous with respect to the
  starting point.

## Implementation notes

* The structure `FunSpace` and theorems within this namespace are implementation details of the
  proof of the Picard-Lindelöf theorem and are not intended to be used outside of this file.
* Some sources, such as Lang, define `FunSpace` as the space of continuous functions from a closed
  interval to a closed ball. We instead define `FunSpace` here as the space of Lipschitz continuous
  functions from a closed interval. This slightly stronger condition allows us to postpone the usage
  of the completeness condition on the space `E` until the application of the contraction mapping
  theorem.
* We have chosen to formalise many of the real constants as `ℝ≥0`, so that the non-negativity of
  certain quantities constructed from them can be shown more easily. When subtraction is involved,
  especially note whether it is the usual subtraction between two reals or the truncated subtraction
  between two non-negative reals.
* In this file, We only prove the existence of a solution. For uniqueness, see `ODE_solution_unique`
  and related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation, dynamical system, initial value problem, Picard-Lindelöf theorem,
Cauchy-Lipschitz theorem

-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Assumptions of the Picard-Lindelöf theorem-/

/-- Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K`, where `t₀ ∈ Icc tmin tmax`, means that the time-dependent vector
field `f` satisfies the conditions to admit an integral curve `α : ℝ → E` to `f` defined on
`Icc tmin tmax` with the initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Note that the initial
point `x` is allowed to differ from the point `x₀` about which the conditions on `f` are stated. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation that is
equivalent to the initial value problem defined by `f`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

/-- The Picard iteration. It will be shown that if `α : ℝ → E` and `picard f t₀ x₀ α` agree on an
interval containing `t₀`, then `α` is a solution to `f` with `α t₀ = x₀` on this interval. -/
noncomputable def picard (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma picard_apply {x₀ : E} {t : ℝ} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

lemma picard_apply₀ {x₀ : E} : picard f t₀ x₀ α t₀ = x₀ := by simp

/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl
  rw [this]
  apply hf.comp (by fun_prop)
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

/-- Given a continuous time-dependent vector field `f` and a continuous curve `α`, the composition
`f t (α t)` is continuous in `t`. -/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

end

/-! ## Space of Lipschitz functions on a closed interval

We define the space of Lipschitz continuous functions from a closed interval. This will be shown to
be a complete metric space on which `picard` is a contracting map, leading to a fixed point that
will serve as the solution to the ODE. The domain is a closed interval in order to easily inherit
the sup metric from continuous maps on compact spaces. We cannot use functions `ℝ → E` with junk
values outside the domain, as the supremum within a closed interval will only be a pseudo-metric,
and the contracting map will fail to have a fixed point. In order to accommodate flows, we do not
require a specific initial condition. Rather, `FunSpace` contains curves whose initial condition is
within a closed ball.
-/

/-- The space of `L`-Lipschitz functions `α : Icc tmin tmax → E` -/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (r L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  lipschitzWith : LipschitzWith L toFun
  mem_closedBall₀ : toFun t₀ ∈ closedBall x₀ r

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L : ℝ≥0}

instance : CoeFun (FunSpace t₀ x₀ r L) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- `FunSpace t₀ x₀ r L` contains the constant map at `x₀`. -/
instance : Inhabited (FunSpace t₀ x₀ r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken (zero_le _), mem_closedBall_self r.2⟩

protected lemma continuous (α : FunSpace t₀ x₀ L r) : Continuous α := α.lipschitzWith.continuous

/-- The embedding of `FunSpace` into the space of continuous maps -/
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

lemma range_toContinuousMap :
    range (fun α : FunSpace t₀ x₀ r L ↦ α.toContinuousMap) =
      { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α t₀ ∈ closedBall x₀ r } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x₀ r L) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_setOf_lipschitzWith L |>.preimage continuous_coeFun |>.inter
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) continuous_const

/-- Extend the domain of `α` from `Icc tmin tmax` to `ℝ` such that `α t = α tmin` for all `t ≤ tmin`
and `α t = α tmax` for all `t ≥ tmax`. -/
noncomputable def compProj (α : FunSpace t₀ x₀ r L) (t : ℝ) : E :=
  α <| projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t

@[simp]
lemma compProj_apply {α : FunSpace t₀ x₀ r L} {t : ℝ} :
    α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t) := rfl

lemma compProj_val {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax} :
    α.compProj t = α t := by simp only [compProj_apply, projIcc_val]

lemma compProj_of_mem {α : FunSpace t₀ x₀ r L} {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.compProj t = α ⟨t, ht⟩ := by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]
lemma continuous_compProj (α : FunSpace t₀ x₀ r L) : Continuous α.compProj :=
  α.continuous.comp continuous_projIcc

/-- The image of a function in `FunSpace` is contained within a closed ball. -/
protected lemma mem_closedBall
    {α : FunSpace t₀ x₀ r L} (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) {t : Icc tmin tmax} :
    α t ∈ closedBall x₀ a := by
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖α t - x₀‖ ≤ ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ L * |t.1 - t₀.1| + r := by
      apply add_le_add _ <| mem_closedBall_iff_norm.mp α.mem_closedBall₀
      rw [← dist_eq_norm]
      exact α.lipschitzWith.dist_le_mul t t₀
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) + r := by
      gcongr
      exact abs_sub_le_max_sub t.2.1 t.2.2 _
    _ ≤ a - r + r := add_le_add_right h _
    _ = a := sub_add_cancel _ _

lemma compProj_mem_closedBall
    (α : FunSpace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) {t : ℝ} :
    α.compProj t ∈ closedBall x₀ a := by
  rw [compProj_apply]
  exact α.mem_closedBall h

end

/-! ## Contracting map on the space of Lipschitz functions -/

section

variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x y : E} {a r L K : ℝ≥0}

/-- The integrand in `next` is continuous. -/
lemma continuousOn_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K) (α : FunSpace t₀ x₀ r L) :
    ContinuousOn (fun t' ↦ f t' (α.compProj t')) (Icc tmin tmax) :=
  continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    α.continuous_compProj.continuousOn
    fun _ _ ↦ α.mem_closedBall hf.mul_max_le

/-- The integrand in `next` is integrable. -/
lemma intervalIntegrable_comp_compProj (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun t' ↦ f t' (α.compProj t')) volume t₀ t := by
  apply ContinuousOn.intervalIntegrable
  apply α.continuousOn_comp_compProj hf |>.mono
  exact uIcc_subset_Icc t₀.2 t.2

/-- The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be a contracting
map -/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := picard f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf _ t₂), Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    -- Can `grind` do this in the future?
    have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
    exact hf.norm_le _ ht _ <| α.mem_closedBall hf.mul_max_le
  mem_closedBall₀ := by simp [hx]

@[simp]
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} :
    next hf hx α t = picard f t₀ x α.compProj t := rfl

lemma next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x := by simp

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) (t : Icc tmin tmax)
    {α β : FunSpace t₀ x₀ r L}
    (h : dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t - t₀.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf hx)^[n] α t)) (f t ((next hf hx)^[n] β t)) ≤
      K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) :=
      hf.lipschitzOnWith t.1 t.2 |>.dist_le_mul
        _ (FunSpace.mem_closedBall hf.mul_max_le) _ (FunSpace.mem_closedBall hf.mul_max_le)
    _ ≤ K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two curves -/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_compProj hf _ t)
        (intervalIntegrable_comp_compProj hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        -- Can `grind` do this in the future?
        have ht' : t' ∈ Icc tmin tmax :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₀.2 t.2) ht'
        rw [← dist_eq_norm, compProj_of_mem, compProj_of_mem]
        exact dist_comp_iterate_next_le hf hx _ ⟨t', ht'⟩ (hn _)
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        -- critical: `integral_pow_abs_sub_uIoc`
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- The `n`-th iterate of `next` is Lipschitz continuous with respect to `FunSpace`, with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (α β : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist ((next hf hx)^[n] α) ((next hf hx)^[n] β) ≤
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le hf hx α β n t
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity

/-- Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz constant is
independent of the initial point. -/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ∀ (x : E) (hx : x ∈ closedBall x₀ r),
      ContractingWith C (next hf hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! := by
    have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨n, ⟨_, this⟩, fun x hx ↦ ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β ↦ dist_iterate_next_iterate_next_le hf hx α β n⟩

/-- The map `next` has a fixed point in the space of curves. This will be used to construct a
solution `α : ℝ → E` to the ODE. -/
lemma exists_isFixedPt_next [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : FunSpace t₀ x₀ r L, IsFixedPt (next hf hx) α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
  ⟨_, h x hx |>.isFixedPt_fixedPoint_iterate⟩

/-! ## Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^[n] α`.
-/

/-- A key step in the base case of `exists_forall_closedBall_funSpace_dist_le_mul` -/
lemma dist_next_next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (hy : y ∈ closedBall x₀ r) (α : FunSpace t₀ x₀ r L) :
    dist (next hf hx α) (next hf hy α) = dist x y := by
  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm]
  simp [add_sub_add_right_eq_sub, dist_eq_norm]

lemma dist_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) (n : ℕ) :
    dist α ((next hf hx)^[n] α) ≤
      (∑ i ∈ Finset.range n, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !)
        * dist α (next hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
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
  nth_rw 1 [← iterate_zero_apply (next hf hx) α]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  apply le_trans <| hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc, mul_comm ((C : ℝ) ^ i), ← mul_assoc]
  gcongr
  exact dist_iterate_next_le hf hx α m

/-- The pointwise distance between any two integral curves `α` and `β` over their domains is bounded
by a constant `L'` times the distance between their respective initial points. This is the result of
taking the limit of `dist_iterate_iterate_next_le_of_lipschitzWith` as `n → ∞`. This implies that
the local solution of a vector field is Lipschitz continuous in the initial condition. -/
lemma exists_forall_closedBall_funSpace_dist_le_mul [CompleteSpace E]
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ L' : ℝ≥0, ∀ (x y : E) (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r)
      (α β : FunSpace t₀ x₀ r L) (_ : IsFixedPt (next hf hx) α) (_ : IsFixedPt (next hf hy) β),
      dist α β ≤ L' * dist x y := by
  obtain ⟨m, C, h⟩ := exists_contractingWith_iterate_next hf
  let L' := (∑ i ∈ Finset.range m, (K * max (tmax - t₀) (t₀ - tmin)) ^ i / i !) * (1 - C)⁻¹
  have hL' : 0 ≤ L' := by
    have : 0 ≤ max (tmax - t₀) (t₀ - tmin) := le_max_of_le_left <| sub_nonneg_of_le t₀.2.2
    positivity
  refine ⟨⟨L', hL'⟩, fun x y hx hy α β hα hβ ↦ ?_⟩
  rw [NNReal.coe_mk]
  apply le_of_tendsto_of_tendsto' (b := Filter.atTop) _ _ <|
    dist_iterate_iterate_next_le_of_lipschitzWith hf hy α (h y hy).2
  · apply Filter.Tendsto.comp (y := 𝓝 β) (tendsto_const_nhds.dist Filter.tendsto_id)
    rw [h y hy |>.fixedPoint_unique (hβ.iterate m)]
    exact h y hy |>.tendsto_iterate_fixedPoint α
  · nth_rw 1 [← hα, dist_next_next]
    apply Filter.Tendsto.mul_const
    apply Filter.Tendsto.const_mul
    convert hasSum_geometric_of_lt_one C.2 (h y hy).1 |>.tendsto_sum_nat
    simp [NNReal.coe_sub <| le_of_lt (h y hy).1, NNReal.coe_one]

end

end FunSpace

/-! ## Properties of the integral equation -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

-- TODO: generalise to open sets and `Ici` and `Iic`
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `picard f t₀ x₀ α`. -/
lemma hasDerivWithinAt_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
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

/-- Converse of `hasDerivWithinAt_picard_Icc`: if `f` is the derivative along `α`, then `α`
satisfies the integral equation. -/
lemma picard_eq_of_hasDerivAt {t : ℝ}
    (hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u))
    (hα : ∀ t' ∈ uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t')
    (hmap : MapsTo α (uIcc t₀ t) u) :
    picard f t₀ (α t₀) α t = α t := by
  rw [← add_sub_cancel (α t₀) (α t), picard_apply,
    integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
  exact hα t' (Ioo_subset_Icc_self ht') |>.hasDerivAt <| Icc_mem_nhds ht'.1 ht'.2

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`. -/
lemma contDiffOn_nat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t ∈ Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
      simp only [Nat.cast_add, Nat.cast_one] at *
      rw [contDiffOn_succ_iff_derivWithin <| uniqueDiffOn_Icc hlt]
      refine ⟨fun t ht ↦ HasDerivWithinAt.differentiableWithinAt (this t ht), by simp, ?_⟩
      apply contDiffOn_comp hf.of_succ (ContDiffOn.congr (hn hf.of_succ) heqon) hmem |>.congr
      intro t ht
      exact HasDerivWithinAt.derivWithin (this t ht) <| (uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ht
  · rw [(subsingleton_Icc_of_ge (not_lt.mp hlt)).eq_singleton_of_mem ht₀]
    intro t ht
    rw [eq_of_mem_singleton ht]
    exact contDiffWithinAt_singleton

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ∞`.

TODO: Extend to the analytic `n = ⊤` case. -/
lemma contDiffOn_enat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k ↦ contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

/-- Solutions to ODEs defined by $C^n$ vector fields are also $C^n$. -/
theorem contDiffOn_enat_Icc_of_hasDerivWithinAt {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hmem : MapsTo α (Icc tmin tmax) u) :
    ContDiffOn ℝ n α (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ ∈ Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t ⊆ Icc tmin tmax := uIcc_subset_Icc ht₀ ht
      rw [picard_eq_of_hasDerivAt (hf.continuousOn.mono (prod_subset_prod_left this))
        (fun t' ht' ↦ hα t' (this ht') |>.mono this) (hmem.mono_left this)]
    exact contDiffOn_enat_picard_Icc ht₀ hf (HasDerivWithinAt.continuousOn hα) hmem (α t₀) this
      |>.congr this
  · rw [not_lt, le_iff_lt_or_eq] at hlt
    cases hlt with
    | inl h =>
      intro _ ht
      rw [Icc_eq_empty (not_le.mpr h)] at ht
      exfalso
      exact notMem_empty _ ht
    | inr h =>
      rw [h, Icc_self]
      intro _ ht
      rw [eq_of_mem_singleton ht]
      exact contDiffWithinAt_singleton

end

end ODE

namespace IsPicardLindelof

/-! ## Properties of `IsPicardLindelof` -/

section

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

lemma continuousOn_uncurry (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a)) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

/-- The special case where the vector field is independent of time -/
lemma of_time_independent
    {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hb : ∀ x ∈ closedBall x₀ a, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a))
    (hm : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    (IsPicardLindelof (fun _ ↦ f) t₀ x₀ a r L K) where
  lipschitzOnWith := fun _ _ ↦ hl
  continuousOn := fun _ _ ↦ continuousOn_const
  norm_le := fun _ _ ↦ hb
  mul_max_le := hm

/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
lemma of_contDiffAt_one [NormedSpace ℝ E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), IsPicardLindelof (fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        rw [← dist_eq_norm, ← dist_eq_norm]
        apply hl.dist_le_mul x _ x₀ (mem_of_mem_nhds hs)
        apply subset_trans _ has hx
        exact closedBall_subset_ball <| half_lt_self ha -- this is where we need `a / 2`
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    ⟨a / 2, le_of_lt <| half_pos ha⟩, ⟨a / 2, le_of_lt <| half_pos ha⟩ / 2,
    ⟨L, le_of_lt hL0⟩, K, half_pos <| half_pos ha, ?_⟩
  apply of_time_independent hb <|
    hl.mono <| subset_trans (closedBall_subset_ball (half_lt_self ha)) has
  rw [NNReal.coe_mk, add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_div,
    NNReal.coe_two, NNReal.coe_mk, mul_comm, ← le_div_iff₀ hL0, sub_half, div_right_comm (a / 2),
    div_right_comm a]

end

/-! ## Existence of solutions to ODEs -/

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, integral form. This version shows the existence
of a local solution whose initial point `x` may be different from the centre `x₀` of the closed
ball within which the properties of the vector field hold. -/
theorem exists_eq_forall_mem_Icc_eq_picard
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t = ODE.picard f t₀ x α t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨(FunSpace.next hf hx α).compProj, by simp, fun t ht ↦ ?_⟩
  rw [FunSpace.compProj_apply, FunSpace.next_apply, hα, projIcc_of_mem _ ht]

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution whose initial point `x` may be different from the centre `x₀` of
the closed ball within which the properties of the vector field hold. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

@[deprecated (since := "2025-06-24")] alias exists_forall_hasDerivWithinAt_Icc_eq :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt₀

open Classical in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the initial point. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is continuous on its domain as a (partial) map `E × ℝ → E`. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx ↦ HasDerivWithinAt.continuousOn (hα1 x hx).2

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow. -/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hf
  ⟨α, hα.1⟩

end IsPicardLindelof

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf t₀
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨α, hα1, fun t ht ↦ ?_⟩
  exact hα2 t (Ioo_subset_Icc_self ht) |>.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨α, hα1, ε, hε, hα2⟩

@[deprecated (since := "2025-06-24")] alias exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt :=
  exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_eventually_eq_hasDerivAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : E → ℝ → E, ∀ᶠ xt in 𝓝 x₀ ×ˢ 𝓝 t₀,
      α xt.1 t₀ = xt.1 ∧ HasDerivAt (α xt.1) (f (α xt.1 xt.2)) xt.2 := by
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  choose α hα using H
  refine ⟨fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then α x hx else 0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), ?_, ?_⟩
  · rw [Filter.prod_mem_prod_iff]
    exact ⟨closedBall_mem_nhds x₀ hr, Ioo_mem_nhds (by linarith) (by linarith)⟩
  · grind

end ContDiffAt
