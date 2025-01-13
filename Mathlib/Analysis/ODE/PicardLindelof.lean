/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
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
repeated applications of the right hand side of this equation.

## Main definitions and results

* `integrate f t₀ x₀ α t`: the right hand side of the integral equation, applied to the curve `α`.
* `IsPicardLindelof`: the structure holding the assumptions of the Picard-Lindelöf theorem.
* `IsPicardLindelof.exists_eq_hasDerivWithinAt`: the existence theorem for local solutions to
  time-dependent ODEs.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_Icc`: the existence theorem for
  local flows to time-dependent vector fields.

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
* We only prove the existence of a solution in this file. For uniqueness, see `ODE_solution_unique`
  and related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation, dynamical system, initial value problem

-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation that is
equivalent to the initial value problem defined by `f`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

/-- The main integral expression on which the Picard-Lindelöf theorem is built. It will be shown
that if `α : ℝ → E` and `integral f t₀ x₀ α` agree on an interval containing `t₀`, then `α` is a
solution to `f` with `α t₀ = x₀` on this interval. -/
noncomputable def integrate (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma integrate_apply {x₀ : E} {t : ℝ} : integrate f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

lemma integrate_apply₀ {x₀ : E} : integrate f t₀ x₀ α t₀ = x₀ := by
  simp only [integrate_apply, integral_same, add_zero]

/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl -- should this be a lemma?
  rw [this]
  apply hf.comp <| contDiffOn_id.prod hα
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

/-- Given a continuous time-dependent vector field `f` and a continuous curve `α`, the composition
`f t (α t)` is continuous in `t`. -/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem

end

/-! ## Assumptions of the Picard-Lindelof theorem-/

/-- Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K` means that the time-dependent vector field `f` satisfies the
conditions to admit an integral curve `α : ℝ → E` to `f` defined on `Icc tmin tmax` with the
initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Note that the initial point `x` is allowed
to differ from the point `x₀` about which the conditions on `f` are stated. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz in with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

/-! ## Space of Lipschitz functions on a closed interval

We define the space of Lipschitz continuous functions from a closed interval. This will be shown to
be a complete metric space on which `integrate` is a contracting map, leading to a fixed point that
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

/-- The constant map -/
instance : Inhabited (FunSpace t₀ x₀ r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken (zero_le _), mem_closedBall_self r.2⟩

protected lemma continuous (α : FunSpace t₀ x₀ L r) : Continuous α := α.lipschitzWith.continuous

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

lemma compProj_subtype {α : FunSpace t₀ x₀ r L} {t : Icc tmin tmax} :
    α.compProj t = α t := by simp only [compProj_apply, projIcc_val]

@[continuity]
lemma continuous_compProj (α : FunSpace t₀ x₀ r L) : Continuous α.compProj :=
  α.continuous.comp continuous_projIcc

/-- The image of a function in `FunSpace` is contained within a closedBall. -/
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
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ L.2
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

/-- The map on `FunSpace` defined by `integrate`, some `n`-th interate of which will be a
contracting map -/
noncomputable def next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := integrate f t₀ x α.compProj t
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, integrate_apply, integrate_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left (intervalIntegrable_comp_compProj hf _ t₁)
        (intervalIntegrable_comp_compProj hf _ t₂), Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    -- any tactic for this?
    have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
    exact hf.norm_le _ ht _ <| α.mem_closedBall hf.mul_max_le
  mem_closedBall₀ := by simp [hx]

@[simp]
lemma next_apply (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} :
    next hf hx α t = integrate f t₀ x α.compProj t := rfl

lemma next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x := by simp

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) (t : Icc tmin tmax)
    (α β : FunSpace t₀ x₀ r L)
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
      apply mul_le_mul_of_nonneg_left _ K.2
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
      next_apply, integrate_apply, integrate_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_compProj hf _ t)
        (intervalIntegrable_comp_compProj hf _ t)]
    calc
      _ ≤ ∫ τ in Ι t₀.1 t.1, K ^ (n + 1) * |τ - t₀| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply norm_integral_le_of_norm_le <| Continuous.integrableOn_uIoc (by fun_prop)
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        -- any tactic for this?
        have ht' : t' ∈ Icc tmin tmax :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₀.2 t.2) ht'
        rw [← dist_eq_norm, compProj_apply, compProj_apply, projIcc_of_mem _ ht']
        exact dist_comp_iterate_next_le hf hx _ ⟨t', ht'⟩ _ _ (hn _)
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

/-- The map `next` has a fixed point in the space of curves. This will be used to construct a
solution `α : ℝ → E` to the ODE. -/
lemma exists_funSpace_next_eq [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : FunSpace t₀ x₀ r L, IsFixedPt (next hf hx) α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_next hf
  ⟨_, h x hx |>.isFixedPt_fixedPoint_iterate⟩

end

end FunSpace

end ODE
