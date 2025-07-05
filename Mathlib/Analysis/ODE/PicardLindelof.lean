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

In this file we prove that an ordinary differential equation $\dot x=v(t, x)$ such that $v$ is
Lipschitz continuous in $x$ and continuous in $t$ has a local solution, see
`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq`.

As a corollary, we prove that a time-independent locally continuously differentiable ODE has a
local solution.

## Implementation notes

In order to split the proof into small lemmas, we introduce a structure `PicardLindelof` that holds
all assumptions of the main theorem. This structure and lemmas in the `PicardLindelof` namespace
should be treated as private implementation details. This is not to be confused with the `Prop`-
valued structure `IsPicardLindelof`, which holds the long hypotheses of the Picard-Lindelöf
theorem for actual use as part of the public API.

We only prove existence of a solution in this file. For uniqueness see `ODE_solution_unique` and
related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation
-/

open Filter Function Set Metric TopologicalSpace intervalIntegral MeasureTheory
open MeasureTheory.MeasureSpace (volume)
open scoped Filter Topology NNReal ENNReal Nat Interval

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `Prop` structure holding the hypotheses of the Picard-Lindelöf theorem.

The similarly named `PicardLindelof` structure is part of the internal API for convenience, so as
not to constantly invoke choice, but is not intended for public use. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E] (v : ℝ → E → E) (tMin t₀ tMax : ℝ)
    (x₀ : E) (L : ℝ≥0) (R C : ℝ) : Prop where
  ht₀ : t₀ ∈ Icc tMin tMax
  hR : 0 ≤ R
  lipschitz : ∀ t ∈ Icc tMin tMax, LipschitzOnWith L (v t) (closedBall x₀ R)
  cont : ∀ x ∈ closedBall x₀ R, ContinuousOn (fun t : ℝ => v t x) (Icc tMin tMax)
  norm_le : ∀ t ∈ Icc tMin tMax, ∀ x ∈ closedBall x₀ R, ‖v t x‖ ≤ C
  C_mul_le_R : (C : ℝ) * max (tMax - t₀) (t₀ - tMin) ≤ R

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. It is part of
the internal API for convenience, so as not to constantly invoke choice. Unless you want to use one
of the auxiliary lemmas, use `IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq` instead
of using this structure.

The similarly named `IsPicardLindelof` is a bundled `Prop` holding the long hypotheses of the
Picard-Lindelöf theorem as named arguments. It is used as part of the public API.
-/
structure PicardLindelof (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Function of the initial value problem -/
  toFun : ℝ → E → E
  /-- Lower limit of `t` -/
  tMin : ℝ
  /-- Upper limit of `t` -/
  tMax : ℝ
  /-- Initial value of `t` -/
  t₀ : Icc tMin tMax
  /-- Initial value of `x` -/
  x₀ : E
  /-- Bound of the function over the region of interest -/
  C : ℝ≥0
  /-- Radius of closed ball in `x` over which the bound `C` holds -/
  R : ℝ≥0
  /-- Lipschitz constant of the function -/
  L : ℝ≥0
  isPicardLindelof : IsPicardLindelof toFun tMin t₀ tMax x₀ L R C

namespace PicardLindelof

variable (v : PicardLindelof E)

instance : CoeFun (PicardLindelof E) fun _ => ℝ → E → E :=
  ⟨toFun⟩

instance : Inhabited (PicardLindelof E) :=
  ⟨⟨0, 0, 0, ⟨0, le_rfl, le_rfl⟩, 0, 0, 0, 0,
      { ht₀ := by rw [Subtype.coe_mk, Icc_self]; exact mem_singleton _
        hR := le_rfl
        lipschitz := fun _ _ => (LipschitzWith.const 0).lipschitzOnWith
        cont := fun _ _ => by simpa only [Pi.zero_apply] using continuousOn_const
        norm_le := fun _ _ _ _ => norm_zero.le
        C_mul_le_R := (zero_mul _).le }⟩⟩

theorem tMin_le_tMax : v.tMin ≤ v.tMax :=
  v.t₀.2.1.trans v.t₀.2.2

protected theorem nonempty_Icc : (Icc v.tMin v.tMax).Nonempty :=
  nonempty_Icc.2 v.tMin_le_tMax

protected theorem lipschitzOnWith {t} (ht : t ∈ Icc v.tMin v.tMax) :
    LipschitzOnWith v.L (v t) (closedBall v.x₀ v.R) :=
  v.isPicardLindelof.lipschitz t ht

protected theorem continuousOn :
    ContinuousOn (uncurry v) (Icc v.tMin v.tMax ×ˢ closedBall v.x₀ v.R) :=
  have : ContinuousOn (uncurry (flip v)) (closedBall v.x₀ v.R ×ˢ Icc v.tMin v.tMax) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ v.L v.isPicardLindelof.cont
      v.isPicardLindelof.lipschitz
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset

theorem norm_le {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) {x : E} (hx : x ∈ closedBall v.x₀ v.R) :
    ‖v t x‖ ≤ v.C :=
  v.isPicardLindelof.norm_le _ ht _ hx

/-- The maximum of distances from `t₀` to the endpoints of `[tMin, tMax]`. -/
def tDist : ℝ :=
  max (v.tMax - v.t₀) (v.t₀ - v.tMin)

theorem tDist_nonneg : 0 ≤ v.tDist :=
  le_max_iff.2 <| Or.inl <| sub_nonneg.2 v.t₀.2.2

theorem dist_t₀_le (t : Icc v.tMin v.tMax) : dist t v.t₀ ≤ v.tDist := by
  rw [Subtype.dist_eq, Real.dist_eq]
  rcases le_total t v.t₀ with ht | ht
  · rw [abs_of_nonpos (sub_nonpos.2 <| Subtype.coe_le_coe.2 ht), neg_sub]
    exact (sub_le_sub_left t.2.1 _).trans (le_max_right _ _)
  · rw [abs_of_nonneg (sub_nonneg.2 <| Subtype.coe_le_coe.2 ht)]
    exact (sub_le_sub_right t.2.2 _).trans (le_max_left _ _)

/-- Projection $ℝ → [t_{\min}, t_{\max}]$ sending $(-∞, t_{\min}]$ to $t_{\min}$ and $[t_{\max}, ∞)$
to $t_{\max}$. -/
def proj : ℝ → Icc v.tMin v.tMax :=
  projIcc v.tMin v.tMax v.tMin_le_tMax

theorem proj_coe (t : Icc v.tMin v.tMax) : v.proj t = t :=
  projIcc_val _ _

theorem proj_of_mem {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) : ↑(v.proj t) = t := by
  simp only [proj, projIcc_of_mem v.tMin_le_tMax ht]

@[continuity, fun_prop]
theorem continuous_proj : Continuous v.proj :=
  continuous_projIcc

/-- The space of curves $γ \colon [t_{\min}, t_{\max}] \to E$ such that $γ(t₀) = x₀$ and $γ$ is
Lipschitz continuous with constant $C$. The map sending $γ$ to
$\mathbf Pγ(t)=x₀ + ∫_{t₀}^{t} v(τ, γ(τ))\,dτ$ is a contracting map on this space, and its fixed
point is a solution of the ODE $\dot x=v(t, x)$. -/
structure FunSpace where
  /-- The particular curve represented by this object. -/
  toFun : Icc v.tMin v.tMax → E
  map_t₀' : toFun v.t₀ = v.x₀
  lipschitz' : LipschitzWith v.C toFun

namespace FunSpace

variable {v}
variable (f : FunSpace v)

instance : CoeFun (FunSpace v) fun _ => Icc v.tMin v.tMax → E :=
  ⟨toFun⟩

instance : Inhabited v.FunSpace :=
  ⟨⟨fun _ => v.x₀, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩⟩

protected theorem lipschitz : LipschitzWith v.C f :=
  f.lipschitz'

protected theorem continuous : Continuous f :=
  f.lipschitz.continuous

/-- Each curve in `PicardLindelof.FunSpace` is continuous. -/
def toContinuousMap : v.FunSpace ↪ C(Icc v.tMin v.tMax, E) :=
  ⟨fun f => ⟨f, f.continuous⟩, fun f g h => by cases f; cases g; simpa using h⟩

instance : MetricSpace v.FunSpace :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

theorem isUniformInducing_toContinuousMap : IsUniformInducing (@toContinuousMap _ _ _ v) :=
  ⟨rfl⟩

theorem range_toContinuousMap :
    range toContinuousMap =
      {f : C(Icc v.tMin v.tMax, E) | f v.t₀ = v.x₀ ∧ LipschitzWith v.C f} := by
  ext f; constructor
  · rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩; exact ⟨hf₀, hf_lip⟩
  · rcases f with ⟨f, hf⟩; rintro ⟨hf₀, hf_lip⟩; exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩

theorem map_t₀ : f v.t₀ = v.x₀ :=
  f.map_t₀'

protected theorem mem_closedBall (t : Icc v.tMin v.tMax) : f t ∈ closedBall v.x₀ v.R :=
  calc
    dist (f t) v.x₀ = dist (f t) (f.toFun v.t₀) := by rw [f.map_t₀']
    _ ≤ v.C * dist t v.t₀ := f.lipschitz.dist_le_mul _ _
    _ ≤ v.C * v.tDist := by gcongr; apply v.dist_t₀_le
    _ ≤ v.R := v.isPicardLindelof.C_mul_le_R

/-- Given a curve $γ \colon [t_{\min}, t_{\max}] → E$, `PicardLindelof.vComp` is the function
$F(t)=v(π t, γ(π t))$, where `π` is the projection $ℝ → [t_{\min}, t_{\max}]$. The integral of this
function is the image of `γ` under the contracting map we are going to define below. -/
def vComp (t : ℝ) : E :=
  v (v.proj t) (f (v.proj t))

theorem vComp_apply_coe (t : Icc v.tMin v.tMax) : f.vComp t = v t (f t) := by
  simp only [vComp, proj_coe]

theorem continuous_vComp : Continuous f.vComp := by
  have := (continuous_subtype_val.prodMk f.continuous).comp v.continuous_proj
  refine ContinuousOn.comp_continuous v.continuousOn this fun x => ?_
  exact ⟨(v.proj x).2, f.mem_closedBall _⟩

theorem norm_vComp_le (t : ℝ) : ‖f.vComp t‖ ≤ v.C :=
  v.norm_le (v.proj t).2 <| f.mem_closedBall _

theorem dist_apply_le_dist (f₁ f₂ : FunSpace v) (t : Icc v.tMin v.tMax) :
    dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
  @ContinuousMap.dist_apply_le_dist _ _ _ _ _ (toContinuousMap f₁) (toContinuousMap f₂) _

theorem dist_le_of_forall {f₁ f₂ : FunSpace v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) :
    dist f₁ f₂ ≤ d :=
  (@ContinuousMap.dist_le_iff_of_nonempty _ _ _ _ _ (toContinuousMap f₁) (toContinuousMap f₂) _
    v.nonempty_Icc.to_subtype).2 h

instance [CompleteSpace E] : CompleteSpace v.FunSpace := by
  refine (completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap).2
      (IsClosed.isComplete ?_)
  rw [range_toContinuousMap, setOf_and]
  refine (isClosed_eq (continuous_eval_const _) continuous_const).inter ?_
  have : IsClosed {f : Icc v.tMin v.tMax → E | LipschitzWith v.C f} :=
    isClosed_setOf_lipschitzWith v.C
  exact this.preimage continuous_coeFun

theorem intervalIntegrable_vComp (t₁ t₂ : ℝ) : IntervalIntegrable f.vComp volume t₁ t₂ :=
  f.continuous_vComp.intervalIntegrable _ _

/-- The Picard-Lindelöf operator. This is a contracting map on `PicardLindelof.FunSpace v` such
that the fixed point of this map is the solution of the corresponding ODE.

More precisely, some iteration of this map is a contracting map. -/
def next (f : FunSpace v) : FunSpace v where
  toFun t := v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ
  map_t₀' := by simp only [integral_same, add_zero]
  lipschitz' := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_add_left, dist_eq_norm,
      integral_interval_sub_left (f.intervalIntegrable_vComp _ _) (f.intervalIntegrable_vComp _ _)]
    exact norm_integral_le_of_norm_le_const fun t _ => f.norm_vComp_le _

theorem next_apply (t : Icc v.tMin v.tMax) : f.next t = v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ :=
  rfl

theorem dist_next_apply_le_of_le {f₁ f₂ : FunSpace v} {n : ℕ} {d : ℝ}
    (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ n / n ! * d) (t : Icc v.tMin v.tMax) :
    dist (next f₁ t) (next f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ (n + 1) / (n + 1)! * d := by
  simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub, ←
    intervalIntegral.integral_sub (intervalIntegrable_vComp _ _ _)
      (intervalIntegrable_vComp _ _ _),
    norm_integral_eq_norm_integral_uIoc] at *
  calc
    ‖∫ τ in Ι (v.t₀ : ℝ) t, f₁.vComp τ - f₂.vComp τ‖ ≤
        ∫ τ in Ι (v.t₀ : ℝ) t, v.L * ((v.L * |τ - v.t₀|) ^ n / n ! * d) := by
      refine norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop)) ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun τ hτ ↦ ?_
      refine (v.lipschitzOnWith (v.proj τ).2).norm_sub_le_of_le (f₁.mem_closedBall _)
          (f₂.mem_closedBall _) ((h _).trans_eq ?_)
      rw [v.proj_of_mem]
      exact uIcc_subset_Icc v.t₀.2 t.2 <| Ioc_subset_Icc_self hτ
    _ = (v.L * |t.1 - v.t₀|) ^ (n + 1) / (n + 1)! * d := by
      simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const, integral_pow_abs_sub_uIoc, div_eq_mul_inv,
        pow_succ' (v.L : ℝ), Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv, mul_assoc]

theorem dist_iterate_next_apply_le (f₁ f₂ : FunSpace v) (n : ℕ) (t : Icc v.tMin v.tMax) :
    dist (next^[n] f₁ t) (next^[n] f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ n / n ! * dist f₁ f₂ := by
  induction n generalizing t with
  | zero =>
    rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    exact dist_apply_le_dist f₁ f₂ t
  | succ n ihn =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact dist_next_apply_le_of_le ihn _

theorem dist_iterate_next_le (f₁ f₂ : FunSpace v) (n : ℕ) :
    dist (next^[n] f₁) (next^[n] f₂) ≤ (v.L * v.tDist) ^ n / n ! * dist f₁ f₂ := by
  refine dist_le_of_forall fun t => (dist_iterate_next_apply_le _ _ _ _).trans ?_
  have : |(t - v.t₀ : ℝ)| ≤ v.tDist := v.dist_t₀_le t
  gcongr

variable [CompleteSpace E]

theorem hasDerivWithinAt_next (t : Icc v.tMin v.tMax) :
    HasDerivWithinAt (f.next ∘ v.proj) (v t (f t)) (Icc v.tMin v.tMax) t := by
  haveI : Fact ((t : ℝ) ∈ Icc v.tMin v.tMax) := ⟨t.2⟩
  simp only [Function.comp_def, next_apply]
  refine HasDerivWithinAt.const_add _ ?_
  have : HasDerivWithinAt (∫ τ in v.t₀..·, f.vComp τ) (f.vComp t) (Icc v.tMin v.tMax) t :=
    integral_hasDerivWithinAt_right (f.intervalIntegrable_vComp _ _)
      (f.continuous_vComp.stronglyMeasurableAtFilter _ _)
      f.continuous_vComp.continuousWithinAt
  rw [vComp_apply_coe] at this
  refine this.congr_of_eventuallyEq_of_mem ?_ t.coe_prop
  filter_upwards [self_mem_nhdsWithin] with _ ht'
  rw [v.proj_of_mem ht']

end FunSpace

section

theorem exists_contracting_iterate :
    ∃ (N : ℕ) (K : _), ContractingWith K (FunSpace.next : v.FunSpace → v.FunSpace)^[N] := by
  rcases ((FloorSemiring.tendsto_pow_div_factorial_atTop (v.L * v.tDist)).eventually
    (gt_mem_nhds zero_lt_one)).exists with ⟨N, hN⟩
  have : (0 : ℝ) ≤ (v.L * v.tDist) ^ N / N ! :=
    div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.tDist_nonneg) _) (Nat.cast_nonneg _)
  exact ⟨N, ⟨_, this⟩, hN, LipschitzWith.of_dist_le_mul fun f g =>
    FunSpace.dist_iterate_next_le f g N⟩

theorem exists_fixed [CompleteSpace E] : ∃ f : v.FunSpace, f.next = f :=
  let ⟨_N, _K, hK⟩ := exists_contracting_iterate v
  ⟨_, hK.isFixedPt_fixedPoint_iterate⟩

end

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. Use
`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq` instead for the public API. -/
theorem exists_solution [CompleteSpace E] :
    ∃ f : ℝ → E, f v.t₀ = v.x₀ ∧ ∀ t ∈ Icc v.tMin v.tMax,
      HasDerivWithinAt f (v t (f t)) (Icc v.tMin v.tMax) t := by
  rcases v.exists_fixed with ⟨f, hf⟩
  refine ⟨f ∘ v.proj, ?_, fun t ht => ?_⟩
  · simp only [(· ∘ ·), proj_coe, f.map_t₀]
  · simp only [(· ∘ ·), v.proj_of_mem ht]
    lift t to Icc v.tMin v.tMax using ht
    simpa only [hf, v.proj_coe] using f.hasDerivWithinAt_next t

end PicardLindelof

theorem IsPicardLindelof.norm_le₀ {E : Type*} [NormedAddCommGroup E] {v : ℝ → E → E}
    {tMin t₀ tMax : ℝ} {x₀ : E} {C R : ℝ} {L : ℝ≥0}
    (hpl : IsPicardLindelof v tMin t₀ tMax x₀ L R C) : ‖v t₀ x₀‖ ≤ C :=
  hpl.norm_le t₀ hpl.ht₀ x₀ <| mem_closedBall_self hpl.hR

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq [CompleteSpace E] {v : ℝ → E → E}
    {tMin t₀ tMax : ℝ} (x₀ : E) {C R : ℝ} {L : ℝ≥0}
    (hpl : IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧
      ∀ t ∈ Icc tMin tMax, HasDerivWithinAt f (v t (f t)) (Icc tMin tMax) t := by
  lift C to ℝ≥0 using (norm_nonneg _).trans hpl.norm_le₀
  lift t₀ to Icc tMin tMax using hpl.ht₀
  exact PicardLindelof.exists_solution
    ⟨v, tMin, tMax, t₀, x₀, C, ⟨R, hpl.hR⟩, L, { hpl with ht₀ := t₀.property }⟩

variable {v : E → E} (t₀ : ℝ) {x₀ : E}

/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
  Picard-Lindelöf theorem. -/
theorem exists_isPicardLindelof_const_of_contDiffAt (hv : ContDiffAt ℝ 1 v x₀) :
    ∃ ε > (0 : ℝ), ∃ L R C, IsPicardLindelof (fun _ => v) (t₀ - ε) t₀ (t₀ + ε) x₀ L R C := by
  obtain ⟨L, s, hs, hlip⟩ := hv.exists_lipschitzOnWith
  obtain ⟨R₁, hR₁ : 0 < R₁, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨R₂, hR₂ : 0 < R₂, hbdd⟩ := Metric.continuousAt_iff.mp hv.continuousAt.norm 1 zero_lt_one
  have hbdd' : ∀ x ∈ Metric.ball x₀ R₂, ‖v x‖ ≤ 1 + ‖v x₀‖ := fun _ hx =>
    sub_le_iff_le_add.mp <| le_of_lt <| lt_of_abs_lt <| Real.dist_eq _ _ ▸ hbdd hx
  set ε := min R₁ R₂ / 2 / (1 + ‖v x₀‖) with hε
  have hε0 : 0 < ε := hε ▸ div_pos (half_pos <| lt_min hR₁ hR₂)
    (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _))
  refine ⟨ε, hε0, L, min R₁ R₂ / 2, 1 + ‖v x₀‖, ?_⟩
  exact
    { ht₀ := Real.closedBall_eq_Icc ▸ mem_closedBall_self hε0.le
      hR := by positivity
      lipschitz := fun _ _ => hlip.mono <|
        (closedBall_subset_ball <| half_lt_self <| lt_min hR₁ hR₂).trans <|
        (Metric.ball_subset_ball <| min_le_left _ _).trans hball
      cont := fun _ _ => continuousOn_const
      norm_le := fun _ _ x hx => hbdd' x <| mem_of_mem_of_subset hx <|
        (closedBall_subset_ball <| half_lt_self <| lt_min hR₁ hR₂).trans <|
        (Metric.ball_subset_ball <| min_le_right _ _).trans (subset_refl _)
      C_mul_le_R := by
        rw [add_sub_cancel_left, sub_sub_cancel, max_self, hε, mul_div_left_comm, div_self, mul_one]
        exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| norm_nonneg _ }

variable [CompleteSpace E]

/-- A time-independent, continuously differentiable ODE admits a solution in some open interval. -/
theorem exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt (hv : ContDiffAt ℝ 1 v x₀) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (v (f t)) t := by
  obtain ⟨ε, hε, _, _, _, hpl⟩ := exists_isPicardLindelof_const_of_contDiffAt t₀ hv
  obtain ⟨f, hf1, hf2⟩ := hpl.exists_forall_hasDerivWithinAt_Icc_eq x₀
  exact ⟨f, hf1, ε, hε, fun t ht =>
    (hf2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

/-- A time-independent, continuously differentiable ODE admits a solution in some open interval. -/
theorem exists_forall_hasDerivAt_Ioo_eq_of_contDiff (hv : ContDiff ℝ 1 v) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (v (f t)) t :=
  let ⟨f, hf1, ε, hε, hf2⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀ hv.contDiffAt
  ⟨f, hf1, ε, hε, fun _ h => hf2 _ h⟩
