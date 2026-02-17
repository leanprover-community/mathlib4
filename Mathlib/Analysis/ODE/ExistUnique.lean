/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Existence and uniqueness of integral curves in normed spaces

This file states the results of Gronwall's inequality and the Picard-Lindelöf theorem in terms
of the integral curve API (`IsIntegralCurve`, `IsIntegralCurveOn`, `IsIntegralCurveAt`).

## Main results

* `IsPicardLindelof.exists_eq_isIntegralCurveOn`: the Picard-Lindelöf theorem, stating the
  existence of a local integral curve to a time-dependent ODE.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith`: the
  existence of a local flow that is Lipschitz continuous in the initial point.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_isIntegralCurveOn_continuousOn`: the existence
  of a local flow that is continuous on its domain as a map `E × ℝ → E`.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_isIntegralCurveOn`: the existence of a local
  flow to a time-dependent vector field.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn`: a `C¹` vector field
  admits integral curves on open intervals for all nearby initial points.
* `ContDiffAt.exists_eq_isIntegralCurveAt`: a `C¹` vector field admits a local integral curve.
* `ContDiffAt.exists_eventually_isIntegralCurveAt`: a `C¹` vector field admits a local flow.

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Existence of solutions to ODEs -/

namespace IsPicardLindelof

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution whose initial point `x` may be different from the centre `x₀` of
the closed ball within which the properties of the vector field hold. -/
theorem exists_eq_isIntegralCurveOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ IsIntegralCurveOn α f (Icc tmin tmax) := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_isIntegralCurveOn₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Icc tmin tmax) :=
  exists_eq_isIntegralCurveOn hf (mem_closedBall_self le_rfl)

open Classical in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the initial point. -/
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      IsIntegralCurveOn (α x) f (Icc tmin tmax)) ∧
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
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn_continuousOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      IsIntegralCurveOn (α ⟨x, ·⟩) f (Icc tmin tmax)) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx ↦ (hα1 x hx).2.continuousOn

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow. -/
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      IsIntegralCurveOn (α x) f (Icc tmin tmax) :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith hf
  ⟨α, hα.1⟩

@[deprecated (since := "2026-02-08")]
alias exists_eq_forall_mem_Icc_hasDerivWithinAt := exists_eq_isIntegralCurveOn

@[deprecated (since := "2026-02-08")]
alias exists_eq_forall_mem_Icc_hasDerivWithinAt₀ := exists_eq_isIntegralCurveOn₀

@[deprecated (since := "2026-02-08")]
alias exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith :=
  exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith

@[deprecated (since := "2026-02-08")]
alias exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn :=
  exists_forall_mem_closedBall_eq_isIntegralCurveOn_continuousOn

@[deprecated (since := "2026-02-08")]
alias exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt :=
  exists_forall_mem_closedBall_eq_isIntegralCurveOn

end IsPicardLindelof

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      IsIntegralCurveOn α (fun _ ↦ f) (Ioo (t₀ - ε) (t₀ + ε)) := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf t₀
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := hpl.exists_eq_isIntegralCurveOn hx
  exact ⟨α, hα1, hα2.mono Ioo_subset_Icc_self⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_isIntegralCurveAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveAt α (fun _ ↦ f) t₀ := by
  have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  exact ⟨α, hα1, hα2.isIntegralCurveAt (Ioo_mem_nhds (by linarith) (by linarith))⟩

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_eventually_isIntegralCurveAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : E → ℝ → E, ∀ᶠ x in 𝓝 x₀,
      α x t₀ = x ∧ IsIntegralCurveAt (α x) (fun _ ↦ f) t₀ := by
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn hf t₀
  choose α hα using H
  refine ⟨fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then α x hx else 0, ?_⟩
  filter_upwards [closedBall_mem_nhds x₀ hr] with x hx
  simp only [dif_pos hx]
  exact ⟨(hα x hx).1,
    (hα x hx).2.isIntegralCurveAt (Ioo_mem_nhds (by linarith) (by linarith))⟩

@[deprecated (since := "2026-02-08")]
alias exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt :=
  exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn

@[deprecated (since := "2026-02-08")]
alias exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ :=
  exists_eq_isIntegralCurveAt

@[deprecated (since := "2026-02-08")]
alias exists_eventually_eq_hasDerivAt := exists_eventually_isIntegralCurveAt

end ContDiffAt

/-! ## Uniqueness of solutions to ODEs -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g : ℝ → E} {a b t₀ : ℝ}

/-- There exists only one solution of an ODE $\dot x=v(t, x)$ in a set `s ⊆ ℝ × E` with
a given initial value provided that the RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`.

This version shows uniqueness in a closed interval `Icc a b`, where `a` is the initial time. -/
theorem IsIntegralCurveOn.eqOn_Icc_right
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b)) (hf' : IsIntegralCurveOn f v (Ico a b))
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : IsIntegralCurveOn g v (Ico a b))
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : f a = g a) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem hv hf
    (fun t ht ↦ (hf' t ht).mono_of_mem_nhdsWithin (Ico_mem_nhdsGE_of_mem ht)) hfs hg
    (fun t ht ↦ (hg' t ht).mono_of_mem_nhdsWithin (Ico_mem_nhdsGE_of_mem ht)) hgs
    (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

/-- A time-reversed version of `IsIntegralCurveOn.eqOn_Icc_right`. Uniqueness is shown in a
closed interval `Icc a b`, where `b` is the "initial" time. -/
theorem IsIntegralCurveOn.eqOn_Icc_left
    (hv : ∀ t ∈ Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b)) (hf' : IsIntegralCurveOn f v (Ioc a b))
    (hfs : ∀ t ∈ Ioc a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : IsIntegralCurveOn g v (Ioc a b))
    (hgs : ∀ t ∈ Ioc a b, g t ∈ s t) (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  have hv' : ∀ t ∈ Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t ∈ Ioc a b := by
      push _ ∈ _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht ↦ ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht ↦ ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  suffices EqOn (f ∘ Neg.neg) (g ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at this
    convert this
    simp
  apply IsIntegralCurveOn.eqOn_Icc_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hgs _ (hmt2 ht)) (by simp [hb])
  · intro t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt hmt2
    simp
  · intro t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt hmt2
    simp

/-- A version of `IsIntegralCurveOn.eqOn_Icc_right` for uniqueness in a closed interval whose
interior contains the initial time. -/
theorem IsIntegralCurveOn.eqOn_Icc
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t)) (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : IsIntegralCurveOn f v (Ioo a b))
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : IsIntegralCurveOn g v (Ioo a b))
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t) (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ ⊆ Ioo a b := Ioc_subset_Ioo_right ht.2
    exact IsIntegralCurveOn.eqOn_Icc_left (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (hf'.mono hss) (fun _ ht' ↦ hfs _ (hss ht'))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (hg'.mono hss) (fun _ ht' ↦ hgs _ (hss ht')) heq
  · have hss : Ico t₀ b ⊆ Ioo a b := Ico_subset_Ioo_left ht.1
    exact IsIntegralCurveOn.eqOn_Icc_right (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (hf'.mono hss) (fun _ ht' ↦ hfs _ (hss ht'))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (hg'.mono hss) (fun _ ht' ↦ hgs _ (hss ht')) heq

/-- A version of `IsIntegralCurveOn.eqOn_Icc` for uniqueness in an open interval. -/
theorem IsIntegralCurveOn.eqOn_Ioo
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t)) (ht : t₀ ∈ Ioo a b)
    (hf : IsIntegralCurveOn f v (Ioo a b)) (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : IsIntegralCurveOn g v (Ioo a b)) (hgs : ∀ t ∈ Ioo a b, g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact IsIntegralCurveOn.eqOn_Icc_left
      (fun t'' ht'' ↦ hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      (hf.continuousOn.mono hss)
      (hf.mono (Ioc_subset_Icc_self.trans hss))
      (fun _ ht'' ↦ hfs _ (hss (Ioc_subset_Icc_self ht'')))
      (hg.continuousOn.mono hss)
      (hg.mono (Ioc_subset_Icc_self.trans hss))
      (fun _ ht'' ↦ hgs _ (hss (Ioc_subset_Icc_self ht''))) heq
      ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t' ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht.1 ht''.1, lt_of_le_of_lt ht''.2 ht'.2⟩
    exact IsIntegralCurveOn.eqOn_Icc_right
      (fun t'' ht'' ↦ hv t'' ((Ico_subset_Icc_self.trans hss) ht''))
      (hf.continuousOn.mono hss)
      (hf.mono (Ico_subset_Icc_self.trans hss))
      (fun _ ht'' ↦ hfs _ (hss (Ico_subset_Icc_self ht'')))
      (hg.continuousOn.mono hss)
      (hg.mono (Ico_subset_Icc_self.trans hss))
      (fun _ ht'' ↦ hgs _ (hss (Ico_subset_Icc_self ht''))) heq
      ⟨h, le_rfl⟩

/-- Local uniqueness of ODE solutions. -/
theorem IsIntegralCurveAt.eventuallyEq
    (hv : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t))
    (hf : IsIntegralCurveAt f v t₀) (hfs : ∀ᶠ t in 𝓝 t₀, f t ∈ s t)
    (hg : IsIntegralCurveAt g v t₀) (hgs : ∀ᶠ t in 𝓝 t₀, g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and ((hf.and hfs).and (hg.and hgs)))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  exact IsIntegralCurveOn.eqOn_Ioo (fun _ ht ↦ (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_self hε)
    (fun _ ht ↦ (h _ ht).2.1.1.hasDerivWithinAt) (fun _ ht ↦ (h _ ht).2.1.2)
    (fun _ ht ↦ (h _ ht).2.2.1.hasDerivWithinAt) (fun _ ht ↦ (h _ ht).2.2.2) heq

/-- There exists only one global solution to an ODE $\dot x=v(t, x)$ with a given initial value
provided that the RHS is Lipschitz continuous. -/
theorem IsIntegralCurve.eq
    (hv : ∀ t, LipschitzOnWith K (v t) (s t))
    (hf : IsIntegralCurve f v) (hfs : ∀ t, f t ∈ s t)
    (hg : IsIntegralCurve g v) (hgs : ∀ t, g t ∈ s t)
    (heq : f t₀ = g t₀) : f = g := by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : ∃ A B, t ∈ Set.Ioo A B ∧ t₀ ∈ Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    rw [Set.mem_Ioo, Set.mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact sub_one_lt _ |>.trans_le <| min_le_left _ _ |>.trans <| neg_abs_le t
    · exact le_abs_self _ |>.trans_lt <| le_max_left _ _ |>.trans_lt <| lt_add_one _
    · exact sub_one_lt _ |>.trans_le <| min_le_right _ _ |>.trans <| neg_abs_le t₀
    · exact le_abs_self _ |>.trans_lt <| le_max_right _ _ |>.trans_lt <| lt_add_one _
  exact IsIntegralCurveOn.eqOn_Ioo
    (fun t _ => hv t) Ht₀ (hf.isIntegralCurveOn _) (fun t _ => hfs t)
    (hg.isIntegralCurveOn _) (fun t _ => hgs t) heq Ht

/-- If two integral curves of a Lipschitz vector field on connected sets `I` and `J` agree at a
point `t₀ ∈ I ∩ J`, then they agree on all of `I ∩ J`. -/
theorem IsIntegralCurveOn.eqOn_inter {I J : Set ℝ}
    (hv : ∀ t ∈ I ∩ J, LipschitzOnWith K (v t) (s t))
    (hI : IsPreconnected I) (hJ : IsPreconnected J) (htI : t₀ ∈ I) (htJ : t₀ ∈ J)
    (hf : IsIntegralCurveOn f v I) (hfs : ∀ t ∈ I ∩ J, f t ∈ s t)
    (hg : IsIntegralCurveOn g v J) (hgs : ∀ t ∈ I ∩ J, g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (I ∩ J) := by
  have hoc := hI.ordConnected.inter hJ.ordConnected
  intro t ⟨htI', htJ'⟩
  rcases lt_or_ge t t₀ with h | h
  · have hss : Icc t t₀ ⊆ I ∩ J := hoc.out ⟨htI', htJ'⟩ ⟨htI, htJ⟩
    exact eqOn_Icc_left
      (fun t' ht' ↦ hv t' (hss (Ioc_subset_Icc_self ht')))
      (hf.continuousOn.mono (hss.trans inter_subset_left))
      (hf.mono ((Ioc_subset_Icc_self.trans hss).trans inter_subset_left))
      (fun t' ht' ↦ hfs t' (hss (Ioc_subset_Icc_self ht')))
      (hg.continuousOn.mono (hss.trans inter_subset_right))
      (hg.mono ((Ioc_subset_Icc_self.trans hss).trans inter_subset_right))
      (fun t' ht' ↦ hgs t' (hss (Ioc_subset_Icc_self ht')))
      heq ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t ⊆ I ∩ J := hoc.out ⟨htI, htJ⟩ ⟨htI', htJ'⟩
    exact eqOn_Icc_right
      (fun t' ht' ↦ hv t' (hss (Ico_subset_Icc_self ht')))
      (hf.continuousOn.mono (hss.trans inter_subset_left))
      (hf.mono ((Ico_subset_Icc_self.trans hss).trans inter_subset_left))
      (fun t' ht' ↦ hfs t' (hss (Ico_subset_Icc_self ht')))
      (hg.continuousOn.mono (hss.trans inter_subset_right))
      (hg.mono ((Ico_subset_Icc_self.trans hss).trans inter_subset_right))
      (fun t' ht' ↦ hgs t' (hss (Ico_subset_Icc_self ht')))
      heq ⟨h, le_rfl⟩

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_of_mem_Icc_right := IsIntegralCurveOn.eqOn_Icc_right

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_of_mem_Icc_left := IsIntegralCurveOn.eqOn_Icc_left

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_of_mem_Icc := IsIntegralCurveOn.eqOn_Icc

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_of_mem_Ioo := IsIntegralCurveOn.eqOn_Ioo

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_of_eventually := IsIntegralCurveAt.eventuallyEq

@[deprecated (since := "2026-02-08")]
alias ODE_solution_unique_univ := IsIntegralCurve.eq
