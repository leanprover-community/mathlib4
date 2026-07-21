/-
Copyright (c) 2026 Julian Rolfes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Rolfes, Luke Schleef, Philipp Svinger, Paul Niessner, Florian Grube
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Peano Existence Theorem

This file proves Peano's existence theorem for a continuous time-dependent vector field on a
finite-dimensional real normed vector space. The assumptions are collected in `IsPeano`.

The proof constructs Tonelli approximations with a delayed input, extracts a uniformly
convergent subsequence using the Arzelà–Ascoli theorem, and passes to the limit in the associated
integral equation.

## Main definitions

- `IsPeano`: the hypotheses on the vector field and its cylinder of definition.
- `IsPeano.stepSize`: the time-step size of a Tonelli approximation.
- `IsPeano.delayedInput`: the delayed time argument used in the Tonelli approximations.
- `IsPeano.tonelliIterate`: the recursively defined curves used in the construction.
- `IsPeano.tonelliApproximation`: the diagonal sequence of Tonelli approximations.
- `IsPeano.boundedTonelliApproximation`: the approximations as bounded continuous functions.

## Main statements

- `IsPeano.exists_eq_forall_mem_Icc_eq_integral`: existence of a solution to the integral equation.
- `IsPeano.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`: Peano's existence theorem in differential
  form.

## Implementation notes

The proof first constructs the solution to the right of the initial time. The solution to the left
is obtained by reversing time, and the two solutions are then glued at the initial point.

The finite-dimensionality assumption is used to apply the Arzelà–Ascoli theorem.

## Tags

differential equation, initial value problem, Peano existence theorem, Tonelli approximation
-/

@[expose] public section

open Metric Set
open scoped NNReal

/-! ### Assumptions of Peano's existence theorem -/

/-- The hypotheses for Peano's existence theorem on a closed time interval and a closed ball. -/
structure IsPeano {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (r L : ℝ≥0) : Prop where
  /-- The vector field is continuous on the set product of a time interval and a closed ball. -/
  continuousOn : ContinuousOn f (Icc tmin tmax ×ˢ closedBall x₀ r)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r, ‖f (t, x)‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ r

namespace IsPeano

open Filter
open scoped BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ × E → E} {α : ℝ → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {r L : ℝ≥0}

lemma mul_abs_sub_le_radius {t : ℝ} (hf : IsPeano f t₀ x₀ r L)
    (ht : t ∈ Icc t₀.val tmax) : L * |t - t₀| ≤ r := by
  have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg (sub_nonneg.mpr ht.1)
  have h_diff : t - t₀ ≤ max (tmax - t₀) (t₀ - tmin) := by
    calc
      t - t₀ ≤ tmax - t₀ := sub_le_sub_right ht.2 t₀
      tmax - t₀ ≤ max (tmax - t₀) (t₀ - tmin) := le_max_left (tmax - t₀) (t₀ - tmin)
  calc
    L * |t - t₀| = L * (t - t₀) := by rw [h_abs]
    L * (t - t₀) ≤ L * max (tmax - t₀) (t₀ - tmin) := by
      apply mul_le_mul_of_nonneg_left h_diff
      positivity
    L * max (tmax - t₀) (t₀ - tmin) ≤ r := hf.mul_max_le

variable [NormedSpace ℝ E]

/-! ### Tonelli approximations -/

section TonelliApproximation

/-- The time-step size of the `n`th Tonelli approximation. -/
noncomputable def stepSize (t₀ : Icc tmin tmax) (n : ℕ) : ℝ := (tmax - t₀) / n

/-- The time-step size of every Tonelli approximation is nonnegative. -/
lemma stepSize_nonneg (t₀ : Icc tmin tmax) (n : ℕ) : 0 ≤ stepSize t₀ n := by
  rcases t₀ with ⟨t₀, ht₀⟩
  rcases mem_Icc.mp ht₀ with ⟨_, ht₀_right⟩
  rw [stepSize]
  apply div_nonneg
  · simp only [sub_nonneg]
    exact ht₀_right
  · simp only [Nat.cast_nonneg]

lemma add_mul_stepSize_eq_tmax (t₀ : Icc tmin tmax) (n : ℕ) :
    t₀.val + ((n : ℝ) + 1) * stepSize t₀ (n + 1) = tmax := by
  rw [stepSize]
  field_simp
  push_cast
  ring

/-- The delayed time input used in the Tonelli approximations. -/
noncomputable def delayedInput (t₀ : Icc tmin tmax) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ max (t - stepSize t₀ n) t₀

/-- Before the first time step, the delayed input is the initial time `t₀`. -/
lemma delayedInput_eq_t₀_of_le {t : ℝ} (t₀ : Icc tmin tmax) (n : ℕ)
    (ht : t ≤ t₀ + stepSize t₀ n) :
    delayedInput t₀ n t = t₀ := by
  unfold delayedInput
  exact max_eq_right ((sub_le_iff_le_add).2 ht)

/-- After the first time step, the delayed input is one time step behind `t`. -/
lemma delayedInput_eq_sub_of_le {t : ℝ} (t₀ : Icc tmin tmax) (n : ℕ)
    (ht : t₀ + stepSize t₀ n ≤ t) :
    delayedInput t₀ n t = t - stepSize t₀ n := by
  unfold delayedInput
  exact max_eq_left ((le_sub_iff_add_le).2 ht)

/-- The delayed input maps the first `k + 1` time steps into the first `k` time steps. -/
lemma mapsTo_delayedInput_previous_interval (n k : ℕ) (t₀ : Icc tmin tmax) :
    MapsTo (delayedInput t₀ n)
      (Icc t₀.val (t₀ + (k + 1 : ℝ) * stepSize t₀ n))
      (Icc t₀.val (t₀ + (k : ℝ) * stepSize t₀ n)) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have h_stepSize_nonneg : 0 ≤ stepSize t₀ n :=
    div_nonneg (sub_nonneg.mpr t₀.2.2) (Nat.cast_nonneg n)
  have h_mul_nonneg : 0 ≤ (k : ℝ) * stepSize t₀ n :=
    mul_nonneg (Nat.cast_nonneg k) h_stepSize_nonneg
  unfold delayedInput
  constructor
  · exact le_max_right _ _
  · apply max_le <;> linarith

/-- The delayed input maps `Icc t₀ tmax` to itself. -/
lemma mapsTo_delayedInput (t₀ : Icc tmin tmax) (n : ℕ) :
    MapsTo (delayedInput t₀ n) (Icc t₀.val tmax) (Icc t₀.val tmax) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have h_stepSize_nonneg : 0 ≤ stepSize t₀ n :=
    div_nonneg (sub_nonneg.mpr t₀.2.2) (Nat.cast_nonneg n)
  have h_t₀_le_tmax : t₀.val ≤ tmax := t₀.2.2
  unfold delayedInput
  constructor
  · exact le_max_right _ _
  · apply max_le <;> linarith

/-- The delayed input is Lipschitz continuous with constant one. -/
lemma lipschitzWith_delayedInput (t₀ : Icc tmin tmax) (n : ℕ) :
    LipschitzWith 1 (delayedInput t₀ n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  intro x y
  have h_dist :=
    abs_max_sub_max_le_abs (x - stepSize t₀ n) (y - stepSize t₀ n) t₀.val
  simp at h_dist
  tauto

/-- The recursively defined curves used to build the Tonelli approximations. -/
noncomputable def tonelliIterate (f : ℝ × E → E) (t₀ : Icc tmin tmax) (x₀ : E) (n : ℕ) :
    ℕ → ℝ → E
  | 0 => fun _ ↦ x₀
  | k + 1 =>
      fun t ↦ x₀ + ∫ s in t₀..t,
        f (s, tonelliIterate f t₀ x₀ n k (delayedInput t₀ n s))

/-- Every recursively defined curve takes the value `x₀` at `t₀`. -/
lemma tonelliIterate_apply_t₀ (f : ℝ × E → E) (t₀ : Icc tmin tmax) (x₀ : E) (n : ℕ) (k : ℕ) :
    tonelliIterate f t₀ x₀ n k t₀ = x₀ := by
  induction k with
  | zero => simp [tonelliIterate]
  | succ => simp [tonelliIterate]

/-- Every recursively defined curve stays in the cylinder and has Lipschitz constant `L`. -/
private lemma tonelliIterate_bounds (hf : IsPeano f t₀ x₀ r L) (n k : ℕ) :
    MapsTo (tonelliIterate f t₀ x₀ n k) (Icc t₀.val tmax) (closedBall x₀ r) ∧
    LipschitzOnWith L (tonelliIterate f t₀ x₀ n k) (Icc t₀.val tmax) := by
  induction k with
  | zero =>
    exact
      ⟨fun _ _ ↦ by simp [tonelliIterate, mem_closedBall],
        (LipschitzWith.const x₀).weaken L.2 |>.lipschitzOnWith⟩
  | succ k hk =>
    have h_map : MapsTo
        (fun s ↦ tonelliIterate f t₀ x₀ n k (delayedInput t₀ n s))
        (Icc t₀ tmax) (closedBall x₀ r) :=
      hk.1.comp (mapsTo_delayedInput t₀ n)
    have h_cont :
        ContinuousOn
          (fun s ↦ f (s, tonelliIterate f t₀ x₀ n k (delayedInput t₀ n s)))
          (uIcc t₀.val tmax) := by
      rw [uIcc_of_le t₀.2.2]
      exact hf.continuousOn.comp
        (ContinuousOn.prodMk continuousOn_id
          (ContinuousOn.comp hk.2.continuousOn
            (lipschitzWith_delayedInput t₀ n).continuous.continuousOn
            (mapsTo_delayedInput t₀ n)))
        (fun t ht ↦ ⟨⟨t₀.2.1.trans ht.1, ht.2⟩, h_map ht⟩)
    have h_int :
        IntervalIntegrable
          (fun s ↦ f (s, tonelliIterate f t₀ x₀ n k (delayedInput t₀ n s)))
          MeasureTheory.volume t₀ tmax :=
      ContinuousOn.intervalIntegrable h_cont
    have h_lip : LipschitzOnWith L (tonelliIterate f t₀ x₀ n (k + 1)) (Icc (↑t₀) tmax) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha b hb
      rw [Real.dist_eq, dist_eq_norm, tonelliIterate, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left]
      · refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
        have ht' := uIoc_subset_uIcc.trans (uIcc_subset_Icc hb ha) ht
        exact hf.norm_le t ⟨t₀.2.1.trans ht'.1, ht'.2⟩ _ (h_map ht')
      · exact h_int.mono_set (uIcc_subset_uIcc left_mem_uIcc <| Icc_subset_uIcc ha)
      · exact h_int.mono_set (uIcc_subset_uIcc left_mem_uIcc <| Icc_subset_uIcc hb)
    refine ⟨fun t ht ↦ ?_, h_lip⟩
    rw [mem_closedBall]
    nth_rewrite 2 [← tonelliIterate_apply_t₀ f t₀ x₀ n (k + 1)]
    refine (h_lip.dist_le_mul t ht t₀ <| left_mem_Icc.mpr t₀.2.2).trans ?_
    rw [Real.dist_eq]
    exact mul_abs_sub_le_radius hf ht

/-- Every recursively defined curve stays in the cylinder. -/
lemma mapsTo_tonelliIterate_closedBall (hf : IsPeano f t₀ x₀ r L) (n : ℕ) (k : ℕ) :
    MapsTo (tonelliIterate f t₀ x₀ n k) (Icc t₀.val tmax) (closedBall x₀ r) :=
  tonelliIterate_bounds hf n k |>.1

/-- Every recursively defined curve is Lipschitz continuous with constant `L`. -/
lemma lipschitzOnWith_tonelliIterate (hf : IsPeano f t₀ x₀ r L) (n : ℕ) (k : ℕ) :
    LipschitzOnWith L (tonelliIterate f t₀ x₀ n k) (Icc t₀.val tmax) :=
  tonelliIterate_bounds hf n k |>.2

/-- Consecutive recursive curves agree on the first `k` time steps. -/
lemma tonelliIterate_eq_succ_on_Icc (n : ℕ) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc t₀.val (t₀.val + k * stepSize t₀ n)) :
    tonelliIterate f t₀ x₀ n k t = tonelliIterate f t₀ x₀ n (k + 1) t := by
  induction k generalizing t with
  | zero =>
    obtain rfl : t = (t₀ : ℝ) := by
      simp only [Nat.cast_zero, zero_mul, add_zero] at ht
      exact le_antisymm ht.2 ht.1
    unfold tonelliIterate
    simp
  | succ k ih =>
    push_cast at ht
    unfold tonelliIterate
    simp only [add_right_inj]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs_min : (t₀ : ℝ) ≤ s := min_eq_left ht.1 ▸ hs.1
    have hs_max : s ≤ t := max_eq_right ht.1 ▸ hs.2
    have hs_in_Icc : s ∈ Icc (t₀ : ℝ) ((t₀ : ℝ) + (k + 1 : ℝ) * stepSize t₀ n) :=
      ⟨hs_min, le_trans hs_max ht.2⟩
    simp only [
      ih (delayedInput t₀ n s)
        (mapsTo_delayedInput_previous_interval n k t₀ hs_in_Icc)]

/-- The diagonal sequence of Tonelli approximations. -/
noncomputable def tonelliApproximation
    (f : ℝ × E → E) (t₀ : Icc tmin tmax) (x₀ : E) (n : ℕ) : ℝ → E :=
  fun t ↦ tonelliIterate f t₀ x₀ (n + 1) (n + 1) t

/-- Every diagonal Tonelli approximation stays in the cylinder. -/
lemma mapsTo_tonelliApproximation_closedBall (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    MapsTo (tonelliApproximation f t₀ x₀ n) (Icc t₀.val tmax) (closedBall x₀ r) :=
  mapsTo_tonelliIterate_closedBall hf (n + 1) (n + 1)

/-- Every diagonal Tonelli approximation is Lipschitz continuous with constant `L`. -/
lemma lipschitzOnWith_tonelliApproximation (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    LipschitzOnWith L (tonelliApproximation f t₀ x₀ n) (Icc t₀.val tmax) :=
  lipschitzOnWith_tonelliIterate hf (n + 1) (n + 1)

/-- Every diagonal Tonelli approximation satisfies the integral equation with delayed input. -/
lemma tonelliApproximation_eq_integral (n : ℕ) (t : ℝ) (ht : t ∈ Icc t₀.val tmax) :
    tonelliApproximation f t₀ x₀ n t =
      x₀ + ∫ s in t₀..t,
        f (s, tonelliApproximation f t₀ x₀ n (delayedInput t₀ (n + 1) s)) := by
  have h_succ : ∀ t ∈ Icc t₀.val tmax, tonelliApproximation f t₀ x₀ n t =
      tonelliIterate f t₀ x₀ (n + 1) (n + 2) t := by
    intro t ht
    apply tonelliIterate_eq_succ_on_Icc (n + 1) (n + 1)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul_stepSize_eq_tmax] using ht
  simp_rw [h_succ t ht, tonelliApproximation, tonelliIterate]

end TonelliApproximation

/-! ### Compactness via the Arzelà–Ascoli theorem -/

section ArzelaAscoli

/-- Restrict a curve on `ℝ` to the interval `Icc t₀ tmax`. -/
def restrictToIcc (α : ℝ → E) : Icc t₀.val tmax → E :=
  fun t ↦ α t

/-- Package a continuous function on `Icc t₀ tmax` as a continuous map. -/
def continuousMapOnIcc (α : Icc t₀.val tmax → E) (hα : Continuous α) :
    C(Icc t₀.val tmax, E) where
  toFun := α
  continuous_toFun := hα

/-- Package a continuous map on the compact interval `Icc t₀ tmax` as a bounded continuous map. -/
def boundedContinuousFunctionOnIcc (α : C(Icc t₀.val tmax, E)) :
    Icc t₀.val tmax →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact α

/-- The Tonelli approximations as bounded continuous functions on `Icc t₀ tmax`. -/
noncomputable def boundedTonelliApproximation
    (hf : IsPeano f t₀ x₀ r L) (n : ℕ) : Icc t₀.val tmax →ᵇ E :=
  boundedContinuousFunctionOnIcc
    (continuousMapOnIcc (restrictToIcc (tonelliApproximation f t₀ x₀ n))
      (continuousOn_iff_continuous_domRestrict.mp
        (lipschitzOnWith_tonelliApproximation hf n).continuousOn))

/-- The bounded continuous form of each Tonelli approximation has Lipschitz constant `L`. -/
lemma lipschitzWith_boundedTonelliApproximation (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    LipschitzWith L (boundedTonelliApproximation hf n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro t s
  rw [boundedTonelliApproximation]
  exact (lipschitzOnWith_tonelliApproximation hf n).dist_le_mul t.val t.property s.val s.property

/-- The family of bounded continuous Tonelli approximations is equicontinuous. -/
lemma equicontinuous_boundedTonelliApproximation (hf : IsPeano f t₀ x₀ r L) :
    Equicontinuous (fun n ↦ (boundedTonelliApproximation hf n).toFun) := by
  have : UniformEquicontinuous (fun n ↦ (boundedTonelliApproximation hf n).toFun) :=
    LipschitzWith.uniformEquicontinuous (fun n ↦ (boundedTonelliApproximation hf n).toFun) L
      (lipschitzWith_boundedTonelliApproximation hf)
  apply UniformEquicontinuous.equicontinuous this

variable [FiniteDimensional ℝ E]

/-- The closure of the family of the Tonelli approximations is compact. -/
lemma isCompact_closure_range_boundedTonelliApproximation (hf : IsPeano f t₀ x₀ r L) :
    IsCompact (closure (range (boundedTonelliApproximation hf))) := by
  apply BoundedContinuousFunction.arzela_ascoli (closedBall x₀ r) _ _ _ _
  · apply isCompact_closedBall
  · intro g x hg
    simp only [mem_range] at hg
    obtain ⟨n, rfl⟩ := hg
    unfold boundedTonelliApproximation boundedContinuousFunctionOnIcc continuousMapOnIcc
      restrictToIcc
    simp only [BoundedContinuousFunction.mkOfCompact_apply]
    apply mapsTo_tonelliApproximation_closedBall hf n x.property
  · intro x U hU
    apply (equicontinuous_boundedTonelliApproximation hf x U hU).mono
    simp

/-- The Tonelli approximations admit a convergent subsequence of bounded continuous functions. -/
lemma exists_tendsto_subseq_boundedTonelliApproximation (hf : IsPeano f t₀ x₀ r L) :
    ∃ β : Icc t₀.val tmax →ᵇ E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (boundedTonelliApproximation hf ∘ φ) atTop (nhds β) := by
  let s : Set (Icc t₀.val tmax →ᵇ E) := closure (range (boundedTonelliApproximation hf))
  have h_s_compact : IsCompact s := by
    simpa [s] using isCompact_closure_range_boundedTonelliApproximation hf
  have h_mem : ∀ n, boundedTonelliApproximation hf n ∈
      closure (range (boundedTonelliApproximation hf)) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  obtain ⟨β, _, φ, hφ_mono, hφ_tendsto⟩ := h_s_compact.tendsto_subseq h_mem
  exact ⟨β, φ, hφ_mono, hφ_tendsto⟩

end ArzelaAscoli

/-! ### Extraction and convergence of a subsequence -/

section LimitExtraction

variable [FiniteDimensional ℝ E]

/-- A subsequence of Tonelli approximations converges uniformly to a continuous curve. -/
lemma exists_tendstoUniformlyOn_subseq_tonelliApproximation (hf : IsPeano f t₀ x₀ r L) :
    ∃ α : ℝ → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContinuousOn α (Icc t₀ tmax) ∧
      MapsTo α (Icc t₀ tmax) (closedBall x₀ r) ∧
        TendstoUniformlyOn (tonelliApproximation f t₀ x₀ ∘ φ) α atTop (Icc t₀.val tmax) := by
  obtain ⟨β, φ, hφ_mono, hβ_tendsto⟩ := exists_tendsto_subseq_boundedTonelliApproximation hf
  let α : ℝ → E := fun t ↦ if h : t ∈ Icc t₀.val tmax then β ⟨t, h⟩ else 0
  refine ⟨α, φ, hφ_mono, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have h_restrict : (Set.Icc t₀.val tmax).domRestrict α = β := by
      ext x
      simp only [α, Set.domRestrict]
      exact dif_pos x.prop
    rw [h_restrict]
    exact β.continuous
  · intro t ht
    have hα_apply : α t = β ⟨t, ht⟩ := by
      simp only [α]
      exact dif_pos ht
    rw [hα_apply]
    let t' : Icc t₀.val tmax := ⟨t, ht⟩
    have h_uniform : TendstoUniformly (fun n ↦ boundedTonelliApproximation hf (φ n)) β atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hβ_tendsto
    have h_pointwise :
        Tendsto (fun n ↦ boundedTonelliApproximation hf (φ n) t') atTop (nhds (β t')) :=
      h_uniform.tendsto_at t'
    apply isClosed_closedBall.mem_of_tendsto h_pointwise
    apply Eventually.of_forall
    intro n
    change tonelliApproximation f t₀ x₀ (φ n) t ∈ closedBall x₀ r
    exact mapsTo_tonelliApproximation_closedBall hf (φ n) ht
  · have h_uniform : TendstoUniformly (fun n ↦ boundedTonelliApproximation hf (φ n)) β atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hβ_tendsto
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hα_comp : α ∘ Subtype.val = ⇑β := by
      ext t
      simp only [Function.comp_apply, α]
      exact dif_pos t.prop
    rw [hα_comp]
    change TendstoUniformly
      (fun n (t : Icc t₀.val tmax) ↦ boundedTonelliApproximation hf (φ n) t) ⇑β atTop
    exact h_uniform

variable {φ : ℕ → ℕ}

/-- The time-step sizes of the Tonelli approximations tend to zero. -/
lemma tendsto_stepSize_zero : Tendsto (stepSize t₀) atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat (tmax - t₀)

/-- The delayed input converges to the identity. -/
lemma tendsto_delayedInput_id (t : ℝ) (ht : t ∈ Icc t₀.val tmax) :
    Tendsto (fun n ↦ delayedInput t₀ n t) atTop (nhds t) := by
  have h_tendsto : Tendsto (fun n ↦ max (t - stepSize t₀ n) t₀.val) atTop
      (nhds (max (t - 0) t₀.val)) :=
    Tendsto.max (Tendsto.sub tendsto_const_nhds tendsto_stepSize_zero) tendsto_const_nhds
  simp only [sub_zero, max_eq_left ht.1] at h_tendsto
  exact h_tendsto

omit [FiniteDimensional ℝ E]

/-- Uniform convergence of Tonelli approximations implies pointwise convergence after composition
with the corresponding delayed inputs. -/
lemma tendsto_tonelliApproximation_delayedInput_of_tendstoUniformlyOn_tonelliApproximation
    (hφ : StrictMono φ)
    (hα : ContinuousOn α (Icc t₀.val tmax))
    (h_tendsto : TendstoUniformlyOn (tonelliApproximation f t₀ x₀ ∘ φ) α atTop
      (Icc t₀.val tmax))
    (t : ℝ) (ht : t ∈ Icc t₀.val tmax) :
    Tendsto
      (fun n ↦
        tonelliApproximation f t₀ x₀ (φ n) (delayedInput t₀ (φ n + 1) t))
      atTop (nhds (α t)) := by
  refine h_tendsto.tendsto_comp (hα t ht) (tendsto_nhdsWithin_iff.mpr ?_)
  exact
    ⟨(tendsto_delayedInput_id t ht).comp <| (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop,
      Eventually.of_forall (fun _ ↦ mapsTo_delayedInput _ _ ht)⟩

end LimitExtraction

/-! ### Passage to the limit -/

/-- Every composition of a Tonelli approximation with its delayed input is continuous. -/
lemma continuousOn_tonelliApproximation_delayedInput (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    ContinuousOn
      (fun t ↦ tonelliApproximation f t₀ x₀ n (delayedInput t₀ (n + 1) t))
      (Icc t₀ tmax) :=
  (lipschitzOnWith_tonelliApproximation hf n).continuousOn.comp
    (lipschitzWith_delayedInput t₀ _).continuous.continuousOn (mapsTo_delayedInput t₀ _)

/-- Every Tonelli approximation composed with its delayed input stays in the cylinder. -/
lemma mapsTo_tonelliApproximation_delayedInput (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    MapsTo
      (fun t ↦ tonelliApproximation f t₀ x₀ n (delayedInput t₀ (n + 1) t))
      (Icc t₀ tmax) (closedBall x₀ r) :=
  (mapsTo_tonelliApproximation_closedBall hf n).comp (mapsTo_delayedInput t₀ _)

/-- Every composition of the vector field `f` with a delayed Tonelli approximation is continuous. -/
lemma continuousOn_comp_tonelliApproximation_delayedInput
    (hf : IsPeano f t₀ x₀ r L) (n : ℕ) :
    ContinuousOn
      (fun t ↦ f (t, tonelliApproximation f t₀ x₀ n (delayedInput t₀ (n + 1) t)))
      (Icc t₀ tmax) := by
  apply hf.continuousOn.comp
    (ContinuousOn.prodMk continuousOn_id (continuousOn_tonelliApproximation_delayedInput hf n))
  intro s hs
  exact
    ⟨mem_Icc.mp ⟨t₀.2.1.trans hs.1, hs.2⟩,
      mapsTo_tonelliApproximation_delayedInput hf n hs⟩

lemma mem_Icc_of_mem_uIoc {s t : ℝ} (ht : t ∈ Icc t₀.val tmax)
    (hs : s ∈ uIoc t₀.val t) : s ∈ Icc t₀.val tmax :=
  Icc_subset_Icc_right ht.2 (Ioc_subset_Icc_self (uIoc_of_le ht.1 ▸ hs))

variable [FiniteDimensional ℝ E]

/-! ### Existence of integral and differential solutions -/

/-- There exists a solution of the integral equation on the interval forward in time. -/
lemma exists_eq_forall_mem_Icc_eq_integral_forward (hf : IsPeano f t₀ x₀ r L) :
    ∃ α : ℝ → E, ContinuousOn α (Icc t₀ tmax) ∧ MapsTo α (Icc t₀ tmax) (closedBall x₀ r) ∧
      ∀ t ∈ Icc t₀.val tmax, α t = x₀ + ∫ s in t₀..t, f (s, α s) := by
  obtain ⟨α, φ, hφ_mono, hα_cont, hα_maps, hα_tendsto⟩ :=
    exists_tendstoUniformlyOn_subseq_tonelliApproximation hf
  refine ⟨α, hα_cont, hα_maps, fun t ht ↦ tendsto_nhds_unique
    (hα_tendsto.tendsto_at ht)
    ((Tendsto.const_add x₀ ?_).congr (fun n ↦ (tonelliApproximation_eq_integral (φ n) t ht).symm))⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ ↦ L)
    _ _ intervalIntegrable_const _
  · apply Eventually.of_forall
    intro n
    have h_cont := continuousOn_comp_tonelliApproximation_delayedInput hf (φ n)
    rw [uIoc_of_le ht.1]
    exact (h_cont.mono (Ioc_subset_Icc_self.trans
      (Icc_subset_Icc le_rfl ht.2))).aestronglyMeasurable measurableSet_Ioc
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro s hs
    have hs := mem_Icc_of_mem_uIoc ht hs
    apply hf.norm_le s ⟨t₀.2.1.trans hs.1, hs.2⟩
    exact mapsTo_tonelliApproximation_delayedInput hf (φ n) hs
  · have h_lim :=
      tendsto_tonelliApproximation_delayedInput_of_tendstoUniformlyOn_tonelliApproximation
        hφ_mono hα_cont hα_tendsto
    apply Eventually.of_forall
    intro s hs
    have hs := mem_Icc_of_mem_uIoc ht hs
    apply Tendsto.comp (hf.continuousOn.continuousWithinAt _)
    · refine tendsto_nhdsWithin_iff.mpr
        ⟨Tendsto.prodMk_nhds tendsto_const_nhds (h_lim s hs), ?_⟩
      apply Eventually.of_forall
      exact fun n ↦ mem_prod.mpr
        ⟨⟨t₀.2.1.trans hs.1, hs.2⟩,
          MapsTo.comp (mapsTo_tonelliApproximation_closedBall hf _)
            (mapsTo_delayedInput t₀ _) hs⟩
    · refine ⟨⟨t₀.2.1.trans hs.1, hs.2⟩, ?_⟩
      apply IsClosed.mem_of_tendsto isClosed_closedBall (hα_tendsto.tendsto_at hs)
      exact Eventually.of_forall (fun n ↦ mapsTo_tonelliApproximation_closedBall hf (φ n) hs)

/-- There exists a solution of the integral equation on the interval backward in time. -/
lemma exists_eq_forall_mem_Icc_eq_integral_backward
    (hf : IsPeano f t₀ x₀ r L) :
    ∃ α : ℝ → E, ContinuousOn α (Icc tmin t₀) ∧ MapsTo α (Icc tmin t₀) (closedBall x₀ r) ∧
      ∀ t ∈ Icc tmin t₀.val,
        α t = x₀ + ∫ s in t₀..t, f (s, α s) := by
  let g : ℝ × E → E := fun x ↦ -f (-x.1, x.2)
  let t₀' : Icc (-tmax) (-tmin) :=
    ⟨-t₀, neg_Icc tmin tmax ▸ (Set.neg_mem_neg.mpr t₀.2)⟩
  have h_g : IsPeano g t₀' x₀ r L := by
    constructor
    · refine (ContinuousOn.neg (hf.continuousOn.comp ?_ ?_))
      · exact ContinuousOn.prodMap continuousOn_neg continuousOn_id
      · exact fun p hp ↦ ⟨⟨le_neg_of_le_neg hp.1.2, neg_le_of_neg_le hp.1.1⟩, hp.2⟩
    · intro t ht x hx
      simpa [g] using hf.norm_le (-t) ⟨le_neg_of_le_neg ht.2, neg_le_of_neg_le ht.1⟩ x hx
    · simpa [t₀', neg_add_eq_sub, sub_neg_eq_add, max_comm] using hf.mul_max_le
  obtain ⟨β, hβ_cont, hβ_maps, hβ_eq⟩ := exists_eq_forall_mem_Icc_eq_integral_forward h_g
  let α := fun x ↦ β (-x)
  refine
    ⟨α, hβ_cont.comp continuousOn_neg (fun _ hs ↦ ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩),
      fun t ht ↦ hβ_maps ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩, fun t ht ↦ ?_⟩
  have hβ_eq' := hβ_eq (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  rw [← intervalIntegral.integral_comp_neg] at hβ_eq'
  simpa [g, ← intervalIntegral.integral_symm] using hβ_eq'

/-- **Peano existence theorem**, integral form. A solution exists on the full time interval and
remains in `closedBall x₀ r`. -/
theorem exists_eq_forall_mem_Icc_eq_integral
    (hf : IsPeano f t₀ x₀ r L) :
    ∃ α : ℝ → E, ContinuousOn α (Icc tmin tmax) ∧ MapsTo α (Icc tmin tmax) (closedBall x₀ r) ∧
      ∀ t ∈ Icc tmin tmax, α t = x₀ + ∫ s in t₀..t, f (s, α s) := by
  obtain ⟨α₁, hα₁_cont, hα₁_maps, hα₁_eq⟩ :=
    exists_eq_forall_mem_Icc_eq_integral_forward hf
  obtain ⟨α₂, hα₂_cont, hα₂_maps, hα₂_eq⟩ :=
    exists_eq_forall_mem_Icc_eq_integral_backward hf
  let α : ℝ → E := fun t ↦ if t₀ ≤ t then α₁ t else α₂ t
  have hα_eq_α₁ : EqOn α α₁ (Icc t₀ tmax) := by
    unfold EqOn
    intro t ht
    unfold α
    rw [if_pos ht.1]
  have hα_eq_α₂ : EqOn α α₂ (Icc tmin t₀) := by
    unfold EqOn
    intro t ht
    unfold α
    by_cases ht_t₀ : t = t₀.val
    · rw [if_pos (ge_of_eq ht_t₀)]
      rw [hα₁_eq, hα₂_eq, ht_t₀]
      · simp
      · exact ht
      · rw [Set.mem_Icc]
        constructor
        · apply le_of_eq ht_t₀.symm
        · apply le_trans ht.2 t₀.prop.2
    · replace ht_t₀ := not_le_of_gt (lt_of_le_of_ne ht.2 ht_t₀)
      rw [if_neg ht_t₀]
  have h_union : Icc tmin t₀ ∪ Icc t₀ tmax = Icc tmin tmax := by
    apply Set.Icc_union_Icc_eq_Icc
    · exact t₀.prop.1
    · exact t₀.prop.2
  use α
  refine ⟨?_, ?_, ?_⟩
  · rw [← h_union]
    apply ContinuousOn.union_of_isClosed
    · apply ContinuousOn.congr hα₂_cont hα_eq_α₂
    · apply ContinuousOn.congr hα₁_cont hα_eq_α₁
    · apply isClosed_Icc
    · apply isClosed_Icc
  · rw [← h_union]
    apply MapsTo.union (MapsTo.congr hα₂_maps hα_eq_α₂.symm)
      (MapsTo.congr hα₁_maps hα_eq_α₁.symm)
  · intro t ht
    by_cases ht_t₀ : t₀.val ≤ t
    · have ht_interval : t ∈ Icc t₀.val tmax := ⟨ht_t₀, ht.2⟩
      rw [hα_eq_α₁ ht_interval, hα₁_eq t ht_interval]
      simp only [add_right_inj]
      rw [intervalIntegral.integral_congr]
      unfold Set.EqOn
      intro s hs
      simp only
      rw [hα_eq_α₁]
      rw [Set.uIcc_of_le ht_interval.1] at hs
      rw [Set.mem_Icc]
      constructor
      · exact hs.1
      · apply le_trans hs.2 ht_interval.2
    · simp only [not_le] at ht_t₀
      apply le_of_lt at ht_t₀
      have ht_interval : t ∈ Icc tmin t₀.val := ⟨ht.1, ht_t₀⟩
      rw [hα_eq_α₂ ht_interval, hα₂_eq t ht_interval]
      simp only [add_right_inj]
      rw [intervalIntegral.integral_congr]
      unfold Set.EqOn
      intro s hs
      simp only
      rw [hα_eq_α₂]
      rw [Set.uIcc_of_ge ht_interval.2] at hs
      rw [Set.mem_Icc]
      constructor
      · apply le_trans ht_interval.1 hs.1
      · exact hs.2

/-- **Peano existence theorem**, differential form. A solution to the initial value problem exists
on the full time interval. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀ (hf : IsPeano f t₀ x₀ r L) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f (t, α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα_cont, hα_maps, hα_eq⟩ := exists_eq_forall_mem_Icc_eq_integral hf
  use α
  constructor
  · rw [hα_eq t₀]
    · simp
    · exact t₀.2
  · intro t ht
    apply HasDerivWithinAt.congr _ hα_eq (hα_eq t ht)
    simp only [hasDerivWithinAt_const_add_iff]
    -- This instance is needed to synthesize `FTCFilter` for `Icc`.
    have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩
    have h_cont : ContinuousOn (fun s ↦ f (s, α s)) (Icc tmin tmax) := by
      apply hf.continuousOn.comp
      · exact ContinuousOn.prodMk continuousOn_id hα_cont
      · exact fun s hs ↦ mem_prod.mpr ⟨hs, hα_maps hs⟩
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · apply (h_cont.intervalIntegrable_of_Icc _).mono_set
      · exact (uIcc_subset_Icc t₀.2 ht).trans Icc_subset_uIcc
      · exact t₀.2.1.trans t₀.2.2
    · apply h_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc
    · exact h_cont.continuousWithinAt ht

end IsPeano
