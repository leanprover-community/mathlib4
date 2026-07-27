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

This files concerns ODE theory involving a continuous time-dependent vector field on a
finite-dimensional real normed vector space. The assumptions are collected in `IsPeano`.

The proof constructs Tonelli approximations with a delayed input, and extracts a uniformly
convergent subsequence using the Arzelà–Ascoli theorem.

## Main definitions

- `IsPeano`: the hypotheses on the vector field and its cylinder of definition.
- `IsPeano.stepSize`: the time-step size of a Tonelli approximation.
- `IsPeano.delayedInput`: the delayed time argument used in the Tonelli approximations.
- `IsPeano.tonelliIterate`: the recursively defined curves used in the construction.
- `IsPeano.tonelliApproximation`: the diagonal sequence of Tonelli approximations.
- `IsPeano.boundedTonelliApproximation`: the approximations as bounded continuous functions.

## Implementation notes

The finite-dimensionality assumption is used to apply the Arzelà–Ascoli theorem.

## Tags

differential equation, initial value problem, Tonelli approximation
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
lemma stepSize_nonneg (t₀ : Icc tmin tmax) (n : ℕ) : 0 ≤ stepSize t₀ n :=
  div_nonneg (sub_nonneg.mpr t₀.2.2) (Nat.cast_nonneg n)

lemma add_mul_stepSize_eq_tmax (t₀ : Icc tmin tmax) (n : ℕ) :
    t₀.val + ((n : ℝ) + 1) * stepSize t₀ (n + 1) = tmax := by
  rw [stepSize]
  field_simp
  push_cast
  ring

/-- The delayed time input used in the Tonelli approximations. -/
noncomputable def delayedInput (t₀ : Icc tmin tmax) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ max (t - stepSize t₀ n) t₀

/-- The delayed input maps the first `k + 1` time steps into the first `k` time steps. -/
lemma mapsTo_delayedInput_previous_interval (n k : ℕ) (t₀ : Icc tmin tmax) :
    MapsTo (delayedInput t₀ n)
      (Icc t₀.val (t₀ + (k + 1 : ℝ) * stepSize t₀ n))
      (Icc t₀.val (t₀ + (k : ℝ) * stepSize t₀ n)) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have h_mul_nonneg : 0 ≤ (k : ℝ) * stepSize t₀ n :=
    mul_nonneg (Nat.cast_nonneg k) (stepSize_nonneg t₀ n)
  unfold delayedInput
  constructor
  · exact le_max_right _ _
  · apply max_le <;> linarith

/-- The delayed input maps `Icc t₀ tmax` to itself. -/
lemma mapsTo_delayedInput (t₀ : Icc tmin tmax) (n : ℕ) :
    MapsTo (delayedInput t₀ n) (Icc t₀.val tmax) (Icc t₀.val tmax) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have := stepSize_nonneg t₀ n
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

end IsPeano
