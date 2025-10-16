/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!

# Fourier multiplier

-/

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure
open scoped FourierTransform

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' H D E F G V : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H] [NormedAddCommGroup V]

variable --[NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedSpace 𝕜 V] [CompleteSpace E]



variable (f : 𝓢'(𝕜, H, E, V)) (g : H → 𝕜) (hg : g.HasTemperateGrowth)

@[fun_prop]
theorem foo (s : ℝ) : ContDiff ℝ ∞ (fun (x : H) ↦ (1 + ‖x‖^2)^(s/2)) := by
  have : ∀ (x : H), 1 + ‖x‖^2 ≠ 0 := by
    intro x
    positivity
  exact (contDiff_const.add (contDiff_fun_id.norm_sq ℝ)).rpow_const_of_ne this

theorem bar (s : ℝ) : (fun (x : H) ↦ (1 + ‖x‖^2)^(s/2)).HasTemperateGrowth := by
  constructor
  · have : ∀ (x : H), 1 + ‖x‖^2 ≠ 0 := by
      intro x
      positivity
    exact (contDiff_const.add (contDiff_fun_id.norm_sq ℝ)).rpow_const_of_ne this
  intro n
  rcases exists_nat_gt s with ⟨k, hk⟩
  use k + n, ↑n ! * k ^ n * 2 ^ n
  intro x
  have hdiff1 : ContDiff ℝ ∞ (fun (x : H) ↦ (1 + ‖x‖^2)) :=
    contDiff_const.add (contDiff_fun_id.norm_sq ℝ)
  set t := {y : ℝ | 1/2 < y}
  have ht : Set.range (fun (x : H) ↦ (1 + ‖x‖^2)) ⊆ t := by
    intro x ⟨y, hy⟩
    rw [← hy]
    simp only [Set.mem_setOf_eq, gt_iff_lt, t]
    exact lt_add_of_lt_add_left (c := 0) (by norm_num) (by positivity)
  have hdiff2 : ContDiffOn ℝ ∞ (fun t ↦ t^(s/2)) t := by
    refine ContDiffOn.rpow_const_of_ne ?_ ?_
    · exact contDiffOn_fun_id
    intro x hx
    simp only [Set.mem_setOf_eq, t] at hx
    positivity
  have hn : n ≤ ∞ := ENat.LEInfty.out
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  have hfderiv : (∀ (i : ℕ), 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun x ↦ 1 + ‖x‖ ^ 2) x‖ ≤ (2 * ‖x‖) ^ i) := by
    intro i hi hi'

    sorry
  have hgderiv : (∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i (fun y ↦ y ^ (s / 2)) t (1 + ‖x‖ ^ 2)‖ ≤ k^n * (1 + ‖x‖)^k) := by
      intro i hi
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
      rw [iteratedDerivWithin_eq_iterate]

      sorry
  have := norm_iteratedFDeriv_comp_le' ht hunique hdiff2 hdiff1 hn x hgderiv hfderiv
  have hpow : ‖x‖^n ≤ (1 + ‖x‖)^n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    linarith
  apply le_trans this
  grw [mul_pow, hpow, pow_add]
  move_mul [(1 + ‖x‖) ^ n, (1 + ‖x‖) ^ k]
  gcongr

def SchwartzMap.fourierMultiplierCLM {g : H → 𝕜} (hg : g.HasTemperateGrowth) : 𝓢(H, E) →L[𝕜] 𝓢(H, E) :=
    (fourierTransformCLE 𝕜).symm.toContinuousLinearMap ∘L (smulLeftCLM E hg) ∘L
      (fourierTransformCLM 𝕜)

theorem fourierMultiplierCLM_apply {g : H → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(H, E)) :
    fourierMultiplierCLM hg f = ((smulLeftCLM E hg) f.fourierTransform).fourierTransformInv := by
  unfold fourierMultiplierCLM
  simp

@[simp]
theorem SchwartzMap.fourierMultiplierCLM_const_apply (f : 𝓢(H, E)) (c : 𝕜) :
    fourierMultiplierCLM (Function.HasTemperateGrowth.const c) f = c • f := by
  unfold fourierMultiplierCLM
  simp

variable (E V) in
def TemperedDistribution.fourierMultiplierCLM {g : H → 𝕜} (hg : g.HasTemperateGrowth) :
    𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  mkCompCLM V (SchwartzMap.fourierMultiplierCLM hg)

@[simp]
theorem TemperedDistribution.fourierMultiplierCLM_apply {g : H → 𝕜} (hg : g.HasTemperateGrowth)
  (f : 𝓢'(𝕜, H, E, V)) (h : 𝓢(H, E)) : TemperedDistribution.fourierMultiplierCLM E V hg f h =
      f (SchwartzMap.fourierMultiplierCLM hg h) := rfl

@[simp]
theorem TemperedDistribution.fourierMultiplierCLM_const_apply (f : 𝓢'(𝕜, H, E, V)) (c : 𝕜) :
    TemperedDistribution.fourierMultiplierCLM E V (.const c) f = c • f := by
  ext
  simp

variable [NormedSpace ℂ V] [CompleteSpace V]

def memSobolev {g : H → ℂ} (hg : g.HasTemperateGrowth) (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) : Prop :=
  ∃ (f' : Lp E 2 (volume : Measure H)),
    TemperedDistribution.fourierMultiplierCLM (E →L[ℂ] V) V hg f = Lp.toTemperedDistribution ℂ V f'

theorem memSobolev_one {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hf : memSobolev (.const 1) f) :
    ∃ (f' : Lp E 2 (volume : Measure H)), f = Lp.toTemperedDistribution ℂ V f' := by
  rcases hf with ⟨f', hf'⟩
  use f'
  simpa using hf'
