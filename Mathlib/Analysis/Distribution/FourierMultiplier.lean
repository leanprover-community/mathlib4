/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Fourier.L2Space

/-!

# Fourier multiplier

-/

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure
open scoped FourierTransform

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' H D E F G V : Type*}

#check norm_fderiv_norm_id_rpow

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H] [NormedAddCommGroup V]

variable [NormedSpace 𝕜 E] [InnerProductSpace ℝ H] [NormedSpace 𝕜 V]

section has_growth

variable (H) in
@[simp]
theorem fderiv_norm_sq' : fderiv ℝ (fun (x : H) ↦ ‖x‖^2) = 2 • (innerSL ℝ (E := H)) := by
  ext1 x
  simpa using (HasFDerivAt.norm_sq (hasFDerivAt_id x)).fderiv

variable (H) in
theorem hasTemperateGrowth_norm_sq : (fun (x : H) ↦ ‖x‖^2).HasTemperateGrowth := by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · simp only [fderiv_norm_sq']
    convert (2 • (innerSL ℝ)).hasTemperateGrowth
  · exact (contDiff_norm_sq ℝ (n := 1)).differentiable (Eq.refl _).le
  · intro x
    simp only [norm_pow, norm_norm, one_mul, add_pow_two]
    apply le_add_of_nonneg_left
    positivity

variable [NormedSpace ℝ E]

theorem Function.HasTemperateGrowth.add {f₁ f₂ : H → E}
    (hf₁ : f₁.HasTemperateGrowth) (hf₂ : f₂.HasTemperateGrowth) : (f₁ + f₂).HasTemperateGrowth := by
  refine ⟨hf₁.1.add hf₂.1, ?_⟩
  intro n
  obtain ⟨k₁, C₁, h₁⟩ := hf₁.2 n
  obtain ⟨k₂, C₂, h₂⟩ := hf₂.2 n
  use max k₁ k₂, C₁ + C₂
  intro x
  rw [iteratedFDeriv_add_apply (hf₁.1.contDiffAt.of_le ENat.LEInfty.out)
    (hf₂.1.contDiffAt.of_le ENat.LEInfty.out)]
  grw [norm_add_le, h₁ x, h₂ x, add_mul, add_le_add]
  · gcongr
    · have := h₁ 0
      simp at this
      grw [← this]
      positivity
    · apply le_add_of_nonneg_right (by positivity)
    exact k₁.le_max_left k₂
  · gcongr
    · have := h₂ 0
      simp at this
      grw [← this]
      positivity
    · apply le_add_of_nonneg_right (by positivity)
    exact k₁.le_max_right k₂

section comp_clm

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Function.HasTemperateGrowth.comp_clm_left {f : H → E} (hf : f.HasTemperateGrowth)
    (g : E →L[ℝ] F) : (g ∘ f).HasTemperateGrowth := by
  refine ⟨hf.1.continuousLinearMap_comp _, ?_⟩
  intro n
  obtain ⟨k, C, h⟩ := hf.2 n
  use k, ‖g‖ * C
  intro x
  grw [ContinuousLinearMap.iteratedFDeriv_comp_left g hf.1.contDiffAt ENat.LEInfty.out,
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le, h, mul_assoc]

end comp_clm

theorem HasTemperateGrowth.const_rpow {f : H → ℝ} (hf : f.HasTemperateGrowth)
    (hf' : ∃ (C : ℝ) (_ : 0 < C), ∀ x, C < f x)
    {r : ℝ} : (fun x ↦ (f x) ^ r).HasTemperateGrowth := by
  obtain ⟨C, hC, hf'⟩ := hf'
  refine ⟨hf.1.rpow_const_of_ne (fun x ↦ (hC.trans (hf' x)).ne'), ?_⟩
  intro n
  sorry

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

end has_growth

variable
  [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

section normed

variable [NormedSpace ℂ E] [SMulCommClass ℂ 𝕜 E]

section multiplier

variable [CompleteSpace E]

variable (E V) in
def TemperedDistribution.fourierMultiplierCLM (g : H → 𝕜) :
    𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  fourierTransformInvCLM 𝕜 H E V ∘L (smulLeftCLM E V g) ∘L fourierTransformCLM 𝕜 H E V

theorem TemperedDistribution.fourierMultiplierCLM_eq (g : H → 𝕜) (f : 𝓢'(𝕜, H, E, V)) :
    TemperedDistribution.fourierMultiplierCLM E V g f = 𝓕⁻ ((smulLeftCLM E V g) (𝓕 f)) := by
  rfl

theorem TemperedDistribution.fourierMultiplierCLM_apply (g : H → 𝕜) (f : 𝓢'(𝕜, H, E, V))
    (u : 𝓢(H, E)) : TemperedDistribution.fourierMultiplierCLM E V g f u =
    f (𝓕 ((SchwartzMap.smulLeftCLM E g) (𝓕⁻ u))) := by
  rfl

@[simp]
theorem TemperedDistribution.fourierMultiplierCLM_const_apply (f : 𝓢'(𝕜, H, E, V)) (c : 𝕜) :
    TemperedDistribution.fourierMultiplierCLM E V (fun _ ↦ c) f = c • f := by
  ext
  unfold TemperedDistribution.fourierMultiplierCLM
  simp

end multiplier

variable [NormedSpace ℂ V] [CompleteSpace V]

open Classical in
def MemSobolev (g : H → ℂ) (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) : Prop :=
  if _hg : g.HasTemperateGrowth then
    ∃ (f' : Lp E 2 (volume : Measure H)),
    TemperedDistribution.fourierMultiplierCLM (E →L[ℂ] V) V g f = Lp.toTemperedDistribution ℂ V f'
  else False

theorem memSobolev_iff {g : H → ℂ} (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) (hg : g.HasTemperateGrowth) :
    MemSobolev g f ↔ ∃ (f' : Lp E 2 (volume : Measure H)),
    .fourierMultiplierCLM (E →L[ℂ] V) V g f = Lp.toTemperedDistribution ℂ V f' := by
  simp only [MemSobolev, dite_else_false]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hg, h⟩⟩

theorem MemSobolev.exists {g : H → ℂ} {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hg : g.HasTemperateGrowth)
    (hf : MemSobolev g f) :
    ∃ (f' : Lp E 2 (volume : Measure H)),
    .fourierMultiplierCLM (E →L[ℂ] V) V g f = Lp.toTemperedDistribution ℂ V f' :=
  (memSobolev_iff f hg).mp hf

theorem memSobolev_one_iff {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} : MemSobolev 1 f ↔
    ∃ (f' : Lp E 2 (volume : Measure H)), f = Lp.toTemperedDistribution ℂ V f' := by
  convert memSobolev_iff f (.const 1)
  simp

end normed

section inner

variable [InnerProductSpace ℂ E]
variable [NormedSpace ℂ V] [CompleteSpace V]

theorem memSobolev_iff_fourierTransform [CompleteSpace E] {g : H → ℂ} (f : 𝓢'(ℂ, H, E →L[ℂ] V, V))
    (hg : g.HasTemperateGrowth) : MemSobolev g f ↔ ∃ (f' : Lp E 2 (volume : Measure H)),
    smulLeftCLM _ _ g (𝓕 f) = Lp.toTemperedDistribution ℂ V f' := by
  rw [memSobolev_iff f hg]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [TemperedDistribution.fourierMultiplierCLM_eq,
      TemperedDistribution.fourier_inversion_inv] at hf'
    rw [hf', toTemperedDistribution_fourierTransform_eq V f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [TemperedDistribution.fourierMultiplierCLM_eq]
    apply_fun 𝓕⁻ at hf'
    rw [hf', toTemperedDistribution_fourierTransformInv_eq V f']

end inner

class Laplacian (X : Type*) (Y : outParam (Type*)) where
  /-- `Δ f` is the Laplace operator applied to `f`. The meaning of this notation is
  type-dependent. -/
  laplacian : X → Y

namespace Laplacian

@[inherit_doc] scoped notation "Δ" => Laplacian.laplacian

end Laplacian

open Laplacian

variable [NormedSpace ℂ V] [CompleteSpace V]

section normed

variable [NormedSpace ℂ E]

noncomputable
instance TemperedDistribution.instLaplacian [CompleteSpace E] :
    Laplacian 𝓢'(ℂ, H, E, V) 𝓢'(ℂ, H, E, V) where
  laplacian := TemperedDistribution.fourierMultiplierCLM E V (‖·‖ ^ 2 : H → ℂ)

theorem laplacian_mem_Sobolev_norm_sq {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hf : MemSobolev (‖·‖ ^ 2) f) :
    MemSobolev 1 (Δ f) := by
  rw [memSobolev_one_iff]
  rw [memSobolev_iff] at hf; swap
  · convert (hasTemperateGrowth_norm_sq H).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  obtain ⟨g, hg⟩ := hf
  use g
  rw [← hg]
  rfl

end normed

section inner

variable (u : BoundedContinuousFunction H ℂ) (f : Lp E 2 (volume : Measure H))

theorem BoundedContinuousFunction.memLp_top (u : BoundedContinuousFunction H E) :
    MemLp u ⊤ (volume : Measure H) := by
  constructor
  · exact u.continuous_toFun.aestronglyMeasurable
  · apply MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound (C := ‖u‖)
    filter_upwards with x
    exact BoundedContinuousFunction.norm_coe_le_norm u x

variable [InnerProductSpace ℂ E] [CompleteSpace E]

#check (ContinuousLinearMap.lsmul ℂ ℂ).holder 2 (u.memLp_top.toLp _) f

variable (g : H → ℂ)

#check (_root_.smulLeftCLM (𝕜 := ℂ) E V (g : H → ℂ))

theorem toTemperedDistribution_holder_eq (g : BoundedContinuousFunction H ℂ)
    (hg : Function.HasTemperateGrowth (g : H → ℂ)) :
    Lp.toTemperedDistribution ℂ V ((ContinuousLinearMap.lsmul ℂ ℂ).holder 2 (g.memLp_top.toLp _) f) =
    (_root_.smulLeftCLM _ V (g : H → ℂ)) (Lp.toTemperedDistribution ℂ V f) := by
  ext u y
  congr 1
  simp
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2) (g.memLp_top.toLp _) f,
    g.memLp_top.coeFn_toLp, u.coeFn_toLp (1 - 2⁻¹)⁻¹,
    ((SchwartzMap.smulLeftCLM (E →L[ℂ] V) g) u).coeFn_toLp (1 - 2⁻¹)⁻¹] with x h_holder hg' hu h'
  simp [h_holder, hg', hu, h', hg]

variable (H) in
def quotientBCF : BoundedContinuousFunction H ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ ‖x‖^2 / (1 + ‖x‖^2)) (by
    apply Continuous.div
    · fun_prop
    · fun_prop
    intro x
    norm_cast
    positivity) 1 (by
    intro x
    simp only [Complex.norm_div, norm_pow, Complex.norm_real, norm_norm]
    rw [div_le_iff₀]; swap
    · rw [norm_pos_iff]
      norm_cast
      positivity
    simp only [one_mul]
    have : ‖x‖^2 ≤ 1 + ‖x‖^2 := by simp
    convert this
    norm_cast
    simp only [Real.norm_eq_abs, abs_eq_self]
    positivity)

theorem foo1 {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hf : MemSobolev (fun x ↦ 1 + ‖x‖ ^ 2) f) :
    MemSobolev 1 (Δ f) := by
  apply laplacian_mem_Sobolev_norm_sq
  rw [memSobolev_iff_fourierTransform f]; swap
  · convert (hasTemperateGrowth_norm_sq H).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  rw [memSobolev_iff_fourierTransform f] at hf; swap
  · convert ((Function.HasTemperateGrowth.const 1).add (hasTemperateGrowth_norm_sq H)).comp_clm_left
      (RCLike.ofRealCLM (K := ℂ))
    simp
  obtain ⟨f', hf'⟩ := hf
  use (ContinuousLinearMap.lsmul ℂ ℂ).holder 2 ((quotientBCF H).memLp_top.toLp _) f'

  sorry
  /-rw [memSobolev_iff]; swap
  · convert (hasTemperateGrowth_norm_sq H).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  rw [memSobolev_iff] at hf; swap
  · convert ((Function.HasTemperateGrowth.const 1).add (hasTemperateGrowth_norm_sq H)).comp_clm_left
      (RCLike.ofRealCLM (K := ℂ))
    simp
  obtain ⟨f', hf'⟩ := hf-/


end inner
