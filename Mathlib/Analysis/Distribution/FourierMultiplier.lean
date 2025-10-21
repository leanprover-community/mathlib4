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

theorem one_add_norm_inv : (fun (x : H) ↦ (1 + ‖x‖^2)⁻¹).HasTemperateGrowth := by
  constructor
  · have : ∀ (x : H), 1 + ‖x‖^2 ≠ 0 := by
      intro x
      positivity
    exact (contDiff_const.add (contDiff_fun_id.norm_sq ℝ)).inv this
  intro n
  obtain ⟨k, C, hC, h⟩ := _root_.Function.HasTemperateGrowth.norm_iteratedFDeriv_le_uniform_aux
    ((Function.HasTemperateGrowth.const 1).add (hasTemperateGrowth_norm_sq H)) n
  use (1 + k) * n, (1 + C)^n * ↑n ! * ↑n !
  intro x
  have hdiff1 : ContDiff ℝ ∞ (fun (x : H) ↦ (1 + ‖x‖^2)) :=
    contDiff_const.add (contDiff_fun_id.norm_sq ℝ)
  set t := {y : ℝ | 1/2 < y}
  have ht : Set.range (fun (x : H) ↦ (1 + ‖x‖^2)) ⊆ t := by
    intro x ⟨y, hy⟩
    rw [← hy]
    simp only [Set.mem_setOf_eq, gt_iff_lt, t]
    exact lt_add_of_lt_add_left (c := 0) (by norm_num) (by positivity)
  have hdiff2 : ContDiffOn ℝ ∞ (fun t ↦ t⁻¹) t := by
    refine ContDiffOn.inv ?_ ?_
    · exact contDiffOn_fun_id
    intro x hx
    simp only [Set.mem_setOf_eq, t] at hx
    positivity
  have hn : n ≤ ∞ := ENat.LEInfty.out
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  have hfderiv : (∀ (i : ℕ), 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun x ↦ 1 + ‖x‖ ^ 2) x‖ ≤ ((1 + C) * (1 + ‖x‖) ^ (1 + k)) ^ i) := by
    intro i hi hi'
    apply (h i hi' x).trans
    rw [mul_pow, ← pow_mul]
    apply mul_le_mul_of_nonneg _ _ hC (by positivity)
    · have : C ≤ 1 + C := by simp
      apply this.trans
      apply le_self_pow₀ _ (by positivity)
      simp [hC]
    · apply pow_le_pow_right₀
      · simp
      have : k ≤ 1 + k := by simp
      apply this.trans
      rw [le_mul_iff_one_le_right ]
      exact hi
      positivity
  have hgderiv : ∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i (fun y ↦ y⁻¹) t (1 + ‖x‖ ^ 2)‖ ≤ n ! := by
      intro i hi
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]

      rw [iteratedDerivWithin_eq_iteratedDeriv hunique]; swap
      · apply contDiffAt_inv
        positivity
      swap
      · apply ht; simp
      rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
      simp only [Int.reduceNeg, norm_mul, norm_pow, norm_neg, one_mem,
        CStarRing.norm_of_mem_unitary, one_pow, RCLike.norm_natCast, one_mul, norm_zpow,
        Real.norm_eq_abs]
      have h1 : (↑i ! : ℝ) ≤ (↑n ! : ℝ) := by
        norm_cast
        exact Nat.factorial_le hi
      have h2 : |1 + ‖x‖ ^ 2| ^ (-1 - ↑i : ℤ) ≤ 1 := by
        apply zpow_le_one_of_nonpos₀
        · have : 0 ≤ 1 + ‖x‖^2 := by positivity
          simp [abs_of_nonneg this]
        · simp
      grw [mul_le_mul_of_nonneg h1 h2 (by positivity) zero_le_one, mul_one]
  have := norm_iteratedFDeriv_comp_le' ht hunique hdiff2 hdiff1 hn x hgderiv hfderiv
  have hpow : ‖x‖^n ≤ (1 + ‖x‖)^n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    linarith
  apply le_trans this
  rw [mul_pow, ← pow_mul]
  grind


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
    f (𝓕 ((SchwartzMap.smulLeftCLM 𝕜 E g) (𝓕⁻ u))) := by
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
    TemperedDistribution.fourierMultiplierCLM (E →L[ℂ] V) V g f = (f' : 𝓢'(ℂ, H, E →L[ℂ] V, V))
  else False

theorem memSobolev_iff {g : H → ℂ} (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) (hg : g.HasTemperateGrowth) :
    MemSobolev g f ↔ ∃ (f' : Lp E 2 (volume : Measure H)),
    .fourierMultiplierCLM (E →L[ℂ] V) V g f = (f' : 𝓢'(ℂ, H, E →L[ℂ] V, V)) := by
  simp only [MemSobolev, dite_else_false]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hg, h⟩⟩

theorem MemSobolev.exists {g : H → ℂ} {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hg : g.HasTemperateGrowth)
    (hf : MemSobolev g f) :
    ∃ (f' : Lp E 2 (volume : Measure H)),
    .fourierMultiplierCLM (E →L[ℂ] V) V g f = (f' : 𝓢'(ℂ, H, E →L[ℂ] V, V)) :=
  (memSobolev_iff f hg).mp hf

theorem memSobolev_one_iff {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} : MemSobolev 1 f ↔
    ∃ (f' : Lp E 2 (volume : Measure H)), f = f' := by
  convert memSobolev_iff f (.const 1)
  simp

end normed

section inner

variable [InnerProductSpace ℂ E]
variable [NormedSpace ℂ V] [CompleteSpace V]

theorem memSobolev_iff_fourierTransform [CompleteSpace E] {g : H → ℂ} (f : 𝓢'(ℂ, H, E →L[ℂ] V, V))
    (hg : g.HasTemperateGrowth) : MemSobolev g f ↔ ∃ (f' : Lp E 2 (volume : Measure H)),
    _root_.smulLeftCLM _ _ g (𝓕 f) = f' := by
  rw [memSobolev_iff f hg]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [TemperedDistribution.fourierMultiplierCLM_eq, FourierPairInv.fourier_inv] at hf'
    rw [hf', toTemperedDistribution_fourierTransform_eq V f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [TemperedDistribution.fourierMultiplierCLM_eq]
    apply_fun 𝓕⁻ at hf'
    rw [hf', toTemperedDistribution_fourierTransformInv_eq V f']

theorem memSobolev_one_iff_fourierTransform [CompleteSpace E]
    (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) : MemSobolev 1 f ↔ ∃ (f' : Lp E 2 (volume : Measure H)),
    𝓕 f = f' := by
  rw [memSobolev_one_iff]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    rw [hf', toTemperedDistribution_fourierTransform_eq]
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    apply_fun 𝓕⁻ at hf'
    simp only [FourierPair.inv_fourier] at hf'
    rw [hf', toTemperedDistribution_fourierTransformInv_eq]

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

open Real

noncomputable
instance TemperedDistribution.instLaplacian [CompleteSpace E] :
    Laplacian 𝓢'(ℂ, H, E, V) 𝓢'(ℂ, H, E, V) where
  laplacian := (2 * π) ^ 2 • TemperedDistribution.fourierMultiplierCLM E V (fun x ↦ ‖x‖ ^ 2 : H → ℂ)

theorem laplacian_mem_Sobolev_norm_sq {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hf : MemSobolev (‖·‖ ^ 2) f) :
    MemSobolev 1 (Δ f) := by
  rw [memSobolev_one_iff]
  rw [memSobolev_iff] at hf; swap
  · convert (hasTemperateGrowth_norm_sq H).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  obtain ⟨g, hg⟩ := hf
  use (2 * π)^2 • g
  have := (Lp.toTemperedDistributionCLM ℂ E V (volume : Measure H) 2).map_smul_of_tower
    ((2 * π)^2) g
  simp only [Lp.toTemperedDistributionCLM_apply] at this
  rw [this, ← hg]
  rfl

variable [CompleteSpace E]

theorem laplacian_toTemperedDistribution_eq' (f : 𝓢(ℝ, E)) : Δ (f : 𝓢'(ℂ, ℝ, E →L[ℂ] V, V)) =
    (2 * π) ^ 2 • ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ _ (fun x ↦ ‖x‖ ^ 2 : ℝ → ℂ) (𝓕 f)) : 𝓢(ℝ, E)) :
      𝓢'(ℂ, ℝ, E →L[ℂ] V, V)) := by
  change (2 * π) ^ 2 • 𝓕⁻ ((_root_.smulLeftCLM _ _ (fun x ↦ ‖x‖ ^ 2 : ℝ → ℂ))
    (𝓕 (f : 𝓢'(ℂ, ℝ, E →L[ℂ] V, V)))) = _
  have ht : Function.HasTemperateGrowth fun (x : ℝ) ↦ (‖x‖ ^ 2 : ℂ) := by
    convert (hasTemperateGrowth_norm_sq _).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp only [RCLike.ofRealCLM_apply, Complex.coe_algebraMap,
      Function.comp_apply, Complex.ofReal_pow]
  congr 1
  rw [TemperedDistribution.fourierTransformCLM_toTemperedDistributionCLM_eq,
    smulLeftCLM_toTemperedDistributionCLM_eq ht,
    TemperedDistribution.fourierTransformInv_toTemperedDistributionCLM_eq]

/-- The Laplacian is equal to `-f.deriv.deriv` for `f : 𝓢(ℝ, E)`. -/
theorem laplacian_toTemperedDistribution_eq (f : 𝓢(ℝ, E)) : Δ (f : 𝓢'(ℂ, ℝ, E →L[ℂ] V, V)) =
    ((-f.deriv.deriv) : 𝓢'(ℂ, ℝ, E →L[ℂ] V, V)) := by
  rw [laplacian_toTemperedDistribution_eq']
  have ht : Function.HasTemperateGrowth (fun (x : ℝ) ↦ (x : ℂ)) := by
    convert (Function.HasTemperateGrowth.id (E := ℝ)).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
  have : (2 * π) ^ 2 • (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ E (fun (x : ℝ) ↦ (‖x‖ ^ 2 : ℂ)) (𝓕 f))) =
      -f.deriv.deriv := by
    rw [← FourierPair.inv_fourier (F := 𝓢(ℝ, E)) f.deriv.deriv]
    rw [fourierTransform_deriv f.deriv, fourierTransform_deriv f]
    simp only [norm_eq_abs, map_smul]
    have := DFunLike.congr_fun (smulLeftCLM_mul ht ht (𝕜 := ℂ) (E := E)) (𝓕 f)
    simp only [coe_comp', Function.comp_apply] at this
    rw [this]
    have h₁ : ∀ (g : 𝓢(ℝ, E)), 𝓕⁻ (- g) = -𝓕⁻ g :=
      (SchwartzMap.fourierTransformCLE ℂ (V := ℝ) (E := E)).symm.toLinearMap.map_neg
    have h₂ : ∀ (a : ℝ) (g : 𝓢(ℝ, E)), 𝓕⁻ (a • g) = a • 𝓕⁻ g :=
      (SchwartzMap.fourierTransformCLE ℂ (V := ℝ) (E := E)).symm.toLinearMap.map_smul_of_tower
    rw [← h₁, ← h₂]
    congr
    rw [smul_smul, ← neg_smul]
    rw [← smul_one_smul ℂ ((2 * π) ^ 2)]
    congr
    · move_mul [← Complex.I, ← Complex.I]
      simp only [pow_two, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_one,
        Complex.I_mul_I, neg_mul, one_mul, neg_neg]
      ring
    ext x
    simp only [Pi.mul_apply]
    norm_cast
    simp only [sq_abs]
    ring
  apply_fun (toTemperedDistributionCLM ℂ ℝ E V volume) at this
  convert this
  · rw [ContinuousLinearMap.map_smul_of_tower]
  · rw [ContinuousLinearMap.map_neg]

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

variable [InnerProductSpace ℂ E]

theorem toTemperedDistribution_holder_eq (g : BoundedContinuousFunction H ℂ)
    (hg : Function.HasTemperateGrowth (g : H → ℂ)) :
    (((ContinuousLinearMap.lsmul ℂ ℂ).holder 2 (g.memLp_top.toLp _) f) : 𝓢'(ℂ, H, E →L[ℂ] V, V)) =
    (_root_.smulLeftCLM _ V (g : H → ℂ)) (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) := by
  ext u y
  congr 1
  simp
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2) (g.memLp_top.toLp _) f,
    g.memLp_top.coeFn_toLp, u.coeFn_toLp (1 - 2⁻¹)⁻¹,
    ((SchwartzMap.smulLeftCLM ℂ (E →L[ℂ] V) g) u).coeFn_toLp (1 - 2⁻¹)⁻¹] with x h_holder hg' hu h'
  simp [h_holder, hg', hu, h', hg]

section quotient

variable (D) [NormedAddCommGroup D]

def quotientBCF : BoundedContinuousFunction D ℂ :=
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

variable {D} in
@[simp]
lemma quotientBCF_apply (x : D) : quotientBCF D x = ‖x‖^2 / (1 + ‖x‖^2) := rfl

variable [InnerProductSpace ℝ D]

theorem quotientBCF_hasTemperateGrowth : Function.HasTemperateGrowth (quotientBCF D) := by
  have ht₁ : Function.HasTemperateGrowth fun (x : D) ↦ (‖x‖ ^ 2 : ℂ) := by
    convert (hasTemperateGrowth_norm_sq D).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  have ht₂ : Function.HasTemperateGrowth fun (x : D) ↦ ((1 + ‖x‖ ^ 2)⁻¹ : ℂ) := by
    convert (one_add_norm_inv (H := D)).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  convert ht₁.mul ht₂

end quotient

variable [CompleteSpace E]

theorem memSobolevLaplacian {f : 𝓢'(ℂ, H, E →L[ℂ] V, V)} (hf : MemSobolev (fun x ↦ 1 + ‖x‖ ^ 2) f) :
    MemSobolev 1 (Δ f) := by
  apply laplacian_mem_Sobolev_norm_sq
  have ht₁ : Function.HasTemperateGrowth fun (x : H) ↦ (‖x‖ ^ 2 : ℂ) := by
    convert (hasTemperateGrowth_norm_sq H).comp_clm_left (RCLike.ofRealCLM (K := ℂ))
    simp
  have ht₂ : Function.HasTemperateGrowth fun (x : H) ↦ (1 + ‖x‖ ^ 2 : ℂ) := by
    convert ((Function.HasTemperateGrowth.const 1).add (hasTemperateGrowth_norm_sq H)).comp_clm_left
      (RCLike.ofRealCLM (K := ℂ))
    simp
  have ht₃ := quotientBCF_hasTemperateGrowth H
  rw [memSobolev_iff_fourierTransform f ht₁]
  rw [memSobolev_iff_fourierTransform f ht₂] at hf
  obtain ⟨f', hf'⟩ := hf
  use (ContinuousLinearMap.lsmul ℂ ℂ).holder 2 ((quotientBCF H).memLp_top.toLp _) f'
  have := DFunLike.congr_fun (mul_smulLeftCLM ht₂ ht₃) (𝓕 f)
  simp only [coe_comp', Function.comp_apply] at this
  rw [toTemperedDistribution_holder_eq f' (quotientBCF H) ht₃]
  rw [← hf', this]
  congr
  ext x
  simp only [Pi.mul_apply, quotientBCF_apply]
  norm_cast
  field_simp

end inner
