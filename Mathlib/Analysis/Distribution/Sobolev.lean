/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces (Bessel potential spaces)

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

section normed

variable [NormedSpace ℂ F]

def MemSobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  ∃ (f' : Lp F p (volume : Measure E)),
    fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f = f'

theorem memSobolev_zero_iff {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    ∃ (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]

theorem memSobolev_add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  change _ = Lp.toTemperedDistributionCLM F volume p (f' + g')
  simp [map_add, hf, hg]

theorem memSobolev_smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  change _ = Lp.toTemperedDistributionCLM F volume p (c • f')
  simp [hf]

variable (E F) in
theorem memSobolev_zero (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  change _ = Lp.toTemperedDistributionCLM F volume p 0
  simp only [map_zero]

variable (E F) in
def Sobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : Submodule ℂ 𝓢'(E, F) where
  carrier := MemSobolev s p
  add_mem' := memSobolev_add
  zero_mem' := memSobolev_zero E F s p
  smul_mem' := memSobolev_smul

namespace Sobolev

def sobFn {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Sobolev E F s p) :
    Lp F p (volume : Measure E) :=
  f.2.choose

theorem sobFn_spec {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : Sobolev E F s p} :
    fourierMultiplierCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f = sobFn f :=
  f.2.choose_spec

@[fun_prop]
theorem Complex.hasTemperateGrowth_ofReal : Function.HasTemperateGrowth Complex.ofReal :=
  ContinuousLinearMap.hasTemperateGrowth (Complex.ofRealCLM)

@[simp]
theorem fourierMultiplier_neg_sobFn_eq {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    {f : Sobolev E F s p} :
    fourierMultiplierCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) (sobFn f) = f := by
  rw [← sobFn_spec, fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  convert fourierMultiplierCLM_const_apply f.1 1 with x
  · simp only [Pi.mul_apply]
    norm_cast
    calc
      _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + -s / 2) := by
        rw [← Real.rpow_add (by positivity)]
      _ = (1 + ‖x‖ ^ 2) ^ (0 : ℝ) := by congr; ring
      _ = _ := by simp
  · simp

theorem injective_sobFn {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    Function.Injective (sobFn (s := s) (p := p) (E := E) (F := F)) := by
  intro ⟨f, hf⟩ ⟨g, hg⟩ hfg
  simp only [Subtype.mk.injEq]
  calc
    f = fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ ((-s + s) / 2) : ℝ)) f := by simp
    _ = fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ))
        (Sobolev.sobFn ⟨f, hf⟩) := by simp
    _ = fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ))
        (Sobolev.sobFn ⟨g, hg⟩) := by congr
    _ = fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ ((-s + s) / 2) : ℝ)) g := by simp
    _ = g := by simp

variable (E F) in
def toLpₗ (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Sobolev E F s p →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := Sobolev.sobFn
  map_add' f g := by
    apply_fun Lp.toTemperedDistributionCLM F (volume : Measure E) p
    · simp [map_add, ← sobFn_spec]
    rw [injective_iff_map_eq_zero, ← LinearMap.ker_eq_bot']
    exact Lp.ker_toTemperedDistributionCLM_eq_bot
  map_smul' c f := by
    apply_fun Lp.toTemperedDistributionCLM F (volume : Measure E) p
    · simp [← sobFn_spec]
    rw [injective_iff_map_eq_zero, ← LinearMap.ker_eq_bot']
    exact Lp.ker_toTemperedDistributionCLM_eq_bot

theorem sobFn_add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f g : Sobolev E F s p) :
    sobFn (f + g) = sobFn f + sobFn g := (toLpₗ E F s p).map_add f g

theorem sobFn_smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) (f : Sobolev E F s p) :
    sobFn (c • f) = c • sobFn f := (toLpₗ E F s p).map_smul c f

@[simp]
theorem toLpₗ_apply {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Sobolev E F s p) :
    toLpₗ E F s p f = sobFn f := rfl

instance instNormedAddCommGroup (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    NormedAddCommGroup (Sobolev E F s p) :=
  NormedAddCommGroup.induced (Sobolev E F s p) (Lp F p (volume : Measure E)) (toLpₗ E F s p)
    injective_sobFn

@[simp]
theorem norm_sobFn_eq (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : Sobolev E F s p) :
    ‖sobFn f‖ = ‖f‖ :=
  rfl

instance instNormedSpace (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    NormedSpace ℂ (Sobolev E F s p) where
  norm_smul_le c f := by
    simp_rw [← norm_sobFn_eq, ← norm_smul]
    apply Eq.le
    congr
    exact (toLpₗ E F s p).map_smul c f

variable (E F) in
def toLpₗᵢ (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Sobolev E F s p →ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  norm_map' f := by simp

variable (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)]

example : NormedSpace ℂ (Sobolev E F s p) := by
  infer_instance

end Sobolev

end normed

section inner

variable [InnerProductSpace ℂ F]

theorem memSobolev_two_iff_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  rw [MemSobolev]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [TemperedDistribution.fourierMultiplierCLM_apply, fourier_fourierInv_eq] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']

theorem memSobolev_zero_two_iff_fourierTransform {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_two_iff_fourier]

namespace Sobolev

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (Sobolev E F s 2) where
  inner f g := inner ℂ (sobFn f) (sobFn g)
  norm_sq_eq_re_inner f := by simp; norm_cast
  conj_inner_symm f g := by simp
  add_left f g h := by rw [sobFn_add, inner_add_left]
  smul_left f g c := by rw [sobFn_smul, inner_smul_left]

end Sobolev

end inner
