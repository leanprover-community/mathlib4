/-
Copyright (c) 2024 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib

open scoped ComplexConjugate
open scoped NNReal ENNReal Matrix Real
open MeasureTheory Complex

-- rename
class WellDistributed {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) : Prop where
  is_well_distributed : ∀ i : ι, μ {i} ≤ 1

-- alternative implementation: l∞ norm ≤ 1
-- variable (μ ν : lp (fun _ : (Fin 2 → ℤ) ↦ ℝ) ∞)

def SupportedCoprime (μ : Measure (Fin 2 → ℤ)) : Prop :=
  ∀ p : Fin 2 → ℤ, μ {p} ≠ 0 → IsCoprime (p 0) (p 1)

variable (μ ν : Measure (Fin 2 → ℤ)) [IsFiniteMeasure μ]
  [WellDistributed μ] [WellDistributed ν]
  (hμ : SupportedCoprime μ) (hν : SupportedCoprime ν)
  (β : ℝ) (a q : ℕ) (hq₀ : q ≠ 0) (haq : IsCoprime a q) (N Q K : ℝ) (hK₀ : 0 ≤ K) (hQ₀ : 0 ≤ Q)
  (hQ : Q ^ 2 < N)
  (hK : Q ^ 2 * K ^ 2 < N) (hq₁ : Q ≤ q) (hq₂ : q ≤ 2 * Q) (hβ₁ : K / (2 * N) ≤ |β|)
  (hβ₂ : |β| ≤ K / N)
  (hμN : ∀ x : Fin 2 → ℤ, μ {x} ≠ 0 → x ⬝ᵥ x ≤ N)
  (hμN : ∀ y : Fin 2 → ℤ, μ {y} ≠ 0 → y ⬝ᵥ y ≤ N)

set_option quotPrecheck false in
notation "θ" => (a:ℝ) / q + β

set_option quotPrecheck false in
notation "S" => ∫ x : Fin 2 → ℤ, ∫ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν ∂μ

theorem MeasureTheory.Lp.norm_const'' {α : Type*} {E : Type*} {m0 : MeasurableSpace α} (p : ℝ≥0∞)
    (μ : Measure α) [NormedAddCommGroup E] [IsFiniteMeasure μ] (c : E) [NeZero μ]
    (hp_zero : p ≠ 0) :
    ‖(Lp.const p μ) c‖ = ‖c‖ * (measureUnivNNReal μ) ^ (1 / p.toReal) :=
  sorry

section CauchySchwarzIntegral

variable {α : Type*} {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
  (μ : Measure α)
  (f g : α → 𝕜)


example {z : ℂ} : ‖z‖^2=conj z * z := by exact?

theorem cauchy_schwarz (hf : Memℒp f 2 μ) (hg : Memℒp g 2 μ) :
    ‖∫ a, f a * g a ∂μ‖ ^ 2 ≤ (∫ a, ‖f a‖ ^ 2 ∂μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) :=
  sorry

@[simp] theorem measure_univ_toReal : (μ Set.univ).toReal = measureUnivNNReal μ := rfl

end CauchySchwarzIntegral


example : ‖S‖ ^ 2 ≤ (measureUnivNNReal μ) ^ 2 * (measureUnivNNReal ν) ^ 2 / (K * Q) ^ 2 := by
  let f : (Fin 2 → ℤ) → ℂ := 1
  have hf : Memℒp f 2 μ := sorry --indicatorConstLp (μ := μ) (s := Set.univ) 2 sorry sorry 1
  let g : (Fin 2 → ℤ) → ℂ := fun x ↦ ∫ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν
  calc
    _ = _ := by simp [f, g]
    _ ≤ _ := cauchy_schwarz (𝕜 := ℂ) μ f g hf sorry
    _ = (measureUnivNNReal μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) := by simp [f]
    _ ≤ (measureUnivNNReal μ) *
          ((measureUnivNNReal μ) * (measureUnivNNReal ν) ^ 2 / (K * Q) ^ 2) := ?_
    _ = _ := by ring
  gcongr
  calc _ = ‖∫ (a : Fin 2 → ℤ), conj (g a) * g a ∂μ‖ := sorry
    _ ≤ _ := ?_
  dsimp only [g]
  simp_rw [← integral_conj]
  sorry
