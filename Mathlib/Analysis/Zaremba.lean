/-
Copyright (c) 2024 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib

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

example : abs S ≤ (measureUnivNNReal μ) * (measureUnivNNReal ν) / (K * Q) := by
  let f : Lp ℂ 2 μ := indicatorConstLp (μ := μ) (s := Set.univ) 2 sorry sorry 1
  let g : Lp ℂ 2 μ := Memℒp.toLp (fun x ↦ ∫ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν) sorry
  have H := norm_inner_le_norm (𝕜 := ℂ) f g
  have : NeZero μ := sorry
  rw [L2.inner_indicatorConstLp_one] at H
  simp [f, Lp.norm_const''] at H
  calc
    _ = _ := by
        congrm Complex.abs ?_
        apply integral_congr_ae
        symm
        apply Memℒp.coeFn_toLp
    _ ≤ _ := H
  apply le_of_pow_le_pow_left (n := 2) (by norm_num) (by positivity)
  calc _ = measureUnivNNReal μ * ‖g‖ ^ ((2:ℝ≥0):ℝ) := by norm_cast; sorry -- squ
    _ ≤ (measureUnivNNReal μ) * (measureUnivNNReal μ * ((measureUnivNNReal ν) / (K * Q)) ^ 2) := ?_
    _ = _ := by ring
  gcongr
  sorry
