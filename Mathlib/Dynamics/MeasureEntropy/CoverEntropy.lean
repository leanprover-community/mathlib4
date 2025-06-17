/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage

/-!
# Measure entropy via covers
-/

namespace Dynamics

open Set MeasureTheory

variable {X : Type*}

/-! ### Measurable covers -/

/-- Test -/
def IsCoverOf (F : Set X) (s : Set (Set X)) : Prop :=
  F ⊆ ⋃ A ∈ s, A

variable [MeasurableSpace X]

def My_Sum (T : X → X) (μ : Measure X) (n : ℕ) (s : Set (Set X)) [Fintype s] : EReal :=
  ∑ A : Fin n → s, μ (⋂ k : Fin n, T^[k] ⁻¹' (A k))

@[simp]
lemma My_Sum_zero {T : X → X} {μ : Measure X} {s : Set (Set X)} [Fintype s] :
    My_Sum T μ 0 s = μ univ := by
  simp [My_Sum]

@[simp]
lemma My_Sum_one {T : X → X} {μ : Measure X} {s : Set (Set X)} [Fintype s] :
    My_Sum T μ 1 s = ∑ A ∈ s, μ A := by
  simp [My_Sum]
  sorry

lemma upper_bound_on_sum (T : X → X) (μ : Measure X) {n : ℕ} (hn : 1 ≤ n) (s : Set (Set X))
    [Fintype s] :
    My_Sum T μ n s ≤ (∑ A ∈ s, μ A) ^ n := by
  apply Nat.le_induction (m := 1) (P := fun n _ ↦ My_Sum T μ n s ≤ (∑ A ∈ s, μ A) ^ n) _ _ n hn
  · rw [My_Sum_one, pow_one]
  · intro n n_1 hin
    sorry

lemma lower_bound_on_sum (T : X → X) (F : Set X) (μ : Measure X) {n : ℕ} (hn : 1 ≤ n)
    (s : Set (Set X)) [Fintype s] (h : F ⊆ ⋃ A ∈ s, A) :
    (μ F) ^ n ≤ My_Sum T μ n s := by
  apply Nat.le_induction (m := 1) (P := fun n _ ↦ (μ F) ^ n ≤ My_Sum T μ n s) _ _ n hn
  · rw [pow_one, My_Sum_one, EReal.coe_ennreal_le_coe_ennreal_iff]
    apply (measure_mono h).trans
    sorry
  · intro n n_1 hin
    sorry

noncomputable def entropy_fun (x : ENNReal) : EReal := x * x.log

@[simp]
lemma entropy_fun_zero : entropy_fun 0 = 0 := by simp [entropy_fun]

@[simp]
lemma entropy_fun_one : entropy_fun 1 = 0 := by simp [entropy_fun]

lemma test_h {ι : Type*} [Fintype ι] (f : ι → ENNReal) :
    ∑ i, entropy_fun (f i) ≤ ENNReal.log (∑ i, f i) := by
  by_cases h : f = 0
  · simp [h]
    sorry
  simp only [not_exists] at h
  simp only [entropy_fun]
  sorry



end Dynamics
