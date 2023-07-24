/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Gauge

open Bornology Filter Set
open scoped NNReal Topology

variable {E : Type _} [AddCommGroup E] [Module ℝ E]

noncomputable section

def gaugeRescale (s t : Set E) (x : E) : E := (gauge s x / gauge t x) • x

theorem gaugeRescale_def (s t : Set E) (x : E) :
    gaugeRescale s t x = (gauge s x / gauge t x) • x :=
  rfl

@[simp] theorem gaugeRescale_zero (s t : Set E) : gaugeRescale s t 0 = 0 := smul_zero _

theorem gaugeRescale_smul (s t : Set E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    gaugeRescale s t (c • x) = c • gaugeRescale s t x := by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm, mul_right_comm, div_self_mul_self]

variable [TopologicalSpace E] [T1Space E]

theorem gaugeRescale_self_apply {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (x : E) : gaugeRescale s s x = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale, div_self, one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'

theorem gaugeRescale_self {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s) :
    gaugeRescale s s = id :=
  funext <| gaugeRescale_self_apply hsa hsb

theorem gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E} (hx : gauge t x ≠ 0) :
    gauge t (gaugeRescale s t x) = gauge s x := by
  rw [gaugeRescale, gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _)),
    smul_eq_mul, div_mul_cancel _ hx]

theorem gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gauge t (gaugeRescale s t x) = gauge s x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'

theorem gauge_gaugeRescale_le (s t : Set E) (x : E) :
    gauge t (gaugeRescale s t x) ≤ gauge s x := by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

theorem gaugeRescale_gaugeRescale {s t u : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gaugeRescale t u (gaugeRescale s t x) = gaugeRescale s u x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x, gaugeRescale_smul, gaugeRescale, gaugeRescale, smul_smul,
    div_mul_div_cancel]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

def gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t) : E ≃ E where
  toFun := gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

variable [TopologicalAddGroup E] [ContinuousSMul ℝ E] {s t : Set E}

theorem mapsTo_gaugeRescale_interior (h₀ : t ∈ 𝓝 0) (hc : Convex ℝ t) :
    MapsTo (gaugeRescale s t) (interior s) (interior t) := fun x hx ↦ by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)

theorem mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (htc : Convex ℝ t) (ht₀ : 0 ∈ t) (hta : Absorbent ℝ t) :
    MapsTo (gaugeRescale s t) (closure s) (closure t) := fun _x hx ↦
  mem_closure_of_gauge_le_one htc ht₀ hta <| (gauge_gaugeRescale_le _ _ _).trans <|
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx

theorem continuous_gaugeRescale {s t : Set E} (hs : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (ht : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    Continuous (gaugeRescale s t) := by
  have hta : Absorbent ℝ t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, (· ∘ ·), gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

def gaugeRescaleHomeomorph (s t : Set E)
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) : E ≃ₜ E where
  toEquiv := gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption
