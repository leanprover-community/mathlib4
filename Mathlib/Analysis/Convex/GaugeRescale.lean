/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Gauge

open Bornology
open scoped NNReal Topology Filter

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

theorem gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gauge t (gaugeRescale s t x) = gauge s x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale, gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _)),
    smul_eq_mul, div_mul_cancel]
  exact ((gauge_pos hta htb).2 hx).ne'

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

theorem continuous_gaugeRescale (s t : Set E) : Continuous (gaugeRescale s t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · intro u hu
    
