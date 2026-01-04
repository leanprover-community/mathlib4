/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Tactic.NormNum.NatFactorial

/-!
-/

@[expose] public section

section

lemma eq1 {α : Type*} {β : Type*} [SemilatticeInf α] [LinearOrder β] {s : Finset β}
    (hs : s.Nonempty) {f : β → α} (hf : Antitone f) : f (s.max' hs) = s.inf' hs f := by
  apply le_antisymm
  · exact s.le_inf' hs _ fun i hi ↦ hf (s.le_max' i hi)
  · exact s.inf'_le _ (s.max'_mem hs)

lemma eq2 {α : Type*} {β : Type*} [SemilatticeSup α] [LinearOrder β] {s : Finset β}
    (hs : s.Nonempty) {f : β → α} (hf : Antitone f) : f (s.min' hs) = s.sup' hs f := by
  apply le_antisymm
  · exact s.le_sup' _ (s.min'_mem hs)
  · exact s.sup'_le hs _ fun i hi ↦ hf (s.min'_le i hi)

end


open Set
open scoped BigOperators
open MeasureTheory

noncomputable section
namespace NumericalIntegration

lemma T1 {A B : ℝ} : (A + B) / 2 ∈ uIcc A B := by
  rw [mem_uIcc]
  by_cases h : A ≤ B
  · left
    exact ⟨by linarith, by linarith⟩
  · right
    exact ⟨by linarith, by linarith⟩

lemma useful {F : ℝ → ℝ} {h : ℝ} (x : ℝ) (hh : 0 < h) (hF : ContDiff ℝ 3 F) :
    ∃ ξ1 ∈ Ioo x (x + h), F (x + h) - (F x + h * deriv F x +
      1 / 2 * h ^ 2 * iteratedDeriv 2 F x) = iteratedDeriv 3 F ξ1 * h ^ 3 / 6 := by
  have hm : x < x + h := by simpa using (half_lt_self hh)
  have hm_mem : x ∈ Icc x (x + h) := ⟨le_rfl, le_of_lt hm⟩
  have hUD : UniqueDiffOn ℝ (Icc x (x + h)) := uniqueDiffOn_Icc hm
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (f := F) hm (by fun_prop)
  norm_num [sub_half] at hξ1_rem
  refine ⟨ξ1, hξ1, ?_⟩
  simp only [one_div, ← hξ1_rem, sub_right_inj]
  rw [(hF.contDiffAt.differentiableAt (by simp)).derivWithin (uniqueDiffOn_Icc hm x hm_mem),
    iteratedDerivWithin_eq_iteratedDeriv hUD ((hF.contDiffAt).of_le (by norm_num)) hm_mem]

theorem midpoint_aux {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (hF : ContDiff ℝ 3 F) :
    ∃ ξ ∈ Ioo (0 : ℝ) h, F h - F 0 - (deriv F (h/2)) * h = (h^3 / 24) * (iteratedDeriv 3 F ξ) := by
  have hm : h / 2 < h := by simpa using (half_lt_self hh)
  have hH : ContDiff ℝ 3 (fun x => F (h - x)) := by fun_prop
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ := useful (h/2) (half_pos hh) hF
  obtain ⟨ζ, hζ, hζ_rem⟩ := useful (F := fun x => F (h - x)) (h/2) (half_pos hh) (by fun_prop)
  obtain ⟨ξ, hξ_mem, hy⟩ : (iteratedDeriv 3 F ξ1 + iteratedDeriv 3 F (h - ζ)) / 2 ∈
    (iteratedDeriv 3 F) '' (uIcc ξ1 (h - ζ)) := intermediate_value_uIcc (by fun_prop) T1
  norm_num [-one_div, sub_half] at hξ1 hζ hξ1_rem hζ_rem
  have hξ0h : ξ ∈ Ioo (0:ℝ) h := by
    have : ξ ∈ Icc (min ξ1 (h - ζ)) (max ξ1 (h - ζ)) := by simpa [uIcc] using hξ_mem
    constructor
    · have lt : 0 < min ξ1 (h - ζ) := by simp [(half_pos hh).trans hξ1.1, hζ]
      linarith [this.1]
    · have lt : max ξ1 (h - ζ) < h := by simp [(half_pos hh).trans hζ.1, hξ1]
      linarith [this.2]
  refine ⟨ξ, hξ0h, ?_⟩
  calc
  _ = F h - (F (h/2) + h / 2 * deriv F (h/2) + 1 / 2 * (h/2) ^ 2 * iteratedDeriv 2 F (h/2))
      - (F 0 - (F (h/2) + h/2 * deriv (fun x ↦ F (h - x)) (h/2) +
      1 / 2 * (h/2) ^ 2 * iteratedDeriv 2 (fun x ↦ F (h - x)) (h/2))) := by
    simp [iteratedDeriv_comp_const_sub, deriv_comp_const_sub, sub_half, field]
    ring
  _ = h ^ 3 / 48 * iteratedDeriv 3 F ξ1 + h ^ 3 / 48 * iteratedDeriv 3 F (h - ζ) := by
    rw [hξ1_rem, hζ_rem]
    simpa [field, mul_assoc, iteratedDeriv_comp_const_sub] using by norm_num
  _ = _ := by grind

theorem midpoint_rule_error {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContDiff ℝ 2 f) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - f ((a + b) / 2) * (b - a)
      = (b - a)^3 / 24 * (iteratedDeriv 2 f ξ) := by
  set h : ℝ := b - a with hdef
  set g : ℝ → ℝ := fun x => f (x + a) with gdef
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hg : ContDiff ℝ 2 g := by fun_prop
  have hFderiv : deriv F = g := by
    funext x
    simpa [F] using hg.continuous.deriv_integral g 0 x
  have hFcont : ContDiff ℝ 3 F := (contDiff_succ_iff_deriv (n := 2) (f₂ := F)).2
      ⟨intervalIntegral.differentiable_integral_of_continuous hg.continuous, by simp,
      by simpa [hFderiv] using hg⟩
  rcases midpoint_aux (F := F) (sub_pos.mpr hab) hFcont with ⟨ξ0, hξ0, hEq⟩
  refine ⟨a + ξ0, by grind, ?_⟩
  have hDerivMid : deriv F (h / 2) = f ((a + b) / 2) := by
    simp [hFderiv, g, add_comm, hdef]
    ring_nf
  have hIter3 : iteratedDeriv 3 F ξ0 = iteratedDeriv 2 f (a + ξ0) := by calc
    _ = iteratedDeriv 2 (deriv F) ξ0 := congrArg (fun u ↦ u ξ0) iteratedDeriv_succ'
    _ = _ := by rw [hFderiv, gdef, iteratedDeriv_comp_add_const, add_comm]
  have hEq' : F h - deriv F (h / 2) * h = (h^3 / 24) * iteratedDeriv 3 F ξ0 := by
    simpa [F] using hEq
  have hFh : F h = (∫ x in a..b, f x) := by simp [F, g, h, add_comm]
  simpa only [hFh, hDerivMid, hIter3] using hEq'

end NumericalIntegration
