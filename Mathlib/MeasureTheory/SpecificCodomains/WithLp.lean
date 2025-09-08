/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrability in `WithLp`

We prove that `f : X → PiLp q E` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → WithLp q (E × F)`.
-/

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p q : ℝ≥0∞} [Fact (1 ≤ q)]

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {f : X → PiLp q E}

lemma memLp_piLp_iff : MemLp f p μ ↔ ∀ i, MemLp (f · i) p μ := by
  simp_rw [← PiLp.ofLp_apply, ← memLp_pi_iff, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
    (PiLp.antilipschitzWith_ofLp q E) (by simp) |>.symm

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

lemma integrable_piLp_iff : Integrable f μ ↔ ∀ i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma eval_integral_piLp (hf : ∀ i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  rw [← PiLp.proj_apply (𝕜 := ℝ) q E i (∫ x, f x ∂μ), ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hf

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X → WithLp q (E × F)}

lemma memLp_prodLp_iff :
    MemLp f p μ ↔ MemLp (fun x ↦ (f x).fst) p μ ∧ MemLp (fun x ↦ (f x).snd) p μ := by
  simp_rw [← memLp_prod_iff]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
    (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp) |>.symm

lemma MemLp.prodLp_fst (h : MemLp f p μ) : MemLp (fun x ↦ (f x).fst) p μ :=
  memLp_prodLp_iff.1 h |>.1

lemma MemLp.prodLp_snd (h : MemLp f p μ) : MemLp (fun x ↦ (f x).snd) p μ :=
  memLp_prodLp_iff.1 h |>.2

alias ⟨_, MemLp.of_fst_of_snd_prodLp⟩ := memLp_prodLp_iff

lemma integrable_prodLp_iff :
    Integrable f μ ↔
    Integrable (fun x ↦ (f x).fst) μ ∧
    Integrable (fun x ↦ (f x).snd) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_prodLp_iff]

lemma Integrable.prodLp_fst (h : Integrable f μ) : Integrable (fun x ↦ (f x).fst) μ :=
  integrable_prodLp_iff.1 h |>.1

lemma Integrable.prodLp_snd (h : Integrable f μ) : Integrable (fun x ↦ (f x).snd) μ :=
  integrable_prodLp_iff.1 h |>.2

alias ⟨_, Integrable.of_fst_of_snd_prodLp⟩ := integrable_prodLp_iff

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem fst_integral_withLp [CompleteSpace F] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).fst = ∫ x, (f x).fst ∂μ := by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, fst_integral]
  · rfl
  · simpa

theorem snd_integral_withLp [CompleteSpace E] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).snd = ∫ x, (f x).snd ∂μ := by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, snd_integral]
  · rfl
  · simpa

end Prod

end MeasureTheory
