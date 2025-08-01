/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability in a product space

We prove that `f : (i : ι) → X → E i` is in `Lᵖ` if and only if for all `i`, `f i` is in `Lᵖ`.
We do the same for `f : X → (E × F)`.
-/

namespace MeasureTheory

open scoped ENNReal

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p : ℝ≥0∞}

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : (i : ι) → X → E i}

lemma memLp_pi_iff : MemLp (fun x ↦ (f · x)) p μ ↔ ∀ i, MemLp (f i) p μ where
  mp hf i := by
    have : f i = (Function.eval i) ∘ (fun x ↦ (f · x)) := by ext; simp
    rw [this]
    exact (LipschitzWith.eval i).comp_memLp (by simp) hf
  mpr hf := by
    classical
    have : (fun x ↦ (f · x)) = ∑ i, (Pi.single i) ∘ (f i) := by ext; simp
    rw [this]
    refine memLp_finset_sum' _ fun i _ ↦ ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff

lemma integrable_pi_iff : Integrable (fun x ↦ (f · x)) μ ↔ ∀ i, Integrable (f i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma eval_integral (hf : ∀ i, Integrable (f i) μ) (i : ι) :
    (∫ x, (f · x) ∂μ) i = ∫ x, f i x ∂μ := by
  rw [← ContinuousLinearMap.proj_apply (R := ℝ) i (∫ x, (f · x) ∂μ),
    ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval hf

variable {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    {E : Type*} [NormedAddCommGroup E]

lemma integrable_eval_pi [∀ i, IsFiniteMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  simp_rw [← Function.eval_apply (x := i)]
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (fun _ _ ↦ measure_ne_top _ _)

lemma integral_eval_pi [NormedSpace ℝ E] [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : AEStronglyMeasurable f (μ i)) :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  simp_rw [← Function.eval_apply (β := X) (x := i)]
  rw [← integral_map, (measurePreserving_eval μ i).map_eq]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X → E × F}

lemma memLp_prod_iff :
    MemLp f p μ ↔ MemLp (fun x ↦ (f x).fst) p μ ∧ MemLp (fun x ↦ (f x).snd) p μ where
  mp h := ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
    LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : f = (AddMonoidHom.inl E F) ∘ (fun x ↦ (f x).fst) +
        (AddMonoidHom.inr E F) ∘ (fun x ↦ (f x).snd) := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Isometry.inl.lipschitz.comp_memLp (by simp) h.1)
      (Isometry.inr.lipschitz.comp_memLp (by simp) h.2)

lemma MemLp.fst (h : MemLp f p μ) : MemLp (fun x ↦ (f x).fst) p μ :=
  memLp_prod_iff.1 h |>.1

lemma MemLp.snd (h : MemLp f p μ) : MemLp (fun x ↦ (f x).snd) p μ :=
  memLp_prod_iff.1 h |>.2

alias ⟨_, MemLp.of_fst_snd⟩ := memLp_prod_iff

end Prod

end MeasureTheory
