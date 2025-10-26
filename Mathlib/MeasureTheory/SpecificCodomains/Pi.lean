/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability in a product space

We prove that `f : X → Π i, E i` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → (E × F)`.
-/

namespace MeasureTheory

open scoped ENNReal

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p : ℝ≥0∞}

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : X → Π i, E i}

lemma memLp_pi_iff : MemLp f p μ ↔ ∀ i, MemLp (f · i) p μ where
  mp hf i := (LipschitzWith.eval (α := E) i).comp_memLp rfl hf
  mpr hf := by
    classical
    have : f = ∑ i, (Pi.single i) ∘ (f · i) := by ext; simp
    rw [this]
    refine memLp_finset_sum' _ fun i _ ↦ ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff

lemma integrable_pi_iff : Integrable f μ ↔ ∀ i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma eval_integral (hf : ∀ i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  simp [← ContinuousLinearMap.proj_apply (R := ℝ) i (∫ x, f x ∂μ),
    ← ContinuousLinearMap.integral_comp_comm _ (Integrable.of_eval hf)]

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
