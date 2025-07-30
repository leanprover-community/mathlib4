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

section aux

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [NontriviallyNormedField 𝕜] {E : ι → Type*}

lemma Isometry.single [∀ i, PseudoEMetricSpace (E i)] [∀ i, Zero (E i)] (i : ι) :
    Isometry (Pi.single (M := E) i) := by
  intro x y
  rw [edist_pi_def, Finset.sup_univ_eq_ciSup]
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

lemma ContinuousLinearMap.norm_single_le_one [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (i : ι) :
    ‖ContinuousLinearMap.single 𝕜 E i‖ ≤ 1 := by
  have : Isometry (ContinuousLinearMap.single 𝕜 E i).toLinearMap := Isometry.single i
  change
    ‖((ContinuousLinearMap.single 𝕜 E i).toLinearMap.toLinearIsometry
      this).toContinuousLinearMap‖ ≤ 1
  exact LinearIsometry.norm_toContinuousLinearMap_le _

lemma ContinuousLinearMap.norm_single [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (i : ι) [Nontrivial (E i)] :
    ‖ContinuousLinearMap.single 𝕜 E i‖ = 1 := by
  have : Isometry (ContinuousLinearMap.single 𝕜 E i).toLinearMap := Isometry.single i
  change
    ‖((ContinuousLinearMap.single 𝕜 E i).toLinearMap.toLinearIsometry
      this).toContinuousLinearMap‖ = 1
  exact LinearIsometry.norm_toContinuousLinearMap _

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    [AddZeroClass E] [AddZeroClass F]

lemma Isometry.inl : Isometry (AddMonoidHom.inl E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

lemma Isometry.inr : Isometry (AddMonoidHom.inr E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

end aux

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

lemma Measure.pi_map_eval [∀ i, SigmaFinite (μ i)] [DecidableEq ι] (i : ι) :
    (Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i) := by
  ext s hs
  classical
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi,
    Measure.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  simp [Function.update, Finset.ne_of_mem_erase hj]

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_eval_pi [∀ i, IsFiniteMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  simp_rw [← Function.eval_apply (x := i)]
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (fun _ _ ↦ measure_ne_top _ _)

lemma measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  exact fun _ _ ↦ measure_univ

lemma integral_eval_pi [NormedSpace ℝ E] [CompleteSpace E]
    [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E} (hf : AEStronglyMeasurable f (μ i)) :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  simp_rw [← Function.eval_apply (β := X) (x := i)]
  rw [← integral_map, (measurePreserving_eval i).map_eq]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval i).map_eq]

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
