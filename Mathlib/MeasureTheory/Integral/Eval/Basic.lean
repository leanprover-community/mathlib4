/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib

section aux

variable {ι : Type*} [Fintype ι]

lemma Isometry.single [DecidableEq ι] {E : ι → Type*}
    [∀ i, PseudoEMetricSpace (E i)]
    [∀ i, Zero (E i)] (i : ι) : Isometry (Pi.single (M := E) i) := by
  intro x y
  rw [edist_pi_def, Finset.sup_univ_eq_ciSup]
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

lemma ContinuousLinearMap.norm_single_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (i : ι) :
    ‖ContinuousLinearMap.single 𝕜 E i‖ ≤ 1 := by
  have : Isometry (ContinuousLinearMap.single 𝕜 E i).toLinearMap := Isometry.single i
  change
    ‖((ContinuousLinearMap.single 𝕜 E i).toLinearMap.toLinearIsometry
      this).toContinuousLinearMap‖ ≤ 1
  exact LinearIsometry.norm_toContinuousLinearMap_le _

lemma ContinuousLinearMap.norm_single {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (i : ι)
    [Nontrivial (E i)] :
    ‖ContinuousLinearMap.single 𝕜 E i‖ = 1 := by
  have : Isometry (ContinuousLinearMap.single 𝕜 E i).toLinearMap := Isometry.single i
  change
    ‖((ContinuousLinearMap.single 𝕜 E i).toLinearMap.toLinearIsometry
      this).toContinuousLinearMap‖ = 1
  exact LinearIsometry.norm_toContinuousLinearMap _

lemma Isometry.inl {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    [AddZeroClass E] [AddZeroClass F] : Isometry (AddMonoidHom.inl E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

lemma Isometry.inr {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    [AddZeroClass E] [AddZeroClass F] : Isometry (AddMonoidHom.inr E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

end aux

namespace MeasureTheory

open Finset

open scoped ENNReal

variable {ι Ω : Type*} {E : ι → Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

section Pi

variable {X : (i : ι) → Ω → E i}

lemma memLp_pi_iff : MemLp (fun ω ↦ (X · ω)) p P ↔ ∀ i, MemLp (X i) p P where
  mp hX i := by
    have : X i = (Function.eval i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
    rw [this]
    exact (LipschitzWith.eval i).comp_memLp (by simp) hX
  mpr hX := by
    classical
    have : (fun ω ↦ (X · ω)) = ∑ i, (Pi.single i) ∘ (X i) := by ext; simp
    rw [this]
    refine memLp_finset_sum' _ fun i _ ↦ ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hX i)

lemma memLp_prod_iff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : Ω → E} {Y : Ω → F} :
    MemLp (fun ω ↦ (X ω, Y ω)) p P ↔ MemLp X p P ∧ MemLp Y p P where
  mp h := by
    have h1 : X = Prod.fst ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
    have h2 : Y = Prod.snd ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
    rw [h1, h2]
    exact ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
      LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : (fun ω ↦ (X ω, Y ω)) = (AddMonoidHom.inl E F) ∘ X + (AddMonoidHom.inr E F) ∘ Y := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Isometry.inl.lipschitz.comp_memLp (by simp) h.1)
      (Isometry.inr.lipschitz.comp_memLp (by simp) h.2)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff

lemma integrable_pi_iff : Integrable (fun ω ↦ (X · ω)) P ↔ ∀ i, Integrable (X i) P := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma integral_eval (hX : ∀ i, Integrable (X i) P) (i : ι) :
    (∫ ω, (X · ω) ∂P) i = ∫ ω, X i ω ∂P := by
  rw [← ContinuousLinearMap.proj_apply (R := ℝ) i (∫ ω, (X · ω) ∂P),
    ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval hX

lemma Measure.pi_map_eval {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsFiniteMeasure (μ i)] [DecidableEq ι]
    (i : ι) :
    (Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i) := by
  ext s hs
  classical
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi,
    Measure.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  simp [Function.update, Finset.ne_of_mem_erase hj]

lemma integrable_eval_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] {X : ι → Type*} {i : ι}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsFiniteMeasure (μ i)] {f : X i → E} (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  simp_rw [← Function.eval_apply (x := i)]
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (fun _ _ ↦ measure_ne_top _ _)

lemma measurePreserving_eval {ι : Type*} [Fintype ι] {Ω : ι → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  exact fun _ _ ↦ measure_univ

lemma integral_eval_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {X : ι → Type*}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E} (hf : AEStronglyMeasurable f (μ i)) :
    ∫ (x : Π i, X i), f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  simp_rw [← Function.eval_apply (β := X) (x := i)]
  rw [← integral_map, (measurePreserving_eval i).map_eq]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval i).map_eq]

end Pi

section PiLp

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {X : Ω → PiLp q E}

lemma memLp_piLp_iff : MemLp X p P ↔ ∀ i, MemLp (X · i) p P := by
  simp_rw [← memLp_pi_iff, ← PiLp.ofLp_apply, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
    (PiLp.antilipschitzWith_ofLp q E) (by simp) |>.symm

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

lemma memLp_prodLp_iff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : Ω → WithLp q (E × F)} :
      MemLp X p P ↔
      MemLp (fun ω ↦ (X ω).fst) p P ∧
      MemLp (fun ω ↦ (X ω).snd) p P := by
  simp_rw [← memLp_prod_iff, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd,
    ← Function.comp_apply (f := WithLp.ofLp)]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
    (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp) |>.symm

alias ⟨MemLp.eval_prodLp, MemLp.of_eval_prodLp⟩ := memLp_prodLp_iff

lemma integrable_piLp_iff : Integrable X P ↔ ∀ i, Integrable (X · i) P := by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

variable [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]

lemma _root_.PiLp.integral_eval (hX : ∀ i, Integrable (X · i) P) (i : ι) :
    (∫ ω, X ω ∂P) i = ∫ ω, X ω i ∂P := by
  rw [← PiLp.proj_apply (𝕜 := ℝ) q E i (∫ ω, X ω ∂P), ← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hX

end PiLp

theorem fst_integral_withLp [Fact (1 ≤ p)] {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [CompleteSpace F] {f : X → WithLp p (E × F)} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv p ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, fst_integral]
  · rfl
  · simpa

theorem snd_integral_withLp [Fact (1 ≤ p)] {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [CompleteSpace E] {f : X → WithLp p (E × F)} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv p ℝ E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm, snd_integral]
  · rfl
  · simpa

end MeasureTheory
