/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.Holder

/-!
# Pull-out property of the conditional expectation

Let `Ω` be endowed with a measurable space structure `mΩ`, and let `m : MeasurableSpace Ω` such that
`m ≤ mΩ`. Let `μ` be a measure over `Ω`. Let `B : F →L[ℝ] E →L[ℝ] G` a continuous bilinear map,
`f : Ω → F` and `g : Ω → E` such that `fun ω ↦ B (f ω) (g ω)` is integrable, `g` is integrable
and `f` is `AEStronglyMeasurable` with respect to `m`. The **pull-out** property of the conditional
expectation states that almost surely, `μ[B f g|m] = B f μ[g|m]`.

We specialize this statement to the cases where `B` is scalar multiplication and multiplication.

# Main statements

* `condExp_bilin_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[B f g|m] = B f μ[g|m]`.
* `condExp_smul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f • g|m] = f • μ[g|m]`.
* `condExp_mul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f * g|m] = f * μ[g|m]`.

# Tags

conditional expectation, pull-out, bilinear map
-/

public section


open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] (B : F →L[ℝ] E →L[ℝ] G)

/-- Auxiliary lemma for `condExp_bilin_of_stronglyMeasurable_left`. -/
theorem condExp_stronglyMeasurable_simpleFunc_bilin [CompleteSpace E]
    (hm : m ≤ mΩ) (f : @SimpleFunc Ω m F) {g : Ω → E} (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := by
  have : ∀ (s c) (f : Ω → E),
      (fun ω ↦ B (Set.indicator s (Function.const Ω c) ω) (f ω)) =
        s.indicator (fun ω ↦ B c (f ω)) := by
    intro s c f
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f ↦ _)
    (fun c s hs ↦ ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ ↦ ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this, this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun ω ↦ B (g₁ ω + g₂ ω) (g ω)|m] =ᵐ[μ]
          μ[fun ω ↦ B (g₁ ω) (g ω)|m] + μ[fun ω ↦ B (g₂ ω) (g ω)|m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₂
        exact condExp_add
          (B.integrable_of_bilin_of_bdd_left C₁ (g₁.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₁) hg)
          (B.integrable_of_bilin_of_bdd_left C₂ (g₂.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₂) hg) m
      _ =ᵐ[μ] fun ω ↦ B (g₁ ω) (μ[g|m] ω) + B (g₂ ω) (μ[g|m] ω) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun ω ↦ B ((g₁ + g₂) ω) (μ[g|m] ω) := by simp

theorem condExp_stronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → F} {g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ ω ∂μ, Tendsto (fs · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hf_bound.exists with ⟨_, h⟩
    exact (norm_nonneg _).trans h
  have hfs_bound : ∀ n ω, ‖fs n ω‖ ≤ c := hf.norm_approxBounded_le hc
  have : μ[fun ω ↦ B (f ω) (μ[g|m] ω)|m] = fun ω ↦ B (f ω) (μ[g|m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n ω ↦ B (fs n ω) (g ω))
    (fun n ω ↦ B (fs n ω) (μ[g|m] ω)) (fun ω ↦ B (f ω) (g ω))
    (fun ω ↦ B (f ω) (μ[g|m] ω)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g|m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x ↦ B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x ↦ B x (μ[g|m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n ↦ Eventually.of_forall fun _ ↦ ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n ↦ Eventually.of_forall fun _ ↦ ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp

theorem condExp_aestronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → F} {g : Ω → E} (hf : AEStronglyMeasurable[m] f μ)
    (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := calc
  μ[fun ω ↦ B (f ω) (g ω)|m]
  _ =ᵐ[μ] μ[fun ω ↦ B (hf.mk f ω) (g ω)|m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω ↦ B (hf.mk f ω) (μ[g|m] ω) := by
    refine condExp_stronglyMeasurable_bilin_of_bound B hm hf.stronglyMeasurable_mk
      hg c ?_
    filter_upwards [hf_bound, hf.ae_eq_mk] with ω hω1 hω2
    rwa [← hω2]
  _ =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := by
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_stronglyMeasurable_left [CompleteSpace E] {f : Ω → F} {g : Ω → E}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ)
    (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := by
  by_cases hm : m ≤ mΩ; swap; · exact ae_of_all _ <| by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · exact ae_of_all _ <| by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices ∀ n, ∀ᵐ ω ∂μ, ω ∈ sets n → (μ[fun ω ↦ B (f ω) (g ω)|m]) ω = B (f ω) (μ[g|m] ω) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with ω hω
    obtain ⟨i, hi⟩ : ∃ i, ω ∈ sets i := by
      have h_mem : ω ∈ ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hω i hi
  refine fun n ↦ ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ.restrict (sets n)]
      fun ω ↦ B (f ω) ((μ.restrict (sets n))[g|m] ω) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with ω hω1 hω2
    rw [hω1, hω2]
  suffices (μ.restrict (sets n))[fun ω ↦ B ((sets n).indicator f ω) (g ω)|m] =ᵐ[μ.restrict (sets n)]
      fun ω ↦ B ((sets n).indicator f ω) ((μ.restrict (sets n))[g|m] ω) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with ω
  by_cases hωs : ω ∈ sets n <;> simp [hωs, h_norm]

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_stronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_aestronglyMeasurable_left [CompleteSpace E]
    {f : Ω → F} {g : Ω → E} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω)|m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := calc
  μ[fun ω ↦ B (f ω) (g ω)|m]
  _ =ᵐ[μ] μ[fun ω ↦ B (hf.mk f ω) (g ω)|m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω ↦ B (hf.mk f ω) (μ[g|m] ω) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
  _ =ᵐ[μ] fun ω ↦ B (f ω) (μ[g|m] ω) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_smul_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ) :
    μ[f • g|m] =ᵐ[μ] f • μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.lsmul ℝ ℝ) hf hfg hg

/-- Pull-out property of the conditional expectation. -/
theorem condExp_smul_of_aestronglyMeasurable_right [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : Integrable f μ) (hfg : Integrable (f • g) μ) (hg : AEStronglyMeasurable[m] g μ) :
    μ[f • g|m] =ᵐ[μ] μ[f|m] • g :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.lsmul ℝ ℝ).flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_aestronglyMeasurable_left {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul ℝ ℝ) hf hfg hg

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_aestronglyMeasurable_right {f g : Ω → ℝ} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul ℝ ℝ) hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_stronglyMeasurable_left {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul ℝ ℝ)
    hf.aestronglyMeasurable hfg hg

/-- Pull-out property of the conditional expectation. -/
lemma condExp_mul_of_stronglyMeasurable_right {f g : Ω → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul ℝ ℝ)
    hg.aestronglyMeasurable hfg hf

theorem condExp_stronglyMeasurable_simpleFunc_mul (hm : m ≤ mΩ) (f : @SimpleFunc Ω m ℝ) {g : Ω → ℝ}
    (hg : Integrable g μ) : μ[(f * g : Ω → ℝ)|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_stronglyMeasurable_simpleFunc_bilin (.mul ℝ ℝ) hm f hg

theorem condExp_stronglyMeasurable_mul_of_bound (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℝ) hm hf hg c hf_bound

theorem condExp_stronglyMeasurable_mul_of_bound₀ (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable[m] f μ) (hg : Integrable g μ) (c : ℝ)
    (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_aestronglyMeasurable_bilin_of_bound (.mul ℝ ℝ) hm hf hg c hf_bound

end MeasureTheory
