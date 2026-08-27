/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Indistinguishable
public import Mathlib.Probability.Process.Filtration

public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace MeasureTheory.Filtration

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [Preorder ι]
  {P : Measure Ω} {𝓕 : Filtration ι mΩ} {X Y : ι → Ω → E}

section Def

variable [Zero E]

open scoped Classical in
/-- Given a process `X` and a filtration `𝓕`, if `X` converges to some `Y` almost everywhere and
`Y` is `⨆ t, 𝓕 t`-measurable, then `limitProcess X 𝓕 P` chooses said `Y`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `X` adapted to `𝓕`
converges to `limitProcess X 𝓕 P` `P`-almost everywhere. -/
noncomputable def limitProcess (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :=
  if h : ∃ g : Ω → E,
    StronglyMeasurable[⨆ t, 𝓕 t] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

lemma ae_tendsto_limitProcess_of_exists
    (h : ∃ g : Ω → E, StronglyMeasurable[⨆ t, 𝓕 t] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  rw [limitProcess, dite_eq_left h]
  exact h.choose_spec.2

theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ t, 𝓕 t] (limitProcess X 𝓕 P) := by
  rw [limitProcess]
  split_ifs with h
  exacts [h.choose_spec.1, stronglyMeasurable_zero]

theorem stronglyMeasurable_limit_process' : StronglyMeasurable[mΩ] (limitProcess X 𝓕 P) :=
  stronglyMeasurable_limitProcess.mono (iSup_le 𝓕.le)

theorem memLp_limitProcess_of_eLpNorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F]
    {𝓕 : Filtration ℕ mΩ} {X : ℕ → Ω → F} (hfm : ∀ n, AEStronglyMeasurable (X n) P)
    (hbdd : ∀ n, eLpNorm (X n) p P ≤ R) : MemLp (limitProcess X 𝓕 P) p P := by
  rw [limitProcess]
  split_ifs with h
  · refine ⟨StronglyMeasurable.aestronglyMeasurable
      ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ ↦ hn ▸ 𝓕.le _)),
      lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
        (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top : ↑R < ∞))⟩
    simp_rw [liminf_eq, eventually_atTop]
    exact sSup_le fun b ⟨a, ha⟩ ↦ (ha a le_rfl).trans (hbdd _)
  · exact MemLp.zero

end Def

variable [IsDirectedOrder ι] [Nonempty ι] [T2Space E]

section Basic

variable [Zero E]

/-- If `X` converges almost surely towards `g` a `⨆ t, 𝓕 t`-strongly measurable function,
then `g` is almost surely equal to `𝓕.limitProcess X P`. -/
lemma limitProcess_ae_eq {X : ι → Ω → E} {g : Ω → E}
    (mg : StronglyMeasurable[⨆ t, 𝓕 t] g) (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  have : ∃ g, StronglyMeasurable[⨆ t, 𝓕 t] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω)) :=
    ⟨g, mg, hg⟩
  rw [Filtration.limitProcess, dite_eq_left this]
  filter_upwards [hg, this.choose_spec.2] with ω h1 h2 using tendsto_nhds_unique h2 h1

omit [Nonempty ι] in
@[gcongr]
lemma limitProcess_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  obtain h | _ := isEmpty_or_nonempty ι
  · have : X = Y := by ext i; exact h.elim' i
    rw [this]
  rw [Filtration.limitProcess]
  split_ifs with h
  · symm
    apply limitProcess_ae_eq h.choose_spec.1
    filter_upwards [h.choose_spec.2, hXY] with ω h1 h2 using h1.congr h2
  rw [Filtration.limitProcess, dite_eq_right]
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨g, hg1, ?_⟩
  filter_upwards [hg2, hXY] with ω h1 h2 using h1.congr (fun t ↦ (h2 t).symm)

lemma limitProcess_const (c : E) :
    𝓕.limitProcess (fun _ _ ↦ c) P =ᵐ[P] (fun _ ↦ c) :=
  limitProcess_ae_eq stronglyMeasurable_const (by simp)

lemma limitProcess_zero :
    𝓕.limitProcess (0 : ι → Ω → E) P =ᵐ[P] 0 := limitProcess_const 0

end Basic

@[to_fun limitProcess_fun_smul]
lemma limitProcess_smul [Zero E] {R : Type*} [DivisionRing R] [MulActionWithZero R E]
    [ContinuousConstSMul R E] (X : ι → Ω → E) (c : R) :
    𝓕.limitProcess (c • X) P =ᵐ[P] c • 𝓕.limitProcess X P := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [limitProcess_zero]
  nth_rw 2 [Filtration.limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq (h.choose_spec.1.const_smul c)
    filter_upwards [h.choose_spec.2] with ω h1 using h1.const_smul c
  rw [Filtration.limitProcess, dite_eq_right]
  · simp
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨c⁻¹ • g, hg1.const_smul _, ?_⟩
  filter_upwards [hg2] with ω h1
  convert h1.const_smul c⁻¹
  · simp [hc]
  · simp

@[to_fun limitProcess_fun_neg]
lemma limitProcess_neg [AddGroup E] [ContinuousNeg E] (X : ι → Ω → E) :
    𝓕.limitProcess (-X) P =ᵐ[P] -𝓕.limitProcess X P := by
  nth_rw 2 [Filtration.limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq h.choose_spec.1.neg
    filter_upwards [h.choose_spec.2] with ω h1 using h1.neg
  rw [Filtration.limitProcess, dite_eq_right]
  · simp
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨-g, hg1.neg, ?_⟩
  filter_upwards [hg2] with ω h1
  simpa using h1.neg

end MeasureTheory.Filtration
