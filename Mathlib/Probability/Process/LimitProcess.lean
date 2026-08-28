/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Filtration

/-!

# Limit of a stochastic process

Under certain assumptions, classical familes of processes such as martingales converge as time
goes to infinity, and several important properties of the process can be inferred from this limit,
so that it is useful to be able to refer to this limit via a definition.
This file thus provides a definition `𝓕.limitProcess X P`, which is the limit of the process `X`
under the measure `P` with an ambient filtration `𝓕`. This is defined for any `X : ι → Ω → E`,
but of course it only makes sense if `X` converges. Moreover, in concrete use cases, `X` will
be strongly adapted to the filtration `𝓕`, so that the limit will be `⨆ t, 𝓕 t`-strongly measurable.
Therefore we define `𝓕.limitProcess X P` to be a `⨆ t, 𝓕 t`-strongly measurable almost everywhere
limit if it exists, and `0` otherwise.

This definition is for example used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `X` adapted to `𝓕`
converges to `limitProcess X 𝓕 P` `P`-almost everywhere.

In this file we provide the definition and prove basic preservation properties of the limit
under continuous maps.

Because several properties often rely on the fact that the limit exists, we also define a predicate
`HasLimitProcess X 𝓕 P` which states that `X` does converge `P`-almost surely towards a
`⨆ t, 𝓕 t`-strongly measurable function.

-/

public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace MeasureTheory.Filtration

variable {ι Ω E F G : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
  [TopologicalSpace F] [TopologicalSpace G] {P : Measure Ω} {𝓕 : Filtration ι mΩ}
  {X Y : ι → Ω → E} {Z : ι → Ω → F} {g : Ω → E}

section HasLimitProcess

/-! ### `HasLimitProcess` predicate -/

/-- A stochastic process `X` satisfies `𝓕.HasLimitProcess X P` if it converges `P`-almost surely
towards a `⨆ t, 𝓕 t`-strongly measurable random variable. -/
@[expose]
def HasLimitProcess (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ g : Ω → E, StronglyMeasurable[⨆ t, 𝓕 t] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))

lemma HasLimitProcess.congr (h : X ≡ᵐ[P] Y) (hX : HasLimitProcess X 𝓕 P) :
    HasLimitProcess Y 𝓕 P := by
  obtain ⟨g, mg, hg⟩ := hX
  refine ⟨g, mg, ?_⟩
  filter_upwards [h, hg] with ω h1 h2
  simp_all

lemma hasLimitProcess_congr_iff (h : X ≡ᵐ[P] Y) :
    HasLimitProcess X 𝓕 P ↔ HasLimitProcess Y 𝓕 P where
  mp h' := h'.congr h
  mpr h' := h'.congr h.symm

lemma HasLimitProcess.comp {f : E → F} (hX : HasLimitProcess X 𝓕 P) (hf : Continuous f) :
    HasLimitProcess (fun t ω ↦ f (X t ω)) 𝓕 P := by
  obtain ⟨g, mg, hg⟩ := hX
  refine ⟨f ∘ g, hf.comp_stronglyMeasurable mg, ?_⟩
  filter_upwards [hg] with ω h using (hf.tendsto _).comp h

lemma HasLimitProcess.comp₂ {f : E → F → G} (hX : HasLimitProcess X 𝓕 P)
    (hZ : HasLimitProcess Z 𝓕 P) (hf : Continuous f.uncurry) :
    HasLimitProcess (fun t ω ↦ f (X t ω) (Z t ω)) 𝓕 P := by
  obtain ⟨g, mg, hg⟩ := hX
  obtain ⟨h, mh, hh⟩ := hZ
  refine ⟨f.uncurry ∘ (Function.prod g h), hf.comp_stronglyMeasurable (mg.prodMk mh), ?_⟩
  filter_upwards [hg, hh] with ω h1 h2 using (hf.tendsto _).comp (h1.prodMk_nhds h2)

lemma HasLimitProcess.smul {R : Type*} [SMul R E] [ContinuousConstSMul R E] (c : R)
    (hX : HasLimitProcess X 𝓕 P) :
    HasLimitProcess (c • X) 𝓕 P :=
  hX.comp (continuous_const_smul c)

lemma hasLimitProcess_smul_iff {R : Type*} [DivisionRing R] [MulAction R E]
    [ContinuousConstSMul R E] {c : R} (hc : c ≠ 0) :
    HasLimitProcess (c • X) 𝓕 P ↔ HasLimitProcess X 𝓕 P where
  mp h := by
    convert h.comp (continuous_const_smul c⁻¹)
    simp [smul_smul, hc]
  mpr h := h.smul c

alias ⟨HasLimitProcess.of_smul, _⟩ := hasLimitProcess_smul_iff

lemma HasLimitProcess.neg [Neg E] [ContinuousNeg E] (hX : HasLimitProcess X 𝓕 P) :
    HasLimitProcess (-X) 𝓕 P :=
  hX.comp continuous_neg

lemma hasLimitProcess_neg_iff [InvolutiveNeg E] [ContinuousNeg E] :
    HasLimitProcess (-X) 𝓕 P ↔ HasLimitProcess X 𝓕 P where
  mp h := by
    convert h.comp continuous_neg
    simp
  mpr h := h.neg

alias ⟨HasLimitProcess.of_neg, _⟩ := hasLimitProcess_neg_iff

@[to_additive]
lemma HasLimitProcess.mul [Mul E] [ContinuousMul E] (hX : HasLimitProcess X 𝓕 P)
    (hY : HasLimitProcess Y 𝓕 P) :
    HasLimitProcess (X * Y) 𝓕 P :=
  hX.comp₂ hY continuous_mul

@[to_additive sub]
lemma HasLimitProcess.div' [Div E] [ContinuousDiv E] (hX : HasLimitProcess X 𝓕 P)
    (hY : HasLimitProcess Y 𝓕 P) :
    HasLimitProcess (X / Y) 𝓕 P :=
  hX.comp₂ hY continuous_div'

lemma HasLimitProcess.prodMk (hX : HasLimitProcess X 𝓕 P) (hZ : HasLimitProcess Z 𝓕 P) :
    HasLimitProcess (fun t ω ↦ (X t ω, Z t ω)) 𝓕 P :=
  hX.comp₂ hZ continuous_id

end HasLimitProcess

section limitProcess

/-! ### The limit of a process -/

section Def

variable [Zero E]

open scoped Classical in
/-- Given a process `X` and a filtration `𝓕`, if `X` converges to some `g` almost everywhere and
`g` is `⨆ t, 𝓕 t`-measurable (i.e. `HasLimitProcess X 𝓕 P` holds),
then `limitProcess X 𝓕 P` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `X` adapted to `𝓕`
converges to `limitProcess X 𝓕 P` `P`-almost everywhere. -/
noncomputable def limitProcess (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :=
  if h : 𝓕.HasLimitProcess X P then h.choose else 0

lemma HasLimitProcess.ae_tendsto_limitProcess (h : HasLimitProcess X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  rw [limitProcess, dite_eq_left h]
  exact h.choose_spec.2

theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ t, 𝓕 t] (limitProcess X 𝓕 P) := by
  rw [limitProcess]
  split_ifs with h
  exacts [h.choose_spec.1, stronglyMeasurable_zero]

theorem stronglyMeasurable_limit_process' : StronglyMeasurable[mΩ] (limitProcess X 𝓕 P) :=
  stronglyMeasurable_limitProcess.mono (iSup_le 𝓕.le)

end Def

section Preserved

variable [IsDirectedOrder ι] [Nonempty ι]

section Basic

variable [T2Space E] [Zero E]

/-- If `X` converges almost surely towards `g` a `⨆ t, 𝓕 t`-strongly measurable function,
then `g` is almost surely equal to `𝓕.limitProcess X P`. -/
lemma limitProcess_ae_eq (mg : StronglyMeasurable[⨆ t, 𝓕 t] g)
    (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  have : HasLimitProcess X 𝓕 P := ⟨g, mg, hg⟩
  rw [limitProcess, dite_eq_left this]
  filter_upwards [hg, this.choose_spec.2] with ω h1 h2 using tendsto_nhds_unique h2 h1

omit [Nonempty ι] in
@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  obtain h | _ := isEmpty_or_nonempty ι
  · have : X = Y := by ext i; exact h.elim' i
    rw [this]
  rw [limitProcess]
  split_ifs with h
  · symm
    apply limitProcess_ae_eq h.choose_spec.1
    filter_upwards [h.choose_spec.2, hXY] with ω h1 h2 using h1.congr h2
  · rw [limitProcess, dite_eq_right ((hasLimitProcess_congr_iff hXY).not.1 h)]

lemma limitProcess_const (c : E) :
    𝓕.limitProcess (fun _ _ ↦ c) P =ᵐ[P] (fun _ ↦ c) :=
  limitProcess_ae_eq stronglyMeasurable_const (by simp)

lemma limitProcess_zero :
    𝓕.limitProcess (0 : ι → Ω → E) P =ᵐ[P] 0 := limitProcess_const 0

end Basic

section Maps

variable {F G : Type*} [Zero F] [TopologicalSpace F] [Zero G] [TopologicalSpace G]

@[to_fun limitProcess_fun_comp]
lemma HasLimitProcess.limitProcess_comp [Zero E] [T2Space F] {f : E → F} (hf : Continuous f)
    (hX : HasLimitProcess X 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω)) P =ᵐ[P] f ∘ (𝓕.limitProcess X P) := by
  apply 𝓕.limitProcess_ae_eq (hf.comp_stronglyMeasurable 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess] with ω h using (hf.tendsto _).comp h

lemma HasLimitProcess.limitProcess_comp₂ [Zero E] [T2Space G] {f : E → F → G}
    (hf : Continuous f.uncurry) {Y : ι → Ω → F}
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ f (X t ω) (Y t ω)) P =ᵐ[P]
      fun ω ↦ f (𝓕.limitProcess X P ω) (𝓕.limitProcess Y P ω) := by
  apply 𝓕.limitProcess_ae_eq (hf.comp_stronglyMeasurable
    (𝓕.stronglyMeasurable_limitProcess.prodMk 𝓕.stronglyMeasurable_limitProcess))
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with
    ω h1 h2 using (hf.tendsto _).comp (h1.prodMk_nhds h2)

variable [T2Space E] [T2Space F]

@[to_fun limitProcess_fun_smul]
lemma limitProcess_smul [Zero E] {R : Type*} [DivisionRing R] [MulActionWithZero R E]
    [ContinuousConstSMul R E] (X : ι → Ω → E) (c : R) :
    𝓕.limitProcess (c • X) P =ᵐ[P] c • 𝓕.limitProcess X P := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [limitProcess_zero]
  nth_rw 2 [limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq (h.choose_spec.1.const_smul c)
    filter_upwards [h.choose_spec.2] with ω h1 using h1.const_smul c
  rw [limitProcess, dite_eq_right ((hasLimitProcess_smul_iff hc).not.2 h)]
  simp

@[to_fun limitProcess_fun_neg]
lemma limitProcess_neg [AddGroup E] [ContinuousNeg E] (X : ι → Ω → E) :
    𝓕.limitProcess (-X) P =ᵐ[P] -𝓕.limitProcess X P := by
  nth_rw 2 [limitProcess]
  split_ifs with h
  · apply limitProcess_ae_eq h.choose_spec.1.neg
    filter_upwards [h.choose_spec.2] with ω h1 using h1.neg
  rw [limitProcess, dite_eq_right]
  · simp
  contrapose h
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨-g, hg1.neg, ?_⟩
  filter_upwards [hg2] with ω h1
  simpa using h1.neg

@[to_fun (attr := to_additive) limitProcess_fun_mul]
lemma limitProcess_mul [Zero E] [Mul E] [ContinuousMul E]
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (X * Y) P =ᵐ[P] 𝓕.limitProcess X P * 𝓕.limitProcess Y P :=
  hX.limitProcess_comp₂ continuous_mul hY

@[to_fun limitProcess_fun_div']
lemma limitProcess_div' [Zero E] [Div E] [ContinuousDiv E]
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (X / Y) P =ᵐ[P] 𝓕.limitProcess X P / 𝓕.limitProcess Y P :=
  hX.limitProcess_comp₂ continuous_div' hY

attribute [to_additive limitProcess_sub] limitProcess_div'
attribute [to_additive limitProcess_fun_sub] limitProcess_fun_div'

lemma limitProcess_prodMk [Zero E] {Y : ι → Ω → F}
    (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.limitProcess (fun t ω ↦ (X t ω, Y t ω)) P =ᵐ[P]
      fun ω ↦ (𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω) :=
  hX.limitProcess_comp₂ (f := fun x y ↦ (x, y)) continuous_id hY

/-- If a stochastic process is bounded in `Lp` then its limit is in `Lp`. -/
theorem memLp_limitProcess_of_eLpNorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type*} [SeminormedAddGroup F]
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

end Maps

end Preserved

end limitProcess

end MeasureTheory.Filtration
