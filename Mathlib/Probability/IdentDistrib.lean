/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Function.UniformIntegrable

#align_import probability.ident_distrib from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Identically distributed random variables

Two random variables defined on two (possibly different) probability spaces but taking value in
the same space are *identically distributed* if their distributions (i.e., the image probability
measures on the target space) coincide. We define this concept and establish its basic properties
in this file.

## Main definitions and results

* `IdentDistrib f g μ ν` registers that the image of `μ` under `f` coincides with the image of `ν`
  under `g` (and that `f` and `g` are almost everywhere measurable, as otherwise the image measures
  don't make sense). The measures can be kept implicit as in `IdentDistrib f g` if the spaces
  are registered as measure spaces.
* `IdentDistrib.comp`: being identically distributed is stable under composition with measurable
  maps.

There are two main kinds of lemmas, under the assumption that `f` and `g` are identically
distributed: lemmas saying that two quantities computed for `f` and `g` are the same, and lemmas
saying that if `f` has some property then `g` also has it. The first kind is registered as
`IdentDistrib.foo_fst`, the second one as `IdentDistrib.foo_snd` (in the latter case, to deduce
a property of `f` from one of `g`, use `h.symm.foo_snd` where `h : IdentDistrib f g μ ν`). For
instance:

* `IdentDistrib.measure_mem_eq`: if `f` and `g` are identically distributed, then the probabilities
  that they belong to a given measurable set are the same.
* `IdentDistrib.integral_eq`: if `f` and `g` are identically distributed, then their integrals
  are the same.
* `IdentDistrib.variance_eq`: if `f` and `g` are identically distributed, then their variances
  are the same.

* `IdentDistrib.aestronglyMeasurable_snd`: if `f` and `g` are identically distributed and `f`
  is almost everywhere strongly measurable, then so is `g`.
* `IdentDistrib.memℒp_snd`: if `f` and `g` are identically distributed and `f`
  belongs to `ℒp`, then so does `g`.

We also register several dot notation shortcuts for convenience.
For instance, if `h : IdentDistrib f g μ ν`, then `h.sq` states that `f^2` and `g^2` are
identically distributed, and `h.norm` states that `‖f‖` and `‖g‖` are identically distributed, and
so on.
-/


open MeasureTheory Filter Finset

noncomputable section

open scoped Topology BigOperators MeasureTheory ENNReal NNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory

/-- Two functions defined on two (possibly different) measure spaces are identically distributed if
their image measures coincide. This only makes sense when the functions are ae measurable
(as otherwise the image measures are not defined), so we require this as well in the definition. -/
structure IdentDistrib (f : α → γ) (g : β → γ)
    (μ : Measure α := by volume_tac)
    (ν : Measure β := by volume_tac) : Prop where
  aemeasurable_fst : AEMeasurable f μ
  aemeasurable_snd : AEMeasurable g ν
  map_eq : Measure.map f μ = Measure.map g ν
#align probability_theory.ident_distrib ProbabilityTheory.IdentDistrib

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

protected theorem refl (hf : AEMeasurable f μ) : IdentDistrib f f μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }
#align probability_theory.ident_distrib.refl ProbabilityTheory.IdentDistrib.refl

protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
  { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }
#align probability_theory.ident_distrib.symm ProbabilityTheory.IdentDistrib.symm

protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν)
    (h₂ : IdentDistrib g h ν ρ) : IdentDistrib f h μ ρ :=
  { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }
#align probability_theory.ident_distrib.trans ProbabilityTheory.IdentDistrib.trans

protected theorem comp_of_aemeasurable {u : γ → δ} (h : IdentDistrib f g μ ν)
    (hu : AEMeasurable u (Measure.map f μ)) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
                           -- ⊢ AEMeasurable (u ∘ g)
                                                -- 🎉 no goals
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst, ←
        AEMeasurable.map_map_of_aemeasurable _ h.aemeasurable_snd, h.map_eq]
      rwa [← h.map_eq] }
      -- 🎉 no goals
#align probability_theory.ident_distrib.comp_of_ae_measurable ProbabilityTheory.IdentDistrib.comp_of_aemeasurable

protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
    IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  h.comp_of_aemeasurable hu.aemeasurable
#align probability_theory.ident_distrib.comp ProbabilityTheory.IdentDistrib.comp

protected theorem of_ae_eq {g : α → γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g) :
    IdentDistrib f g μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }
#align probability_theory.ident_distrib.of_ae_eq ProbabilityTheory.IdentDistrib.of_ae_eq

theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs, ←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs, h.map_eq]
#align probability_theory.ident_distrib.measure_mem_eq ProbabilityTheory.IdentDistrib.measure_mem_eq

alias measure_preimage_eq := measure_mem_eq
#align probability_theory.ident_distrib.measure_preimage_eq ProbabilityTheory.IdentDistrib.measure_preimage_eq

theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ → Prop} (pmeas : MeasurableSet {x | p x})
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  -- ⊢ ∀ᵐ (y : γ) ∂Measure.map g ν, p y
  rw [← h.map_eq]
  -- ⊢ ∀ᵐ (y : γ) ∂Measure.map f μ, p y
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp
  -- 🎉 no goals
#align probability_theory.ident_distrib.ae_snd ProbabilityTheory.IdentDistrib.ae_snd

theorem ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t)
    (ht : ∀ᵐ x ∂μ, f x ∈ t) : ∀ᵐ x ∂ν, g x ∈ t :=
  h.ae_snd tmeas ht
#align probability_theory.ident_distrib.ae_mem_snd ProbabilityTheory.IdentDistrib.ae_mem_snd

/-- In a second countable topology, the first function in an identically distributed pair is a.e.
strongly measurable. So is the second function, but use `h.symm.aestronglyMeasurable_fst` as
`h.aestronglyMeasurable_snd` has a different meaning.-/
theorem aestronglyMeasurable_fst [TopologicalSpace γ] [MetrizableSpace γ] [OpensMeasurableSpace γ]
    [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ :=
  h.aemeasurable_fst.aestronglyMeasurable
#align probability_theory.ident_distrib.ae_strongly_measurable_fst ProbabilityTheory.IdentDistrib.aestronglyMeasurable_fst

/-- If `f` and `g` are identically distributed and `f` is a.e. strongly measurable, so is `g`. -/
theorem aestronglyMeasurable_snd [TopologicalSpace γ] [MetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable g ν := by
  refine' aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, _⟩
  -- ⊢ ∃ t, IsSeparable t ∧ ∀ᵐ (x : β) ∂ν, g x ∈ t
  rcases(aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  -- ⊢ ∃ t, IsSeparable t ∧ ∀ᵐ (x : β) ∂ν, g x ∈ t
  refine' ⟨closure t, t_sep.closure, _⟩
  -- ⊢ ∀ᵐ (x : β) ∂ν, g x ∈ closure t
  apply h.ae_mem_snd isClosed_closure.measurableSet
  -- ⊢ ∀ᵐ (x : α) ∂μ, f x ∈ closure t
  filter_upwards [ht] with x hx using subset_closure hx
  -- 🎉 no goals
#align probability_theory.ident_distrib.ae_strongly_measurable_snd ProbabilityTheory.IdentDistrib.aestronglyMeasurable_snd

theorem aestronglyMeasurable_iff [TopologicalSpace γ] [MetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g ν :=
  ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩
#align probability_theory.ident_distrib.ae_strongly_measurable_iff ProbabilityTheory.IdentDistrib.aestronglyMeasurable_iff

theorem essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : ∀ a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]
  -- 🎉 no goals
#align probability_theory.ident_distrib.ess_sup_eq ProbabilityTheory.IdentDistrib.essSup_eq

theorem lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν := by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  -- ⊢ ∫⁻ (x : α), id (f x) ∂μ = ∫⁻ (x : β), id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst, ←
    lintegral_map' aemeasurable_id h.aemeasurable_snd, h.map_eq]
#align probability_theory.ident_distrib.lintegral_eq ProbabilityTheory.IdentDistrib.lintegral_eq

theorem integral_eq [NormedAddCommGroup γ] [NormedSpace ℝ γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν := by
  by_cases hf : AEStronglyMeasurable f μ
  -- ⊢ ∫ (x : α), f x ∂μ = ∫ (x : β), g x ∂ν
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases(aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine' ⟨aemeasurable_id, ⟨closure t, t_sep.closure, _⟩⟩
      rw [ae_map_iff h.aemeasurable_fst]
      · filter_upwards [ht] with x hx using subset_closure hx
      · exact isClosed_closure.measurableSet
    change ∫ x, id (f x) ∂μ = ∫ x, id (g x) ∂ν
    -- ⊢ ∫ (x : α), id (f x) ∂μ = ∫ (x : β), id (g x) ∂ν
    rw [← integral_map h.aemeasurable_fst A]
    -- ⊢ ∫ (y : γ), id y ∂Measure.map f μ = ∫ (x : β), id (g x) ∂ν
    rw [h.map_eq] at A
    -- ⊢ ∫ (y : γ), id y ∂Measure.map f μ = ∫ (x : β), id (g x) ∂ν
    rw [← integral_map h.aemeasurable_snd A, h.map_eq]
    -- 🎉 no goals
  · rw [integral_non_aestronglyMeasurable hf]
    -- ⊢ 0 = ∫ (x : β), g x ∂ν
    rw [h.aestronglyMeasurable_iff] at hf
    -- ⊢ 0 = ∫ (x : β), g x ∂ν
    rw [integral_non_aestronglyMeasurable hf]
    -- 🎉 no goals
#align probability_theory.ident_distrib.integral_eq ProbabilityTheory.IdentDistrib.integral_eq

theorem snorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
    (p : ℝ≥0∞) : snorm f p μ = snorm g p ν := by
  by_cases h0 : p = 0
  -- ⊢ snorm f p μ = snorm g p ν
  · simp [h0]
    -- 🎉 no goals
  by_cases h_top : p = ∞
  -- ⊢ snorm f p μ = snorm g p ν
  · simp only [h_top, snorm, snormEssSup, ENNReal.top_ne_zero, eq_self_iff_true, if_true, if_false]
    -- ⊢ essSup (fun x => ↑‖f x‖₊) μ = essSup (fun x => ↑‖g x‖₊) ν
    apply essSup_eq
    -- ⊢ IdentDistrib (fun x => ↑‖f x‖₊) fun x => ↑‖g x‖₊
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
    -- 🎉 no goals
  simp only [snorm_eq_snorm' h0 h_top, snorm', one_div]
  -- ⊢ (∫⁻ (a : α), ↑‖f a‖₊ ^ ENNReal.toReal p ∂μ) ^ (ENNReal.toReal p)⁻¹ = (∫⁻ (a  …
  congr 1
  -- ⊢ ∫⁻ (a : α), ↑‖f a‖₊ ^ ENNReal.toReal p ∂μ = ∫⁻ (a : β), ↑‖g a‖₊ ^ ENNReal.to …
  apply lintegral_eq
  -- ⊢ IdentDistrib (fun x => ↑‖f x‖₊ ^ ENNReal.toReal p) fun x => ↑‖g x‖₊ ^ ENNRea …
  exact h.comp (Measurable.pow_const (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
    p.toReal)
#align probability_theory.ident_distrib.snorm_eq ProbabilityTheory.IdentDistrib.snorm_eq

theorem memℒp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν)
    (hf : Memℒp f p μ) : Memℒp g p ν := by
  refine' ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, _⟩
  -- ⊢ snorm g p ν < ⊤
  rw [← h.snorm_eq]
  -- ⊢ snorm f p μ < ⊤
  exact hf.2
  -- 🎉 no goals
#align probability_theory.ident_distrib.mem_ℒp_snd ProbabilityTheory.IdentDistrib.memℒp_snd

theorem memℒp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    Memℒp f p μ ↔ Memℒp g p ν :=
  ⟨fun hf => h.memℒp_snd hf, fun hg => h.symm.memℒp_snd hg⟩
#align probability_theory.ident_distrib.mem_ℒp_iff ProbabilityTheory.IdentDistrib.memℒp_iff

theorem integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : Integrable f μ) : Integrable g ν := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  -- ⊢ Memℒp g 1
  exact h.memℒp_snd hf
  -- 🎉 no goals
#align probability_theory.ident_distrib.integrable_snd ProbabilityTheory.IdentDistrib.integrable_snd

theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩
#align probability_theory.ident_distrib.integrable_iff ProbabilityTheory.IdentDistrib.integrable_iff

protected theorem norm [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖) (fun x => ‖g x‖) μ ν :=
  h.comp measurable_norm
#align probability_theory.ident_distrib.norm ProbabilityTheory.IdentDistrib.norm

protected theorem nnnorm [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖₊) (fun x => ‖g x‖₊) μ ν :=
  h.comp measurable_nnnorm
#align probability_theory.ident_distrib.nnnorm ProbabilityTheory.IdentDistrib.nnnorm

protected theorem pow [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) {n : ℕ} :
    IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν :=
  h.comp (measurable_id.pow_const n)
#align probability_theory.ident_distrib.pow ProbabilityTheory.IdentDistrib.pow

protected theorem sq [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν :=
  h.comp (measurable_id.pow_const 2)
#align probability_theory.ident_distrib.sq ProbabilityTheory.IdentDistrib.sq

protected theorem coe_nnreal_ennreal {f : α → ℝ≥0} {g : β → ℝ≥0} (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => (f x : ℝ≥0∞)) (fun x => (g x : ℝ≥0∞)) μ ν :=
  h.comp measurable_coe_nnreal_ennreal
#align probability_theory.ident_distrib.coe_nnreal_ennreal ProbabilityTheory.IdentDistrib.coe_nnreal_ennreal

@[to_additive]
theorem mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x * c) (fun x => g x * c) μ ν :=
  h.comp (measurable_mul_const c)
#align probability_theory.ident_distrib.mul_const ProbabilityTheory.IdentDistrib.mul_const
#align probability_theory.ident_distrib.add_const ProbabilityTheory.IdentDistrib.add_const

@[to_additive]
theorem const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c * f x) (fun x => c * g x) μ ν :=
  h.comp (measurable_const_mul c)
#align probability_theory.ident_distrib.const_mul ProbabilityTheory.IdentDistrib.const_mul
#align probability_theory.ident_distrib.const_add ProbabilityTheory.IdentDistrib.const_add

@[to_additive]
theorem div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x / c) (fun x => g x / c) μ ν :=
  h.comp (MeasurableDiv.measurable_div_const c)
#align probability_theory.ident_distrib.div_const ProbabilityTheory.IdentDistrib.div_const
#align probability_theory.ident_distrib.sub_const ProbabilityTheory.IdentDistrib.sub_const

@[to_additive]
theorem const_div [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c / f x) (fun x => c / g x) μ ν :=
  h.comp (MeasurableDiv.measurable_const_div c)
#align probability_theory.ident_distrib.const_div ProbabilityTheory.IdentDistrib.const_div
#align probability_theory.ident_distrib.const_sub ProbabilityTheory.IdentDistrib.const_sub

theorem evariance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    evariance f μ = evariance g ν := by
  convert (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  -- ⊢ evariance g ν = ∫⁻ (x : β), ↑‖g x - ∫ (x : α), f x ∂μ‖₊ ^ 2 ∂ν
  rw [h.integral_eq]
  -- ⊢ evariance g ν = ∫⁻ (x : β), ↑‖g x - ∫ (x : β), g x ∂ν‖₊ ^ 2 ∂ν
  rfl
  -- 🎉 no goals
#align probability_theory.ident_distrib.evariance_eq ProbabilityTheory.IdentDistrib.evariance_eq

theorem variance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    variance f μ = variance g ν := by rw [variance, h.evariance_eq]; rfl
                                      -- ⊢ ENNReal.toReal (evariance g ν) = variance g ν
                                                                     -- 🎉 no goals
#align probability_theory.ident_distrib.variance_eq ProbabilityTheory.IdentDistrib.variance_eq

end IdentDistrib

section UniformIntegrable

open TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure α} [IsFiniteMeasure μ]

/-- This lemma is superseded by `Memℒp.uniformIntegrable_of_identDistrib` which only requires
`AEStronglyMeasurable`. -/
theorem Memℒp.uniformIntegrable_of_identDistrib_aux {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : Memℒp (f j) p μ) (hfmeas : ∀ i, StronglyMeasurable (f i))
    (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  refine' uniformIntegrable_of' hp hp' hfmeas fun ε hε => _
  -- ⊢ ∃ C, ∀ (i : ι), snorm (Set.indicator {x | C ≤ ‖f i x‖₊} (f i)) p μ ≤ ENNReal …
  by_cases hι : Nonempty ι
  -- ⊢ ∃ C, ∀ (i : ι), snorm (Set.indicator {x | C ≤ ‖f i x‖₊} (f i)) p μ ≤ ENNReal …
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  -- ⊢ ∃ C, ∀ (i : ι), snorm (Set.indicator {x | C ≤ ‖f i x‖₊} (f i)) p μ ≤ ENNReal …
          -- 🎉 no goals
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.snorm_indicator_norm_ge_pos_le μ (hfmeas _) hε
  -- ⊢ ∃ C, ∀ (i : ι), snorm (Set.indicator {x | C ≤ ‖f i x‖₊} (f i)) p μ ≤ ENNReal …
  refine' ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq _) hC₂⟩
  -- ⊢ snorm (Set.indicator {x | { val := C, property := (_ : 0 ≤ C) } ≤ ‖f i x‖₊}  …
  have : {x : α | (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖f i x‖₊}.indicator (f i) =
      (fun x : E => if (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖x‖₊ then x else 0) ∘ f i := by
    ext x
    simp only [Set.indicator, Set.mem_setOf_eq]; norm_cast
  simp_rw [coe_nnnorm, this]
  -- ⊢ snorm ((fun x => if { val := C, property := (_ : 0 ≤ C) } ≤ ‖x‖₊ then x else …
  rw [← snorm_map_measure _ (hf i).aemeasurable_fst, (hf i).map_eq,
    snorm_map_measure _ (hf j).aemeasurable_fst]
  · rfl
    -- 🎉 no goals
  all_goals
    exact_mod_cast aestronglyMeasurable_id.indicator
      (measurableSet_le measurable_const measurable_nnnorm)
#align probability_theory.mem_ℒp.uniform_integrable_of_ident_distrib_aux ProbabilityTheory.Memℒp.uniformIntegrable_of_identDistrib_aux

/-- A sequence of identically distributed Lᵖ functions is p-uniformly integrable. -/
theorem Memℒp.uniformIntegrable_of_identDistrib {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : Memℒp (f j) p μ) (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) :
    UniformIntegrable f p μ := by
  have hfmeas : ∀ i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι → α → E := fun i => (hfmeas i).choose
  -- ⊢ UniformIntegrable f p μ
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  -- ⊢ UniformIntegrable f p μ
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hfmeas i).2.symm
  -- ⊢ UniformIntegrable f p μ
  have hgℒp : Memℒp (g j) p μ := hℒp.ae_eq (hgeq j).symm
  -- ⊢ UniformIntegrable f p μ
  exact UniformIntegrable.ae_eq
    (Memℒp.uniformIntegrable_of_identDistrib_aux hp hp' hgℒp hgmeas fun i =>
      (IdentDistrib.of_ae_eq (hgmeas i).aemeasurable (hgeq i)).trans
        ((hf i).trans <| IdentDistrib.of_ae_eq (hfmeas j).aemeasurable (hgeq j).symm)) hgeq
#align probability_theory.mem_ℒp.uniform_integrable_of_ident_distrib ProbabilityTheory.Memℒp.uniformIntegrable_of_identDistrib

end UniformIntegrable

end ProbabilityTheory
