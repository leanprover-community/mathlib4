/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.UniformIntegrable

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
* `IdentDistrib.memLp_snd`: if `f` and `g` are identically distributed and `f`
  belongs to `ℒp`, then so does `g`.

We also register several dot notation shortcuts for convenience.
For instance, if `h : IdentDistrib f g μ ν`, then `h.sq` states that `f^2` and `g^2` are
identically distributed, and `h.norm` states that `‖f‖` and `‖g‖` are identically distributed, and
so on.
-/


open MeasureTheory Filter Finset

noncomputable section

open scoped Topology MeasureTheory ENNReal NNReal

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

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

protected theorem refl (hf : AEMeasurable f μ) : IdentDistrib f f μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }

protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
  { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }

protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν)
    (h₂ : IdentDistrib g h ν ρ) : IdentDistrib f h μ ρ :=
  { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }

protected theorem comp_of_aemeasurable {u : γ → δ} (h : IdentDistrib f g μ ν)
    (hu : AEMeasurable u (Measure.map f μ)) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst, ←
        AEMeasurable.map_map_of_aemeasurable _ h.aemeasurable_snd, h.map_eq]
      rwa [← h.map_eq] }

protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
    IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  h.comp_of_aemeasurable hu.aemeasurable

protected theorem of_ae_eq {g : α → γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g) :
    IdentDistrib f g μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }

lemma _root_.MeasureTheory.AEMeasurable.identDistrib_mk
    (hf : AEMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf hf.ae_eq_mk

lemma _root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk
    [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (hf : AEStronglyMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk

theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs, ←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs, h.map_eq]

alias measure_preimage_eq := measure_mem_eq

theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ → Prop} (pmeas : MeasurableSet {x | p x})
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp

theorem ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t)
    (ht : ∀ᵐ x ∂μ, f x ∈ t) : ∀ᵐ x ∂ν, g x ∈ t :=
  h.ae_snd tmeas ht

/-- In a second countable topology, the first function in an identically distributed pair is a.e.
strongly measurable. So is the second function, but use `h.symm.aestronglyMeasurable_fst` as
`h.aestronglyMeasurable_snd` has a different meaning. -/
theorem aestronglyMeasurable_fst [TopologicalSpace γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ] [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) :
    AEStronglyMeasurable f μ :=
  h.aemeasurable_fst.aestronglyMeasurable

/-- If `f` and `g` are identically distributed and `f` is a.e. strongly measurable, so is `g`. -/
theorem aestronglyMeasurable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable g ν := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx using subset_closure hx

theorem aestronglyMeasurable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g ν :=
  ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩

theorem essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : ∀ a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]

theorem lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν := by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst, ←
    lintegral_map' aemeasurable_id h.aemeasurable_snd, h.map_eq]

theorem integral_eq [NormedAddCommGroup γ] [NormedSpace ℝ γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν := by
  by_cases hf : AEStronglyMeasurable f μ
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine ⟨aemeasurable_id, ⟨closure t, t_sep.closure, ?_⟩⟩
      rw [ae_map_iff h.aemeasurable_fst]
      · filter_upwards [ht] with x hx using subset_closure hx
      · exact isClosed_closure.measurableSet
    change ∫ x, id (f x) ∂μ = ∫ x, id (g x) ∂ν
    rw [← integral_map h.aemeasurable_fst A]
    rw [h.map_eq] at A
    rw [← integral_map h.aemeasurable_snd A, h.map_eq]
  · rw [integral_non_aestronglyMeasurable hf]
    rw [h.aestronglyMeasurable_iff] at hf
    rw [integral_non_aestronglyMeasurable hf]

theorem eLpNorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
    (p : ℝ≥0∞) : eLpNorm f p μ = eLpNorm g p ν := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm, eLpNormEssSup, ENNReal.top_ne_zero, if_true,
      if_false]
    apply essSup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
  simp only [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', one_div]
  congr 1
  apply lintegral_eq
  exact h.comp (Measurable.pow_const (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
    p.toReal)

theorem memLp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν)
    (hf : MemLp f p μ) : MemLp g p ν := by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2

@[deprecated (since := "2025-02-21")]
alias memℒp_snd := memLp_snd

theorem memLp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    MemLp f p μ ↔ MemLp g p ν :=
  ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩

@[deprecated (since := "2025-02-21")]
alias memℒp_iff := memLp_iff

theorem integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : Integrable f μ) : Integrable g ν := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf

theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩

protected theorem norm [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖) (fun x => ‖g x‖) μ ν :=
  h.comp measurable_norm

protected theorem nnnorm [NormedAddCommGroup γ] [OpensMeasurableSpace γ]
    (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖₊) (fun x => ‖g x‖₊) μ ν :=
  h.comp measurable_nnnorm

protected theorem pow [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) {n : ℕ} :
    IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν :=
  h.comp (measurable_id.pow_const n)

protected theorem sq [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν :=
  h.comp (measurable_id.pow_const 2)

protected theorem coe_nnreal_ennreal {f : α → ℝ≥0} {g : β → ℝ≥0} (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => (f x : ℝ≥0∞)) (fun x => (g x : ℝ≥0∞)) μ ν :=
  h.comp measurable_coe_nnreal_ennreal

@[to_additive]
theorem mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x * c) (fun x => g x * c) μ ν :=
  h.comp (measurable_mul_const c)

@[to_additive]
theorem const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c * f x) (fun x => c * g x) μ ν :=
  h.comp (measurable_const_mul c)

@[to_additive]
theorem div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x / c) (fun x => g x / c) μ ν :=
  h.comp (MeasurableDiv.measurable_div_const c)

@[to_additive]
theorem const_div [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c / f x) (fun x => c / g x) μ ν :=
  h.comp (MeasurableDiv.measurable_const_div c)

@[to_additive]
lemma inv [Inv γ] [MeasurableInv γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib f⁻¹ g⁻¹ μ ν := h.comp measurable_inv

theorem evariance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    evariance f μ = evariance g ν := by
  convert (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl

theorem variance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    variance f μ = variance g ν := by rw [variance, h.evariance_eq]; rfl

end IdentDistrib

section UniformIntegrable

open TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- This lemma is superseded by `MemLp.uniformIntegrable_of_identDistrib` which only requires
`AEStronglyMeasurable`. -/
theorem MemLp.uniformIntegrable_of_identDistrib_aux {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : MemLp (f j) p μ) (hfmeas : ∀ i, StronglyMeasurable (f i))
    (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  refine uniformIntegrable_of' hp hp' hfmeas fun ε hε => ?_
  by_cases hι : Nonempty ι
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.eLpNorm_indicator_norm_ge_pos_le (hfmeas _) hε
  refine ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq ?_) hC₂⟩
  have : {x | (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖f i x‖₊} = {x | C ≤ ‖f i x‖} := by
    ext x
    simp_rw [← norm_toNNReal]
    exact Real.le_toNNReal_iff_coe_le (norm_nonneg _)
  rw [this, ← eLpNorm_norm, ← eLpNorm_norm (Set.indicator _ _)]
  simp_rw [norm_indicator_eq_indicator_norm, coe_nnnorm]
  let F : E → ℝ := (fun x : E => if (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖x‖₊ then ‖x‖ else 0)
  have F_meas : Measurable F := by
    apply measurable_norm.indicator (measurableSet_le measurable_const measurable_nnnorm)
  have : ∀ k, (fun x ↦ Set.indicator {x | C ≤ ‖f k x‖} (fun a ↦ ‖f k a‖) x) = F ∘ f k := by
    intro k
    ext x
    simp only [Set.indicator, Set.mem_setOf_eq]; norm_cast
  rw [this, this, ← eLpNorm_map_measure F_meas.aestronglyMeasurable (hf i).aemeasurable_fst,
    (hf i).map_eq, eLpNorm_map_measure F_meas.aestronglyMeasurable (hf j).aemeasurable_fst]

@[deprecated (since := "2025-02-21")]
alias Memℒp.uniformIntegrable_of_identDistrib_aux := MemLp.uniformIntegrable_of_identDistrib_aux

/-- A sequence of identically distributed Lᵖ functions is p-uniformly integrable. -/
theorem MemLp.uniformIntegrable_of_identDistrib {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : MemLp (f j) p μ) (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) :
    UniformIntegrable f p μ := by
  have hfmeas : ∀ i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι → α → E := fun i => (hfmeas i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hfmeas i).2.symm
  have hgℒp : MemLp (g j) p μ := hℒp.ae_eq (hgeq j).symm
  exact UniformIntegrable.ae_eq
    (MemLp.uniformIntegrable_of_identDistrib_aux hp hp' hgℒp hgmeas fun i =>
      (IdentDistrib.of_ae_eq (hgmeas i).aemeasurable (hgeq i)).trans
        ((hf i).trans <| IdentDistrib.of_ae_eq (hfmeas j).aemeasurable (hgeq j).symm)) hgeq

@[deprecated (since := "2025-02-21")]
alias Memℒp.uniformIntegrable_of_identDistrib := MemLp.uniformIntegrable_of_identDistrib

end UniformIntegrable

/-- If `X` and `Y` are independent and `(X, Y)` and `(X', Y')` are identically distributed,
then `X'` and `Y'` are independent. -/
lemma indepFun_of_identDistrib_pair
    {μ : Measure γ} {μ' : Measure δ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : γ → α} {X' : δ → α} {Y : γ → β} {Y' : δ → β} (h_indep : IndepFun X Y μ)
    (h_ident : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (X' ω, Y' ω)) μ μ') :
    IndepFun X' Y' μ' := by
  rw [indepFun_iff_map_prod_eq_prod_map_map _ _, ← h_ident.map_eq,
    (indepFun_iff_map_prod_eq_prod_map_map _ _).1 h_indep]
  · exact congr (congrArg Measure.prod <| (h_ident.comp measurable_fst).map_eq)
      (h_ident.comp measurable_snd).map_eq
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd

end ProbabilityTheory
