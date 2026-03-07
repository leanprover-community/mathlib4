/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be almost everywhere strongly measurable if `f` is almost everywhere
equal to a strongly measurable function, i.e. the sequential limit of simple functions.
It is said to be almost everywhere finitely strongly measurable with respect to a measure `μ`
if the supports of those simple functions have finite measure.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

## Main definitions
* `AEStronglyMeasurable f μ`: `f` is almost everywhere equal to a `StronglyMeasurable` function.
* `AEFinStronglyMeasurable f μ`: `f` is almost everywhere equal to a `FinStronglyMeasurable`
  function.

* `AEFinStronglyMeasurable.sigmaFiniteSet`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `AEFinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions.

One can specify the sigma-algebra according to which simple functions are taken using the
`AEStronglyMeasurable[m]` notation in the `MeasureTheory` scope. -/
@[fun_prop]
def AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α → β)
    (μ : Measure[m₀] α := by volume_tac) : Prop :=
  ∃ g : α → β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEStronglyMeasurable ..])
  (by fun_prop (disch := measurability))

/-- A function is `m`-`AEStronglyMeasurable` with respect to a measure `μ` if it is almost
everywhere equal to the limit of a sequence of `m`-simple functions. -/
scoped notation "AEStronglyMeasurable[" m "]" => @MeasureTheory.AEStronglyMeasurable _ _ _ m

/-- A function is `AEFinStronglyMeasurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def AEFinStronglyMeasurable
    [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

end Definitions

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

end FinStronglyMeasurable

theorem aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

/-! ## Almost everywhere strongly measurable functions -/

section AEStronglyMeasurable
variable [TopologicalSpace β] [TopologicalSpace γ] {m m₀ : MeasurableSpace α} {μ ν : Measure[m₀] α}
  {f g : α → β}

@[fun_prop]
protected theorem StronglyMeasurable.aestronglyMeasurable (hf : StronglyMeasurable[m] f) :
    AEStronglyMeasurable[m] f μ := ⟨f, hf, EventuallyEq.refl _ _⟩

@[fun_prop]
theorem aestronglyMeasurable_const {b : β} : AEStronglyMeasurable[m] (fun _ : α => b) μ :=
  stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := fun_prop)]
theorem aestronglyMeasurable_one [One β] : AEStronglyMeasurable[m] (1 : α → β) μ :=
  stronglyMeasurable_one.aestronglyMeasurable

@[simp, nontriviality]
lemma AEStronglyMeasurable.of_subsingleton_dom [Subsingleton α] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable

@[simp, nontriviality]
lemma AEStronglyMeasurable.of_subsingleton_cod [Subsingleton β] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable

@[fun_prop, simp]
theorem aestronglyMeasurable_zero_measure (f : α → β) :
    AEStronglyMeasurable[m] f (0 : Measure[m₀] α) := by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[fun_prop]
theorem SimpleFunc.aestronglyMeasurable (f : α →ₛ β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

namespace AEStronglyMeasurable

@[fun_prop]
lemma of_discrete [Countable α] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable

section Mk

/-- A `StronglyMeasurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`stronglyMeasurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEStronglyMeasurable[m] f μ) : α → β :=
  hf.choose

@[fun_prop]
lemma stronglyMeasurable_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f) :=
  hf.choose_spec.1

@[fun_prop]
theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable[m] f μ) : Measurable[m] (hf.mk f) :=
  hf.stronglyMeasurable_mk.measurable

theorem ae_eq_mk (hf : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

theorem congr (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩

theorem _root_.aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable[m] f μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable[m] f μ) (h : ν ≤ μ) :
    AEStronglyMeasurable[m] f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

protected lemma mono_ac (h : ν ≪ μ) (hμ : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f ν := let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩

theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

lemma mono {m'} (hm : m ≤ m') (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m'] f μ :=
  let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩

lemma of_trim {m₀' : MeasurableSpace α} (hm₀ : m₀' ≤ m₀)
    (hf : AEStronglyMeasurable[m] f (μ.trim hm₀)) : AEStronglyMeasurable[m] f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

@[fun_prop]
protected theorem restrict (hfm : AEStronglyMeasurable[m] f μ) {s} :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self

theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable[m] f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
@[fun_prop]
theorem _root_.Continuous.comp_aestronglyMeasurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
@[fun_prop]
theorem _root_.Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
protected theorem fst {f : α → β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x ↦ (f x).1) μ :=
  continuous_fst.comp_aestronglyMeasurable hf

@[fun_prop]
protected theorem snd {f : α → β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x ↦ (f x).2) μ :=
  continuous_snd.comp_aestronglyMeasurable hf

@[fun_prop]
protected theorem prodMk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prodMk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

/-- The composition of a continuous function of two variables and two ae strongly measurable
functions is ae strongly measurable. -/
theorem _root_.Continuous.comp_aestronglyMeasurable₂
    {β' : Type*} [TopologicalSpace β']
    {g : β → β' → γ} {f : α → β} {f' : α → β'} (hg : Continuous g.uncurry)
    (hf : AEStronglyMeasurable[m] f μ) (h'f : AEStronglyMeasurable[m] f' μ) :
    AEStronglyMeasurable[m] (fun x => g (f x) (f' x)) μ :=
  hg.comp_aestronglyMeasurable (hf.prodMk h'f)

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
@[fun_prop]
theorem _root_.Measurable.aestronglyMeasurable
    [MeasurableSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable[m] f) : AEStronglyMeasurable[m] f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
lemma of_measurableSpace_le_on {m' m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [Zero β]
    (hm : m ≤ m₀) {s : Set α} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m'] (s ∩ t))
    (hf : AEStronglyMeasurable[m] f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable[m'] f μ := by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
    refine Filter.EventuallyEq.trans ?_ <|
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable[m'] (s.indicator (hf.mk f)) from
    this.aestronglyMeasurable.congr h_ind_eq
  exact (hf.stronglyMeasurable_mk.indicator hs_m).stronglyMeasurable_of_measurableSpace_le_on hs_m
    hs fun x hxs => Set.indicator_of_notMem hxs _

section Arithmetic

@[to_additive (attr := fun_prop)]
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f * g) μ :=
  ⟨hf.mk f * hg.mk g, by fun_prop, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf

@[to_additive (attr := fun_prop)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_additive (attr := fun_prop)]
protected theorem div [Group β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[fun_prop]
theorem div₀ [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] [MeasurableSingletonClass β]
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (f * g) μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (g * f) μ ↔ AEStronglyMeasurable[m] g μ :=
  mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_additive (attr := fun_prop)]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (fun x => f x • g x) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := fun_prop) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (n : ℕ) :
    AEStronglyMeasurable[m] (f ^ n) μ :=
  ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := fun_prop)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable[m] f μ) (c : 𝕜) : AEStronglyMeasurable[m] (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[to_additive (attr := fun_prop)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable[m] f μ) (c : 𝕜) : AEStronglyMeasurable[m] (fun x => c • f x) μ :=
  hf.const_smul c

@[to_additive (attr := fun_prop)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : AEStronglyMeasurable[m] f μ) (c : β) : AEStronglyMeasurable[m] (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)

end Arithmetic

section Star

@[fun_prop]
protected theorem star {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] {f : α → R}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (star f) μ :=
  ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

end Star

section Order

@[fun_prop]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[fun_prop]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.List.aestronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  induction l with
  | nil => exact aestronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.List.aestronglyMeasurable_fun_prod
    (l : List (α → M)) (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Multiset.aestronglyMeasurable_prod (l : Multiset (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Multiset.aestronglyMeasurable_fun_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod hs

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Finset.aestronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aestronglyMeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Finset.aestronglyMeasurable_fun_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod hf

end CommMonoid

section SecondCountableAEStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[fun_prop]
theorem _root_.AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[fun_prop]
theorem _root_.aestronglyMeasurable_id {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {_ : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α → α) μ :=
  aemeasurable_id.aestronglyMeasurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

end SecondCountableAEStronglyMeasurable

@[fun_prop]
protected theorem dist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf

@[fun_prop]
protected theorem nnnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf

/-- The `enorm` of a strongly a.e. measurable function is a.e. measurable.

Note that unlike `AEStronglyMeasurable.norm` and `AEStronglyMeasurable.nnnorm`, this lemma proves
a.e. measurability, **not** a.e. strong measurability. This is an intentional decision:
for functions taking values in `ℝ≥0∞`, a.e. measurability is much more useful than
a.e. strong measurability. -/
@[fun_prop]
protected theorem enorm {β : Type*} [TopologicalSpace β] [ContinuousENorm β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (‖f ·‖ₑ) μ :=
  (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable

/-- Given a.e. strongly measurable functions `f` and `g`, `edist f g` is measurable.

Note that this lemma proves a.e. measurability, **not** a.e. strong measurability.
This is an intentional decision: for functions taking values in ℝ≥0∞,
a.e. measurability is much more useful than a.e. strong measurability. -/
@[fun_prop]
protected theorem edist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prodMk hg)).aemeasurable

@[fun_prop]
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf

theorem _root_.aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B

theorem _root_.aestronglyMeasurable_indicator_iff₀
    [Zero β] {s : Set α} (hs : NullMeasurableSet s μ) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    aestronglyMeasurable_indicator_iff (measurableSet_toMeasurable ..),
    restrict_congr_set hs.toMeasurable_ae_eq]

@[fun_prop]
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

@[fun_prop]
protected theorem indicator₀ [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : NullMeasurableSet s μ) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff₀ hs).2 hfm.restrict

theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  simp only [hfx, hgx]

@[to_additive]
lemma nullMeasurableSet_mulSupport {E} [TopologicalSpace E] [MetrizableSpace E] [One E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) : NullMeasurableSet (mulSupport f) μ :=
  (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl

theorem nullMeasurableSet_lt [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a < g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  simp only [hfx, hgx]

theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  simp only [hfx, hgx]

theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) {f : α → β} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

theorem comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

theorem comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

theorem comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable

theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      AEMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine ⟨g, ?_, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩

theorem _root_.aestronglyMeasurable_iff_nullMeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      NullMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
  aestronglyMeasurable_iff_aemeasurable_separable.trans <| and_congr_left fun ⟨_, hsep, h⟩ ↦
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf ↦ hf.aemeasurable_of_aerange h⟩

theorem _root_.MeasurableEmbedding.aestronglyMeasurable_map_iff {γ : Type*}
    {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    (hf : MeasurableEmbedding f) {g : α → β} :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

theorem _root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β} (hg : IsEmbedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ := by
  letI := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by rw [rangeFactorization_surjective.range_eq]; exact isClosed_univ }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.aemeasurable
    exact hG.measurableEmbedding.aemeasurable_comp_iff.1 this
  · rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.isSeparable_preimage ht, h't⟩

/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem _root_.aestronglyMeasurable_of_tendsto_ae {ι : Type*} [PseudoMetrizableSpace β]
    (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ ae μ := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine ⟨closure (⋃ i, t i), .closure <| .iUnion t_sep, ?_⟩
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    filter_upwards with n using mem_iUnion_of_mem n (hx n)

/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
theorem _root_.exists_stronglyMeasurable_limit_of_tendsto_ae [PseudoMetrizableSpace β]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    ∃ f_lim : α → β, StronglyMeasurable f_lim ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) := by
  borelize β
  obtain ⟨g, _, hg⟩ :
    ∃ g : α → β, Measurable g ∧ ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hg
  refine ⟨Hg.mk g, Hg.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx

/-- If `f` is almost everywhere strongly measurable and its range is almost everywhere contained
in a nonempty measurable set `s`, then there is a strongly measurable representative `g` of `f`
whose range is contained in `s`. -/
lemma exists_stronglyMeasurable_range_subset {α β : Type*}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [mb : MeasurableSpace β] [BorelSpace β]
    [m : MeasurableSpace α] {μ : Measure α} {f : α → β} (hf : AEStronglyMeasurable f μ)
    {s : Set β} (hs : MeasurableSet s) (h_nonempty : s.Nonempty) (h_mem : ∀ᵐ x ∂μ, f x ∈ s) :
    ∃ g : α → β, StronglyMeasurable g ∧ (∀ x, g x ∈ s) ∧ f =ᵐ[μ] g := by
  obtain ⟨f', hf', hff'⟩ := hf
  classical
  refine ⟨(f' ⁻¹' s).piecewise f' (fun _ ↦ h_nonempty.some), ?meas, ?subset, ?ae_eq⟩
  case meas => exact hf'.piecewise (hf'.measurable hs) stronglyMeasurable_const
  case subset =>
    rw [← Set.range_subset_iff]
    simpa [Set.range_piecewise] using fun _ _ ↦ h_nonempty.some_mem
  case ae_eq =>
    apply hff'.trans
    filter_upwards [h_mem, hff'] with x hx hx'
    exact Eq.symm <| (f' ⁻¹' s).piecewise_eq_of_mem f' _ (by simpa [hx'] using hx)

theorem piecewise {s : Set α} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : AEStronglyMeasurable g (μ.restrict sᶜ)) :
    AEStronglyMeasurable (s.piecewise f g) μ := by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs] at h
    rw [ae_restrict_iff' hs]
    filter_upwards [h] with x hx
    intro hx_mem
    simp only [hx_mem, Set.piecewise_eq_of_mem, hx hx_mem]
  · have h := hg.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at h
    rw [ae_restrict_iff' hs.compl]
    filter_upwards [h] with x hx
    intro hx_mem
    rw [Set.mem_compl_iff] at hx_mem
    simp only [hx_mem, not_false_eq_true, Set.piecewise_eq_of_notMem, hx hx_mem]

@[fun_prop]
theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι → Measure α}
    (h : ∀ i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (Measure.sum μ) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine ⟨⋃ i, t i, .iUnion t_sep, ?_⟩
  simp only [Measure.ae_sum_eq, mem_iUnion, eventually_iSup]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩

@[simp]
theorem _root_.aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β]
    {_m : MeasurableSpace α} {μ : ι → Measure α} :
    AEStronglyMeasurable f (sum μ) ↔ ∀ i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]
theorem _root_.aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν := by
  rw [← sum_cond, aestronglyMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl

@[fun_prop, measurability]
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[fun_prop, measurability]
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι → Set α}
    (h : ∀ i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le

@[simp]
theorem _root_.aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      ∀ i, AEStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]
theorem _root_.aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α → β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union, aestronglyMeasurable_union_iff]

@[fun_prop, measurability]
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section MulAction

variable {M G G₀ : Type*}
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

theorem _root_.aestronglyMeasurable_const_smul_iff (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u

theorem _root_.aestronglyMeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

end MulAction

end AEStronglyMeasurable
end AEStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AEFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

section Mk

variable [Zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEFinStronglyMeasurable f μ) : α → β :=
  hf.choose

theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1

theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

section Arithmetic

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end Arithmetic

section Order

variable [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

variable [Zero β] [T2Space β]

theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq, ae_restrict_iff' ht.compl]
  exact Eventually.of_forall hgt_zero

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
noncomputable def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose

protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1

theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1

instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2

end AEFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure,
  `AEFinStronglyMeasurable` and `AEMeasurable` are equivalent. -/
theorem aefinStronglyMeasurable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ := by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]

/-- In a space with second countable topology and a sigma-finite measure,
  an `AEMeasurable` function is `AEFinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem aefinStronglyMeasurable_of_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : AEMeasurable f μ) : AEFinStronglyMeasurable f μ :=
  (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

end SecondCountableTopology

end MeasureTheory
