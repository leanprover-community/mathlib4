/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Kernel
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional Independence

We define conditional independence of sets/σ-algebras/functions with respect to a σ-algebra.

Two σ-algebras `m₁` and `m₂` are conditionally independent given a third σ-algebra `m'` if for all
`m₁`-measurable sets `t₁` and `m₂`-measurable sets `t₂`,
`μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.

On standard Borel spaces, the conditional expectation with respect to `m'` defines a kernel
`ProbabilityTheory.condExpKernel`, and the definition above is equivalent to
`∀ᵐ ω ∂μ, condExpKernel μ m' ω (t₁ ∩ t₂) = condExpKernel μ m' ω t₁ * condExpKernel μ m' ω t₂`.
We use this property as the definition of conditional independence.

## Main definitions

We provide four definitions of conditional independence:
* `iCondIndepSets`: conditional independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
  This is meant to be used with π-systems.
* `iCondIndep`: conditional independence of a family of measurable space structures
  `m : ι → MeasurableSpace Ω`,
* `iCondIndepSet`: conditional independence of a family of sets `s : ι → Set Ω`,
* `iCondIndepFun`: conditional independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `CondIndepFun` is the version of
`iCondIndepFun` for two functions.

## Main statements

* `ProbabilityTheory.iCondIndepSets.iCondIndep`: if π-systems are conditionally independent as sets
  of sets, then the measurable space structures they generate are conditionally independent.
* `ProbabilityTheory.condIndepSets.condIndep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[Z, hZ; μ] Y` for `CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ`,
  independence of `X` and `Y` given `Z`.
* `X ⟂ᵢ[Z, hZ] Y` for the cases of `μ = volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of conditional independence in this file are a particular case of independence with
respect to a kernel and a measure, as defined in the file `Probability/Independence/Kernel.lean`.
The kernel used is `ProbabilityTheory.condExpKernel`.

-/

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

section Definitions

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)

/-- A family of sets of sets `π : ι → Set (Set Ω)` is conditionally independent given `m'` with
respect to a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧`.
See `ProbabilityTheory.iCondIndepSets_iff`.
It will be used for families of pi_systems. -/
def iCondIndepSets (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

/-- Two sets of sets `s₁, s₂` are conditionally independent given `m'` with respect to a measure
`μ` if for any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndepSets_iff`. -/
def CondIndepSets (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

/-- A family of measurable space structures (i.e. of σ-algebras) is conditionally independent given
`m'` with respect to a measure `μ` (typically defined on a finer σ-algebra) if the family of sets of
measurable sets they define is independent. `m : ι → MeasurableSpace Ω` is conditionally independent
given `m'` with respect to measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for
any sets `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then
`μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧ `.
See `ProbabilityTheory.iCondIndep_iff`. -/
def iCondIndep (m : ι → MeasurableSpace Ω)
    (μ : @Measure Ω mΩ := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

end

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are conditionally independent given
`m'` with respect to a measure `μ` (defined on a third σ-algebra) if for any sets
`t₁ ∈ m₁, t₂ ∈ m₂`, `μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.
See `ProbabilityTheory.condIndep_iff`. -/
def CondIndep (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' ≤ mΩ)

/-- A family of sets is conditionally independent if the family of measurable space structures they
generate is conditionally independent. For a set `s`, the generated measurable space has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.iCondIndepSet_iff`. -/
def iCondIndepSet (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

/-- Two sets are conditionally independent if the two measurable space structures they generate are
conditionally independent. For a set `s`, the generated measurable space structure has measurable
sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.condIndepSet_iff`. -/
def CondIndepSet (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is conditionally independent if the family of
measurable space structures they generate on `Ω` is conditionally independent. For a function `g`
with codomain having measurable space structure `m`, the generated measurable space structure is
`m.comap g`.
See `ProbabilityTheory.iCondIndepFun_iff`. -/
def iCondIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

/-- Two functions are conditionally independent if the two measurable space structures they generate
are conditionally independent. For a function `f` with codomain having measurable space structure
`m`, the generated measurable space structure is `m.comap f`.
See `ProbabilityTheory.condIndepFun_iff`.
We use the notation `X ⟂ᵢ[Z, hZ; μ] Y` to write that `X` and `Y` are conditionally independent
given (the σ-algebra generated by) `Z` (scoped in `ProbabilityTheory`). -/
def CondIndepFun {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

end

end Definitions

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y μ

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y volume

section DefinitionLemmas

section
variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)

lemma iCondIndepSets_iff (π : ι → Set (Set Ω)) (hπ : ∀ i s (_hs : s ∈ π i), MeasurableSet s)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
      μ⟦⋂ i ∈ s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦f i | m'⟧) := by
  simp only [iCondIndepSets, Kernel.iIndepSets]
  have h_eq' : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i) i (_hi : i ∈ s),
      (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (f i))) =ᵐ[μ] μ⟦f i | m'⟧ :=
    fun s f H i hi ↦ condExpKernel_ae_eq_condExp hm' (hπ i (f i) (H i hi))
  have h_eq : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i), ∀ᵐ ω ∂μ,
      ∀ i ∈ s, ENNReal.toReal (condExpKernel μ m' ω (f i)) = (μ⟦f i | m'⟧) ω := by
    intro s f H
    simp_rw [← Finset.mem_coe]
    rw [ae_ball_iff (Finset.countable_toSet s)]
    exact h_eq' s f H
  have h_inter_eq : ∀ (s : Finset ι) (f : ι → Set Ω) (_H : ∀ i, i ∈ s → f i ∈ π i),
      (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (⋂ i ∈ s, f i)))
        =ᵐ[μ] μ⟦⋂ i ∈ s, f i | m'⟧ := by
    refine fun s f H ↦ condExpKernel_ae_eq_condExp hm' ?_
    exact MeasurableSet.biInter (Finset.countable_toSet _) (fun i hi ↦ hπ i _ (H i hi))
  refine ⟨fun h s f hf ↦ ?_, fun h s f hf ↦ ?_⟩ <;> specialize h s hf
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h'] with ω h_eq h_inter_eq h'
    rw [← h_inter_eq, h', ENNReal.toReal_prod, Finset.prod_apply]
    exact Finset.prod_congr rfl h_eq
  · refine ((stronglyMeasurable_condExpKernel ?_).ae_eq_trim_iff hm' ?_).mpr ?_
    · exact .biInter (Finset.countable_toSet _) (fun i hi ↦ hπ i _ (hf i hi))
    · refine Measurable.stronglyMeasurable ?_
      exact Finset.measurable_fun_prod s (fun i hi ↦ measurable_condExpKernel (hπ i _ (hf i hi)))
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h] with ω h_eq h_inter_eq h
    have h_ne_top : condExpKernel μ m' ω (⋂ i ∈ s, f i) ≠ ∞ :=
      (measure_ne_top (condExpKernel μ m' ω) _)
    have : (∏ i ∈ s, condExpKernel μ m' ω (f i)) ≠ ∞ :=
      ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top, h_inter_eq, h, Finset.prod_apply,
      ← ENNReal.ofReal_toReal this, ENNReal.toReal_prod]
    congr 1
    exact Finset.prod_congr rfl (fun i hi ↦ (h_eq i hi).symm)

lemma condIndepSets_iff (s1 s2 : Set (Set Ω)) (hs1 : ∀ s ∈ s1, MeasurableSet s)
    (hs2 : ∀ s ∈ s2, MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSets m' hm' s1 s2 μ ↔ ∀ (t1 t2 : Set Ω) (_ : t1 ∈ s1) (_ : t2 ∈ s2),
      (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  simp only [CondIndepSets, Kernel.IndepSets]
  have hs1_eq : ∀ s ∈ s1, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs ↦ condExpKernel_ae_eq_condExp hm' (hs1 s hs)
  have hs2_eq : ∀ s ∈ s2, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs ↦ condExpKernel_ae_eq_condExp hm' (hs2 s hs)
  have hs12_eq : ∀ s ∈ s1, ∀ t ∈ s2, (fun ω ↦ ENNReal.toReal (condExpKernel μ m' ω (s ∩ t)))
      =ᵐ[μ] μ⟦s ∩ t | m'⟧ :=
    fun s hs t ht ↦ condExpKernel_ae_eq_condExp hm' ((hs1 s hs).inter ((hs2 t ht)))
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t hs ht ↦ ?_⟩ <;> specialize h s t hs ht
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h'] with ω hs_eq ht_eq hst_eq h'
    rw [← hst_eq, Pi.mul_apply, ← hs_eq, ← ht_eq, h', ENNReal.toReal_mul]
  · refine ((stronglyMeasurable_condExpKernel ((hs1 s hs).inter (hs2 t ht))).ae_eq_trim_iff hm'
      ((measurable_condExpKernel (hs1 s hs)).mul
        (measurable_condExpKernel (hs2 t ht))).stronglyMeasurable).mpr ?_
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h] with ω hs_eq ht_eq hst_eq h
    have h_ne_top : condExpKernel μ m' ω (s ∩ t) ≠ ∞ := measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top, hst_eq, h, Pi.mul_apply, ← hs_eq, ← ht_eq,
      ← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
    exact ENNReal.mul_ne_top (measure_ne_top (condExpKernel μ m' ω) s)
      (measure_ne_top (condExpKernel μ m' ω) t)

lemma iCondIndepSets_singleton_iff (s : ι → Set Ω) (hπ : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' (fun i ↦ {s i}) μ ↔ ∀ S : Finset ι,
      μ⟦⋂ i ∈ S, s i | m'⟧ =ᵐ[μ] ∏ i ∈ S, (μ⟦s i | m'⟧) := by
  rw [iCondIndepSets_iff]
  · simp only [Set.mem_singleton_iff]
    refine ⟨fun h S ↦ h S (fun i _ ↦ rfl), fun h S f hf ↦ ?_⟩
    filter_upwards [h S] with a ha
    refine Eq.trans ?_ (ha.trans ?_)
    · grind
    · simp_rw [Finset.prod_apply]
      refine Finset.prod_congr rfl (fun i hi ↦ ?_)
      rw [hf i hi]
  · simpa only [Set.mem_singleton_iff, forall_eq]

theorem condIndepSets_singleton_iff {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    CondIndepSets m' hm' {s} {t} μ ↔ (μ⟦s ∩ t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSets_iff _ _ _ _ ?_ ?_]
  · simp only [Set.mem_singleton_iff, forall_eq_apply_imp_iff, forall_eq]
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']

lemma iCondIndep_iff_iCondIndepSets (m : ι → MeasurableSpace Ω)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ ↔ iCondIndepSets m' hm' (fun x ↦ {s | MeasurableSet[m x] s}) μ := by
  simp only [iCondIndep, iCondIndepSets, Kernel.iIndep]

lemma iCondIndep_iff (m : ι → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ
      ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[m i] (f i)),
      μ⟦⋂ i ∈ s, f i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦f i | m'⟧) := by
  rw [iCondIndep_iff_iCondIndepSets, iCondIndepSets_iff]
  · rfl
  · exact hm

end

section CondIndep

lemma condIndep_iff_condIndepSets (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ CondIndepSets m' hm' {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [CondIndep, CondIndepSets, Kernel.Indep]

lemma condIndep_iff (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ ∀ t1 t2, MeasurableSet[m₁] t1 → MeasurableSet[m₂] t2
        → (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndep_iff_condIndepSets, condIndepSets_iff]
  · rfl
  · exact hm₁
  · exact hm₂

end CondIndep

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' ≤ mΩ)

lemma iCondIndepSet_iff_iCondIndep (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndep m' hm' (fun i ↦ generateFrom {s i}) μ := by
  simp only [iCondIndepSet, iCondIndep, Kernel.iIndepSet]

theorem iCondIndepSet_iff_iCondIndepSets_singleton (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndepSets m' hm' (fun i ↦ {s i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hs

lemma iCondIndepSet_iff (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔
      ∀ S : Finset ι, μ⟦⋂ i ∈ S, s i | m'⟧ =ᵐ[μ] ∏ i ∈ S, μ⟦s i | m'⟧ := by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton _ _ _ hs, iCondIndepSets_singleton_iff _ _ _ hs]

lemma condIndepSet_iff_condIndep (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndep m' (generateFrom {s}) (generateFrom {t}) hm' μ := by
  simp only [CondIndepSet, CondIndep, Kernel.IndepSet]

theorem condIndepSet_iff_condIndepSets_singleton {s t : Set Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

lemma condIndepSet_iff (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ (μ⟦s ∩ t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ hs ht μ, condIndepSets_singleton_iff _ _ hs ht]

lemma iCondIndepFun_iff_iCondIndep {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ iCondIndep m' hm' (fun x ↦ MeasurableSpace.comap (f x) (m x)) μ := by
  simp only [iCondIndepFun, iCondIndep, Kernel.iIndepFun]

lemma iCondIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (hf : ∀ i, Measurable (f i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ ∀ (s : Finset ι) {g : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[(m i).comap (f i)] (g i)),
      μ⟦⋂ i ∈ s, g i | m'⟧ =ᵐ[μ] ∏ i ∈ s, (μ⟦g i | m'⟧) := by
  simp only [iCondIndepFun_iff_iCondIndep]
  rw [iCondIndep_iff]
  exact fun i ↦ (hf i).comap_le

lemma condIndepFun_iff_condIndep {β γ : Type*} [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ
      ↔ CondIndep m' (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) hm' μ := by
  simp only [CondIndepFun, CondIndep, Kernel.IndepFun]

lemma condIndepFun_iff {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ ↔ ∀ t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      → MeasurableSet[MeasurableSpace.comap g mγ] t2
        → (μ⟦t1 ∩ t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndepFun_iff_condIndep, condIndep_iff _ _ _ _ hf.comap_le hg.comap_le]

end DefinitionLemmas

section CondIndepSets

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

@[symm]
theorem CondIndepSets.symm {s₁ s₂ : Set (Set Ω)}
    (h : CondIndepSets m' hm' s₁ s₂ μ) : CondIndepSets m' hm' s₂ s₁ μ :=
  Kernel.IndepSets.symm h

theorem condIndepSets_of_condIndepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    CondIndepSets m' hm' s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31

theorem condIndepSets_of_condIndepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    CondIndepSets m' hm' s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32

theorem CondIndepSets.union {s₁ s₂ s' : Set (Set Ω)}
    (h₁ : CondIndepSets m' hm' s₁ s' μ) (h₂ : CondIndepSets m' hm' s₂ s' μ) :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
theorem CondIndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ
      ↔ CondIndepSets m' hm' s₁ s' μ ∧ CondIndepSets m' hm' s₂ s' μ :=
  Kernel.IndepSets.union_iff

theorem CondIndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp

theorem CondIndepSets.bUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : ∀ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bUnion hyp

theorem CondIndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    (h₁ : CondIndepSets m' hm' s₁ s' μ) :
    CondIndepSets m' hm' (s₁ ∩ s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁

theorem CondIndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h

theorem CondIndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bInter h

end CondIndepSets

section CondIndepSet

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condIndepSet_empty_right (s : Set Ω) : CondIndepSet m' hm' s ∅ μ :=
  Kernel.indepSet_empty_right s

theorem condIndepSet_empty_left (s : Set Ω) : CondIndepSet m' hm' ∅ s μ :=
  Kernel.indepSet_empty_left s

end CondIndepSet

section CondIndep

@[symm]
theorem CondIndep.symm {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : CondIndep m' m₁ m₂ hm' μ) :
    CondIndep m' m₂ m₁ hm' μ :=
  CondIndepSets.symm h

theorem condIndep_bot_right (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' m₁ ⊥ hm' μ :=
  Kernel.indep_bot_right m₁

theorem condIndep_bot_left (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' ⊥ m₁ hm' μ :=
  (Kernel.indep_bot_right m₁).symm

theorem condIndep_of_condIndep_of_le_left {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h31 : m₃ ≤ m₁) :
    CondIndep m' m₃ m₂ hm' μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31

theorem condIndep_of_condIndep_of_le_right {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h32 : m₃ ≤ m₂) :
    CondIndep m' m₁ m₃ hm' μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32

end CondIndep

/-! ### Deducing `CondIndep` from `iCondIndep` -/


section FromiCondIndepToCondIndep

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem iCondIndepSets.condIndepSets {s : ι → Set (Set Ω)}
    (h_indep : iCondIndepSets m' hm' s μ) {i j : ι} (hij : i ≠ j) :
    CondIndepSets m' hm' (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij

theorem iCondIndep.condIndep {m : ι → MeasurableSpace Ω}
    (h_indep : iCondIndep m' hm' m μ) {i j : ι} (hij : i ≠ j) :
      CondIndep m' (m i) (m j) hm' μ :=
  Kernel.iIndep.indep h_indep hij

theorem iCondIndepFun.condIndepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i}
    (hf_Indep : iCondIndepFun m' hm' f μ) {i j : ι} (hij : i ≠ j) :
    CondIndepFun m' hm' (f i) (f j) μ :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromiCondIndepToCondIndep

/-!
## π-system lemma

Conditional independence of measurable spaces is equivalent to conditional independence of
generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Conditional independence of σ-algebras implies conditional independence of
  generating π-systems -/

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem iCondIndep.iCondIndepSets {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n))
    (h_indep : iCondIndep m' hm' m μ) :
    iCondIndepSets m' hm' s μ :=
  Kernel.iIndep.iIndepSets hms h_indep

theorem CondIndep.condIndepSets {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep m' (generateFrom s1) (generateFrom s2) hm' μ) :
    CondIndepSets m' hm' s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Conditional independence of generating π-systems implies conditional independence of
  σ-algebras -/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem CondIndepSets.condIndep
    {p1 p2 : Set (Set Ω)} (h1 : m₁ ≤ mΩ) (h2 : m₂ ≤ mΩ)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m₁ = generateFrom p1) (hpm2 : m₂ = generateFrom p2)
    (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' m₁ m₂ hm' μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

theorem CondIndepSets.condIndep'
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' (generateFrom p1) (generateFrom p2) hm' μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

theorem condIndepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iCondIndepSets m' hm' s μ) (hST : Disjoint S T) :
    CondIndepSets m' hm' (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

theorem iCondIndepSet.condIndep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (S T : Set ι)
    (hST : Disjoint S T) :
    CondIndep m' (generateFrom { t | ∃ n ∈ S, s n = t })
      (generateFrom { t | ∃ k ∈ T, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

theorem condIndep_iSup_of_disjoint {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_indep : iCondIndep m' hm' m μ) {S T : Set ι} (hST : Disjoint S T) :
    CondIndep m' (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) hm' μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST

theorem condIndep_iSup_of_directed_le {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ)
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ) (hm : Directed (· ≤ ·) m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

theorem iCondIndepSet.condIndep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) :
    CondIndep m' (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

theorem iCondIndepSet.condIndep_generateFrom_le [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) {k : ι} (hk : i < k) :
    CondIndep m' (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

theorem iCondIndepSet.condIndep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (n : ℕ) :
    CondIndep m' (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

theorem condIndep_iSup_of_monotone [SemilatticeSup ι] {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ)
    (hm : Monotone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

theorem condIndep_iSup_of_antitone [SemilatticeInf ι] {m : ι → MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m₁ ≤ mΩ)
    (hm : Antitone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

theorem iCondIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iCondIndepSets m' hm' π μ) (haS : a ∉ S) :
    CondIndepSets m' hm' (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

@[deprecated (since := "2025-05-23")]
alias iCondIndepSets.piiUnionInter_of_not_mem := iCondIndepSets.piiUnionInter_of_notMem

/-- The σ-algebras generated by conditionally independent pi-systems are conditionally independent.
-/
theorem iCondIndepSets.iCondIndep (m : ι → MeasurableSpace Ω)
    (h_le : ∀ i, m i ≤ mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iCondIndepSets m' hm' π μ) :
    iCondIndep m' hm' m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section CondIndepSet

/-! ### Conditional independence of measurable sets

-/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ}
  {s t : Set Ω} (S T : Set (Set Ω))

theorem CondIndepSets.condIndepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ]
    (h_indep : CondIndepSets m' hm' S T μ) :
    CondIndepSet m' hm' s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

theorem CondIndep.condIndepSet_of_measurableSet {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) :
    CondIndepSet m' hm' s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

theorem condIndep_iff_forall_condIndepSet (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t
      → CondIndepSet m' hm' s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

end CondIndepSet

section CondIndepFun

/-! ### Conditional independence of random variables

-/

variable {β β' : Type*} {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → β'}

theorem condIndepFun_iff_condExp_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → (μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧) =ᵐ[μ] fun ω ↦ (μ⟦f ⁻¹' s | m'⟧) ω * (μ⟦g ⁻¹' t | m'⟧) ω := by
  rw [condIndepFun_iff _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t ↦ ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht

theorem iCondIndepFun_iff_condExp_inter_preimage_eq_mul {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) (hf : ∀ i, Measurable (f i)) :
    iCondIndepFun m' hm' f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        (μ⟦⋂ i ∈ S, f i ⁻¹' sets i | m'⟧) =ᵐ[μ] ∏ i ∈ S, (μ⟦f i ⁻¹' sets i | m'⟧) := by
  rw [iCondIndepFun_iff]
  swap
  · exact hf
  refine ⟨fun h s sets h_sets ↦ ?_, fun h s sets h_sets ↦ ?_⟩
  · refine h s (g := fun i ↦ f i ⁻¹' (sets i)) (fun i hi ↦ ?_)
    exact ⟨sets i, h_sets i hi, rfl⟩
  · classical
    let g := fun i ↦ if hi : i ∈ s then (h_sets i hi).choose else Set.univ
    specialize h s (sets := g) (fun i hi ↦ ?_)
    · simp only [g, dif_pos hi]
      exact (h_sets i hi).choose_spec.1
    · have hg : ∀ i ∈ s, sets i = f i ⁻¹' g i := by
        intro i hi
        rw [(h_sets i hi).choose_spec.2.symm]
        simp only [g, dif_pos hi]
      convert h with i hi i hi <;> exact hg i hi

theorem condIndepFun_iff_condIndepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → CondIndepSet m' hm' (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [CondIndepFun, CondIndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

@[symm]
nonrec theorem CondIndepFun.symm {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω → β} {g : Ω → β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  hfg.symm

theorem CondIndepFun.comp {γ γ' : Type*} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : CondIndepFun m' hm' f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun m' hm' (φ ∘ f) (ψ ∘ g) μ :=
  Kernel.IndepFun.comp hfg hφ hψ

lemma condIndepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (c : β) (X : Ω → β') :
    CondIndepFun m' hm' (fun _ ↦ c) X μ :=
  Kernel.indepFun_const_left c X

lemma condIndepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (X : Ω → β) (c : β') :
    CondIndepFun m' hm' X (fun _ ↦ c) μ :=
  Kernel.indepFun_const_right X c

theorem CondIndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' f (-g) μ := hfg.comp measurable_id measurable_neg

theorem CondIndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' (-f) g μ := hfg.comp measurable_neg measurable_id

lemma condIndepFun_of_measurable_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable[m'] X) (hY : Measurable Y) :
    CondIndepFun m' hm' X Y μ := by
  rw [condIndepFun_iff _ hm' _ _ (hX.mono hm' le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [show (fun ω : Ω ↦ (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
  calc μ[(X ⁻¹' s).indicator 1 * (Y ⁻¹' t).indicator 1|m']
  _ =ᵐ[μ] (X ⁻¹' s).indicator 1 * μ[(Y ⁻¹' t).indicator 1|m'] := by
    refine condExp_stronglyMeasurable_mul_of_bound hm' (stronglyMeasurable_const.indicator (hX hs))
      ((integrable_indicator_iff (hY ht)).2 integrableOn_const) 1 (ae_of_all μ fun ω ↦ ?_)
    rw [Set.indicator]
    split_ifs with h <;> simp
  _ =ᵐ[μ] μ[(X ⁻¹' s).indicator 1|m'] * μ[(Y ⁻¹' t).indicator 1|m'] := by
    nth_rw 2 [condExp_of_stronglyMeasurable hm']
    · exact stronglyMeasurable_const.indicator (hX hs)
    · exact (integrable_indicator_iff ((hX.le hm') hs)).2 integrableOn_const

lemma condIndepFun_of_measurable_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable X) (hY : Measurable[m'] Y) :
    CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_measurable_left hY hX).symm

lemma condIndepFun_self_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Z : Ω → β'} (hX : Measurable X) (hZ : Measurable Z) :
    Z ⟂ᵢ[Z, hZ; μ] X :=
  condIndepFun_of_measurable_left (comap_measurable Z) hX

lemma condIndepFun_self_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω → β} {Z : Ω → β'} (hX : Measurable X) (hZ : Measurable Z) :
    X ⟂ᵢ[Z, hZ; μ] Z :=
  condIndepFun_of_measurable_right hX (comap_measurable Z)

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectations, and the
almost sure equality is expressed as equality of the composition-product with the measure, which is
equivalent to a.e. equality. See `condIndepFun_iff_map_prod_eq_prod_map_map` for the a.e. equality
version with kernels.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (μ.trim hm') ⊗ₘ (condExpKernel μ m').map (fun ω ↦ (f ω, g ω))
        = (μ.trim hm') ⊗ₘ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g) :=
  Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with Markov kernels associated to the conditional expectations.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
theorem condIndepFun_iff_map_prod_eq_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [CountableOrCountablyGenerated Ω (β × β')]
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (condExpKernel μ m').map (fun ω ↦ (f ω, g ω))
        =ᵐ[μ.trim hm'] (condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg, ← Kernel.compProd_eq_iff]

/-- Two random variables are conditionally independent with respect to `m'` iff the law of
`(id, f, g)` under `μ`, in which the identity is to the space with σ-algebra `m'`, can be written
as a product involving the conditional expectations of `f` and `g` given `m'`.

For a random variable `f`, `(condExpKernel μ m').map f` is the law of the conditional expectation
of `f` given `m'`: almost surely, `(condExpKernel μ m').map f ω s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ @Measure.map _ _ _ (m'.prod _) (fun ω ↦ (ω, f ω, g ω)) μ
        = (Kernel.id ×ₖ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g))
          ∘ₘ μ.trim hm' := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]
  congr!
  · rw [Measure.compProd_map (by fun_prop), compProd_trim_condExpKernel,
      Measure.map_map (by fun_prop) ((measurable_id.mono le_rfl hm').prodMk measurable_id)]
    rfl
  · rw [Measure.compProd_eq_comp_prod]

/-- Two random variables `f, g` are conditionally independent given a third `k` iff the
joint distribution of `k, f, g` factors into a product of their conditional distributions
given `k`. -/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) =
        (Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k := by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : MeasurableSet[mγ.comap k] (k ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      (μ.map (fun ω ↦ (k ω, f ω, g ω))) (s ×ˢ t ×ˢ u) =
        (@Measure.map _ _ _ ((mγ.comap k).prod inferInstance)
          (fun ω ↦ (ω, f ω, g ω)) μ) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.map_apply (by fun_prop) (hs.prod (ht.prod hu)),
      Measure.map_apply _ ((hk_meas hs).prod (ht.prod hu))]
    · simp [Set.mk_preimage_prod]
    · exact (measurable_id.mono le_rfl hk.comap_le).prodMk (by fun_prop)
  have h_right {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k) (s ×ˢ t ×ˢ u) =
        ((Kernel.id ×ₖ
          ((condExpKernel μ (mγ.comap k)).map f ×ₖ (condExpKernel μ (mγ.comap k)).map g)) ∘ₘ
        μ.trim hk.comap_le) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.bind_apply ((hk_meas hs).prod (ht.prod hu)) (by fun_prop),
      Measure.bind_apply (hs.prod (ht.prod hu)) (by fun_prop), lintegral_map ?_ (by fun_prop),
      lintegral_trim]
    rotate_left
    · exact Kernel.measurable_coe _ ((hk_meas hs).prod (ht.prod hu))
    · exact Kernel.measurable_coe _ (hs.prod (ht.prod hu))
    refine lintegral_congr_ae ?_
    filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hf hk ht,
      condDistrib_apply_ae_eq_condExpKernel_map hg hk hu] with a haX haT
    simp only [Kernel.prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ hs]
    rw [@Measure.dirac_apply' _ (mγ.comap k) _ _ (hk_meas hs)]
    congr
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h ↦ ?_⟩
  · convert h (hk_meas hs) ht hu
    · exact h_left hs ht hu
    · exact h_right hs ht hu
  · rintro - t u ⟨s, hs, rfl⟩ ht hu
    convert h hs ht hu
    · exact (h_left hs ht hu).symm
    · exact (h_right hs ht hu).symm

/-- Two random variables `f, g` are conditionally independent given a third `k` iff the
conditional distribution of `f` given `k` and `g` is equal to the conditional distribution of `f`
given `k`. -/
theorem condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k) :
    g ⟂ᵢ[k, hk; μ] f ↔
      condDistrib f (fun ω ↦ (k ω, g ω)) μ =ᵐ[μ.map (fun ω ↦ (k ω, g ω))]
        (condDistrib f k μ).prodMkRight _ := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (μ := μ) _ hf.aemeasurable,
    condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk,
    Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
    calc ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ (μ.map k ⊗ₘ condDistrib g k μ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc]
      congr 2
      have h := Kernel.prod_prodMkRight_comp_deterministic_prod (condDistrib g k μ)
        (condDistrib f k μ) Kernel.id measurable_id
      rw [← Kernel.id] at h
      simpa using h.symm
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
      rw [compProd_map_condDistrib hg.aemeasurable]
  rw [← h_eq]
  have h1 : μ.map (fun x ↦ ((k x, g x), f x)) = (μ.map (fun a ↦ (k a , g a, f a))).map e := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h1_symm : μ.map (fun a ↦ (k a , g a, f a)) =
      (μ.map (fun x ↦ ((k x, g x), f x))).map e.symm := by
    rw [h1, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  have h2 : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      ((Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k).map e := by
    rw [← Measure.deterministic_comp_eq_map e.measurable, Measure.comp_assoc]
    congr 2
    unfold e
    rw [Kernel.deterministic_comp_eq_map, Kernel.prodAssoc_symm_prod]
  have h2_symm : (Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k =
      (((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k).map e.symm := by
    rw [h2, Measure.map_map (by fun_prop) (by fun_prop), MeasurableEquiv.symm_comp_self,
      Measure.map_id]
  rw [h1, h2]
  exact ⟨fun h ↦ by rw [h], fun h ↦ by rw [h1_symm, h1, h2_symm, h2, h]⟩

@[deprecated (since := "2025-10-14")] alias condIndepFun_iff_condDistrib_prod_ae_eq_prodMkLeft :=
  condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight

section iCondIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

@[nontriviality]
lemma iCondIndepFun.of_subsingleton [Subsingleton ι] : iCondIndepFun m' hm' f μ :=
  Kernel.iIndepFun.of_subsingleton

/-- If `f` is a family of mutually conditionally independent random variables
(`iCondIndepFun m' hm' m f μ`) and `S, T` are two disjoint finite index sets, then the tuple formed
by `f i` for `i ∈ S` is conditionally independent of the tuple `(f i)_i` for `i ∈ T`. -/
theorem iCondIndepFun.condIndepFun_finset {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i)) :
    CondIndepFun m' hm' (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

theorem iCondIndepFun.condIndepFun_prodMk {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (hf_Indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

@[deprecated (since := "2025-03-05")]
alias iCondIndepFun.condIndepFun_prod_mk := iCondIndepFun.condIndepFun_prodMk

open Finset in
lemma iCondIndepFun.condIndepFun_prodMk_prodMk (h_indep : iCondIndepFun m' hm' f μ)
    (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l)

@[deprecated (since := "2025-03-05")]
alias iCondIndepFun.condIndepFun_prod_mk_prod_mk := iCondIndepFun.condIndepFun_prodMk_prodMk

end iCondIndepFun

section Mul
variable {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.indepFun_mul_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
lemma iCondIndepFun.indepFun_mul_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iCondIndepFun.indepFun_mul_mul (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

end Mul

section Div
variable {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.indepFun_div_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
lemma iCondIndepFun.indepFun_div_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iCondIndepFun.indepFun_div_div (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
theorem iCondIndepFun.condIndepFun_finset_prod_of_notMem
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i))
    {s : Finset ι} {i : ι} (hi : i ∉ s) :
    CondIndepFun m' hm' (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finset_prod_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2025-05-24")]
alias iCondIndepFun.condIndepFun_finset_sum_of_not_mem :=
  iCondIndepFun.condIndepFun_finset_sum_of_notMem

@[to_additive existing, deprecated (since := "2025-05-24")]
alias iCondIndepFun.condIndepFun_finset_prod_of_not_mem :=
  iCondIndepFun.condIndepFun_finset_prod_of_notMem

@[to_additive]
theorem iCondIndepFun.condIndepFun_prod_range_succ {f : ℕ → Ω → β}
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    CondIndepFun m' hm' (∏ j ∈ Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

end CommMonoid

theorem iCondIndepSet.iCondIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β}
    {s : ι → Set Ω} (hs : iCondIndepSet m' hm' s μ) :
    iCondIndepFun m' hm' (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs

end CondIndepFun

end ProbabilityTheory
