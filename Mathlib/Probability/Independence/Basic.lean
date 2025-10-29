/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Kernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → MeasurableSpace Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `MeasurableSpace.comap f m`.

## Main statements

* `iIndepSets.iIndep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `IndepSets.indep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[μ] Y` for `IndepFun X Y μ`, independence of two random variables.
* `X ⟂ᵢ Y` for `IndepFun X Y volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of independence in this file are a particular case of independence with respect to a
kernel and a measure, as defined in the file `Kernel.lean`.

We provide four definitions of independence:
* `iIndepSets`: independence of a family of sets of sets `pi : ι → Set (Set Ω)`. This is meant to
  be used with π-systems.
* `iIndep`: independence of a family of measurable space structures `m : ι → MeasurableSpace Ω`,
* `iIndepSet`: independence of a family of sets `s : ι → Set Ω`,
* `iIndepFun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `IndepFun` is the version of `iIndepFun`
for two functions.

The definition of independence for `iIndepSets` uses finite sets (`Finset`). See
`ProbabilityTheory.Kernel.iIndepSets`. An alternative and equivalent way of defining independence
would have been to use countable sets.

Most of the definitions and lemmas in this file list all variables instead of using the `variable`
keyword at the beginning of a section, for example
`lemma Indep.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `MeasurableSpace` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`{_mΩ : MeasurableSpace Ω}`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
  Part A, Chapter 4.
-/

assert_not_exists MeasureTheory.Integrable

open MeasureTheory MeasurableSpace Set

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι β γ : Type*} {κ : ι → Type*}

section Definitions

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i) `.
It will be used for families of pi_systems. -/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. -/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`.
We use the notation `f ⟂ᵢ[μ] g` for `IndepFun f g μ` (scoped in `ProbabilityTheory`). -/
def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

end Definitions

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" μ "] " Y:50 => ProbabilityTheory.IndepFun X Y μ

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ " Y:50 => ProbabilityTheory.IndepFun X Y volume

section Definition_lemmas
variable {π : ι → Set (Set Ω)} {m : ι → MeasurableSpace Ω} {_ : MeasurableSpace Ω} {μ : Measure Ω}
  {S : Finset ι} {s : ι → Set Ω}

lemma iIndepSets_iff (π : ι → Set (Set Ω)) (μ : Measure Ω) :
    iIndepSets π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp only [iIndepSets, Kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

lemma iIndepSets.meas_biInter (h : iIndepSets π μ) (s : Finset ι) {f : ι → Set Ω}
    (hf : ∀ i, i ∈ s → f i ∈ π i) : μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) :=
  (iIndepSets_iff _ _).1 h s hf

lemma iIndepSets.isProbabilityMeasure (h : iIndepSets π μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h ∅ (f := fun _ ↦ univ)⟩

lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) (hs : ∀ i, s i ∈ π i) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← h.meas_biInter _ fun _i _ ↦ hs _]

lemma IndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) :
    IndepSets s1 s2 μ ↔ ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (μ (t1 ∩ t2) = μ t1 * μ t2) := by
  simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

lemma iIndep_iff_iIndepSets (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := by
  simp only [iIndep, iIndepSets, Kernel.iIndep]

lemma iIndep.iIndepSets' {m : ι → MeasurableSpace Ω}
    {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : iIndep m μ) :
    iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := (iIndep_iff_iIndepSets _ _).1 hμ

lemma iIndep.isProbabilityMeasure (h : iIndep m μ) : IsProbabilityMeasure μ :=
  h.iIndepSets'.isProbabilityMeasure

lemma iIndep_iff (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → MeasurableSet[m i] (f i)),
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp only [iIndep_iff_iIndepSets, iIndepSets_iff]; rfl

lemma iIndep.meas_biInter (hμ : iIndep m μ) (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i) := (iIndep_iff _ _).1 hμ _ hs

lemma iIndep.meas_iInter [Fintype ι] (hμ : iIndep m μ) (hs : ∀ i, MeasurableSet[m i] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← hμ.meas_biInter fun _ _ ↦ hs _]

lemma Indep_iff_IndepSets (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [Indep, IndepSets, Kernel.Indep]

lemma Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ
      ↔ ∀ t1 t2, MeasurableSet[m₁] t1 → MeasurableSet[m₂] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [Indep_iff_IndepSets, IndepSets_iff]; rfl

lemma iIndepSet_iff_iIndep (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ iIndep (fun i ↦ generateFrom {s i}) μ := by
  simp only [iIndepSet, iIndep, Kernel.iIndepSet]

lemma iIndepSet.isProbabilityMeasure (h : iIndepSet s μ) : IsProbabilityMeasure μ :=
  ((iIndepSet_iff_iIndep _ _).1 h).isProbabilityMeasure

lemma iIndepSet_iff (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ ∀ (s' : Finset ι) {f : ι → Set Ω}
      (_H : ∀ i, i ∈ s' → MeasurableSet[generateFrom {s i}] (f i)),
      μ (⋂ i ∈ s', f i) = ∏ i ∈ s', μ (f i) := by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]

lemma IndepSet_iff_Indep (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ Indep (generateFrom {s}) (generateFrom {t}) μ := by
  simp only [IndepSet, Indep, Kernel.IndepSet]

lemma IndepSet_iff (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ ∀ t1 t2, MeasurableSet[generateFrom {s}] t1
      → MeasurableSet[generateFrom {t}] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  simp only [IndepSet_iff_Indep, Indep_iff]

lemma iIndepFun_iff_iIndep {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ iIndep (fun x ↦ (m x).comap (f x)) μ := by
  simp only [iIndepFun, iIndep, Kernel.iIndepFun]

@[nontriviality, simp]
lemma iIndepSets.of_subsingleton [Subsingleton ι] {m : ι → Set (Set Ω)} [IsProbabilityMeasure μ] :
    iIndepSets m μ := Kernel.iIndepSets.of_subsingleton

@[nontriviality, simp]
lemma iIndep.of_subsingleton [Subsingleton ι] {m : ι → MeasurableSpace Ω} [IsProbabilityMeasure μ] :
    iIndep m μ := Kernel.iIndep.of_subsingleton

@[nontriviality, simp]
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} [IsProbabilityMeasure μ] : iIndepFun f μ :=
  Kernel.iIndepFun.of_subsingleton

protected lemma iIndepFun.iIndep {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) :
    iIndep (fun x ↦ (m x).comap (f x)) μ := hf

lemma iIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ ∀ (s : Finset ι) {f' : ι → Set Ω}
      (_H : ∀ i, i ∈ s → MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) := by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]

lemma iIndepFun.meas_biInter {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) (hs : ∀ i, i ∈ S → MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i) := hf.iIndep.meas_biInter hs

lemma iIndepFun.meas_iInter [Fintype ι] {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun f μ) (hs : ∀ i, MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := hf.iIndep.meas_iInter hs

lemma IndepFun_iff_Indep [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ := by
  simp only [IndepFun, Indep, Kernel.IndepFun]

lemma IndepFun_iff {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ ∀ t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      → MeasurableSet[MeasurableSpace.comap g mγ] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [IndepFun_iff_Indep, Indep_iff]

lemma IndepFun.meas_inter [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    (hfg : f ⟂ᵢ[μ] g) {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s)
    (ht : MeasurableSet[mγ.comap g] t) :
    μ (s ∩ t) = μ s * μ t :=
  (IndepFun_iff _ _ _).1 hfg _ _ hs ht

end Definition_lemmas

section Indep

variable {m₁ m₂ m₃ : MeasurableSpace Ω} (m' : MeasurableSpace Ω)
  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

@[symm]
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ :=
  Kernel.IndepSets.symm h

@[symm]
theorem Indep.symm (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h

theorem indep_bot_right [IsZeroOrProbabilityMeasure μ] : Indep m' ⊥ μ :=
  Kernel.indep_bot_right m'

theorem indep_bot_left [IsZeroOrProbabilityMeasure μ] : Indep ⊥ m' μ := (indep_bot_right m').symm

theorem indepSet_empty_right [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet s ∅ μ :=
  Kernel.indepSet_empty_right s

theorem indepSet_empty_left [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet ∅ s μ :=
  Kernel.indepSet_empty_left s

theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    IndepSets s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31

theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    IndepSets s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32

theorem indep_of_indep_of_le_left (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
    Indep m₃ m₂ μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31

theorem indep_of_indep_of_le_right (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
    Indep m₁ m₃ μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32

theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ) :
    IndepSets (s₁ ∪ s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    IndepSets (s₁ ∪ s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  Kernel.IndepSets.union_iff

theorem IndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ n, IndepSets (s n) s' μ) :
    IndepSets (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp

theorem IndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋃ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bUnion hyp

@[deprecated (since := "2025-10-28")] alias IndepSets.bUnion := IndepSets.biUnion

theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) (h₁ : IndepSets s₁ s' μ) :
    IndepSets (s₁ ∩ s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁

theorem IndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, IndepSets (s n) s' μ) :
    IndepSets (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h

theorem IndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋂ n ∈ u, s n) s' μ :=
  Kernel.IndepSets.bInter h

theorem indepSets_singleton_iff {s t : Set Ω} :
    IndepSets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t := by
  simp only [IndepSets, Kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromIndepToIndep

variable {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem iIndepSets.indepSets {s : ι → Set (Set Ω)}
    (h_indep : iIndepSets s μ) {i j : ι} (hij : i ≠ j) : IndepSets (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij

theorem iIndep.indep
    (h_indep : iIndep m μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) μ :=
  Kernel.iIndep.indep h_indep hij

theorem iIndepFun.indepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun f μ) {i j : ι}
    (hij : i ≠ j) :
    f i ⟂ᵢ[μ] f j :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

variable {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

theorem iIndep.iIndepSets
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : iIndep m μ) :
    iIndepSets s μ :=
  Kernel.iIndep.iIndepSets hms h_indep

theorem Indep.indepSets {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) :
    IndepSets s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

variable {m : ι → MeasurableSpace Ω} {m1 m2 _mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

theorem IndepSets.indep [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ _mΩ) (h2 : m2 ≤ _mΩ) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) :
    Indep m1 m2 μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

theorem IndepSets.indep' [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
    Indep (generateFrom p1) (generateFrom p2) μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

theorem indepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

theorem iIndepSet.indep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

theorem indep_iSup_of_disjoint
    (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST

theorem indep_iSup_of_directed_le
    [IsZeroOrProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m1 μ)
    (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

theorem iIndepSet.indep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

theorem iIndepSet.indep_generateFrom_le [Preorder ι]
    {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

theorem iIndepSet.indep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

theorem indep_iSup_of_monotone [SemilatticeSup ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Monotone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

theorem indep_iSup_of_antitone [SemilatticeInf ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Antitone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

theorem iIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

@[deprecated (since := "2025-05-23")]
alias iIndepSets.piiUnionInter_of_not_mem := iIndepSets.piiUnionInter_of_notMem

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem iIndepSets.iIndep
    (h_le : ∀ i, m i ≤ _mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π μ) :
    iIndep m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `IndepSet s t μ ↔ IndepSets {s} {t} μ`.
-/


variable {m₁ m₂ _mΩ : MeasurableSpace Ω} {μ : Measure Ω} {s t : Set Ω} (S T : Set (Set Ω))

theorem indepSet_iff_indepSets_singleton (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

theorem indepSet_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff

lemma IndepSet.measure_inter_eq_mul {μ : Measure Ω} (h : IndepSet s t μ) :
    μ (s ∩ t) = μ s * μ t := by
  simpa using Kernel.IndepSet.measure_inter_eq_mul _ _ h

theorem IndepSets.indepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by volume_tac) [IsZeroOrProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) :
    IndepSet s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

theorem Indep.indepSet_of_measurableSet
    (h_indep : Indep m₁ m₂ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s) (ht : MeasurableSet[m₂] t) :
    IndepSet s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

theorem indep_iff_forall_indepSet (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

theorem iIndep_comap_mem_iff {f : ι → Set Ω} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) μ ↔ iIndepSet f μ :=
  Kernel.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff

theorem iIndepSets_singleton_iff {s : ι → Set Ω} :
    iIndepSets (fun i ↦ {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i ∈ t, μ (s i) := by
  simp_rw [iIndepSets, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

theorem iIndepSet.meas_biInter {f : ι → Set Ω} (h : iIndepSet f μ) (s : Finset ι) :
    μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simpa using Kernel.iIndepSet.meas_biInter h s

theorem iIndepSet_iff_iIndepSets_singleton {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ iIndepSets (fun i ↦ {f i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hf

theorem iIndepSet_iff_meas_biInter {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ ∀ s, μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp_rw [iIndepSet, Kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

theorem iIndepSets.iIndepSet_of_mem {π : ι → Set (Set Ω)} {f : ι → Set Ω}
    (hfπ : ∀ i, f i ∈ π i) (hf : ∀ i, MeasurableSet (f i))
    (hπ : iIndepSets π μ) : iIndepSet f μ :=
  Kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    f ⟂ᵢ[μ] g ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  simp only [IndepFun, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} :
    iIndepFun f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i ∈ S, μ (f i ⁻¹' sets i) := by
  simp only [iIndepFun, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun_congr {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (h : ∀ i, f i =ᵐ[μ] g i) :
    iIndepFun f μ ↔ iIndepFun g μ := Kernel.iIndepFun_congr' (by simp [h])

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

nonrec lemma iIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f μ) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i ↦ g i ∘ f i) μ := h.comp _ hg

nonrec lemma iIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f μ) (g : ∀ i, β i → γ i)
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ i, AEMeasurable (g i) (μ.map (f i))) :
    iIndepFun (fun i ↦ g i ∘ f i) μ := h.comp₀ _ (by simp [hf]) (by simp [hg])

theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    f ⟂ᵢ[μ] g ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [IndepFun, IndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

theorem indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ.map (fun ω ↦ (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg ht],
      (Measure.map_apply_of_aemeasurable (hf.prodMk hg) (hs.prod ht)).symm⟩
  constructor
  · refine fun h ↦ (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [← (h₀ hs ht).1, ← (h₀ hs ht).2, h s t hs ht]
  · intro h s t hs ht
    rw [(h₀ hs ht).1, (h₀ hs ht).2, h, Measure.prod_prod]

theorem indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  apply indepFun_iff_map_prod_eq_prod_map_map' hf hg <;> apply IsFiniteMeasure.toSigmaFinite

theorem iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f : Π i, Ω → β i} [IsProbabilityMeasure μ]
    (hf : ∀ i, AEMeasurable (f i) μ) :
    iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i)) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : ∀ i, Set (β i)} (hm : ∀ (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i ↦ f i ω) (univ.pi s) := by
    constructor
    · congr with x
      rw [Measure.map_apply_of_aemeasurable (hf x) (hm x)]
    · rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun x ↦ hf x)
        (.univ_pi hm)]
      congr with x
      simp
  constructor
  · refine fun hS ↦ (Measure.pi_eq fun h hm ↦ ?_).symm
    rw [← (h₀ hm).1, ← (h₀ hm).2]
    simpa [hm] using hS Finset.univ (sets := h)
  · intro h S s hs
    specialize h₀ (s := fun i ↦ if i ∈ S then s i else univ)
      fun i ↦ by beta_reduce; split_ifs with hiS <;> simp [hiS, hs]
    simp only [apply_ite, preimage_univ, measure_univ, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_ite, Finset.filter_univ_mem, iInter_ite, iInter_univ, inter_univ, h,
      Measure.pi_pi] at h₀
    rw [h₀.2, ← h₀.1]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : f ⟂ᵢ[μ] g) : g ⟂ᵢ[μ] f := hfg.symm

theorem IndepFun.congr {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : f ⟂ᵢ[μ] g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    f' ⟂ᵢ[μ] g' := by
  refine Kernel.IndepFun.congr' hfg ?_ ?_ <;> simpa

@[deprecated (since := "2025-03-18")] alias IndepFun.ae_eq := IndepFun.congr

section Prod

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] {X : Ω → 𝓧} {Y : Ω' → 𝓨}

/-- Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when viewed as random
variables defined on the product space `Ω × Ω'`. -/
lemma indepFun_prod (mX : Measurable X) (mY : Measurable Y) :
    (fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2) := by
  refine indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) |>.2 ?_
  convert Measure.map_prod_map μ ν mX mY |>.symm
  · rw [← Function.comp_def, ← Measure.map_map mX measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
  · rw [← Function.comp_def, ← Measure.map_map mY measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]

/-- Given random variables `X : Ω → 𝓧` and `Y : Ω' → 𝓨`, they are independent when viewed as random
variables defined on the product space `Ω × Ω'`. -/
lemma indepFun_prod₀ (mX : AEMeasurable X μ) (mY : AEMeasurable Y ν) :
    (fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2) := by
  have : (fun ω ↦ mX.mk X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ mY.mk Y ω.2) :=
    indepFun_prod mX.measurable_mk mY.measurable_mk
  refine this.congr ?_ ?_
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_fst.aemeasurable
    · rw [measurePreserving_fst.map_eq]
      exact (AEMeasurable.ae_eq_mk mX).symm
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_snd.aemeasurable
    · rw [measurePreserving_snd.map_eq]
      exact (AEMeasurable.ae_eq_mk mY).symm

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}

/-- Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as random
variables defined on the product space `Π i, Ω i`. -/
lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  refine iIndepFun_iff_map_fun_eq_pi_map ?_ |>.2 ?_
  · exact fun i ↦ (mX i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [Measure.pi_map_pi mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval μ i).map_eq, AEMeasurable.map_map_of_aemeasurable,
    Function.comp_def]
  · rw [(measurePreserving_eval μ i).map_eq]
    exact mX i
  · exact (measurable_pi_apply i).aemeasurable

end Prod

theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g :=
  Kernel.IndepFun.comp hfg hφ hψ

theorem IndepFun.comp₀ {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hφ : AEMeasurable φ (μ.map f)) (hψ : AEMeasurable ψ (μ.map g)) :
    (φ ∘ f) ⟂ᵢ[μ] (ψ ∘ g) :=
  Kernel.IndepFun.comp₀ hfg (by simp [hf]) (by simp [hg]) (by simp [hφ]) (by simp [hψ])

lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (c : β) (X : Ω → β') :
    (fun _ ↦ c) ⟂ᵢ[μ] X :=
  Kernel.indepFun_const_left c X

lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (X : Ω → β) (c : β') :
    X ⟂ᵢ[μ] (fun _ ↦ c) :=
  Kernel.indepFun_const_right X c

theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : f ⟂ᵢ[μ] g) :
    f ⟂ᵢ[μ] (-g) := hfg.comp measurable_id measurable_neg

theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : f ⟂ᵢ[μ] g) :
    (-f) ⟂ᵢ[μ] g := hfg.comp measurable_neg measurable_id

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

lemma iIndepFun.isProbabilityMeasure (h : iIndepFun f μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ ↦ univ)⟩

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ :=
  Kernel.iIndepFun.indepFun_finset₀ S T hST hf_Indep (by simp [hf_meas])

lemma iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

@[deprecated (since := "2025-03-05")]
alias iIndepFun.indepFun_prod_mk := iIndepFun.indepFun_prodMk

lemma iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk₀ hf_Indep (by simp [hf_meas]) i j k hik hjk

lemma iIndepFun.indepFun_prodMk_prodMk (h_indep : iIndepFun f μ) (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk h_indep hf i j k l hik hil hjk hjl

@[deprecated (since := "2025-03-05")]
alias iIndepFun.indepFun_prod_mk_prod_mk := iIndepFun.indepFun_prodMk_prodMk

lemma iIndepFun.indepFun_prodMk_prodMk₀ (h_indep : iIndepFun f μ) (hf : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk₀ h_indep (by simp [hf]) i j k l hik hil hjk hjl

variable {ι' : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

open Function in
lemma iIndepFun.precomp {g : ι' → ι} (hg : g.Injective) (h : iIndepFun f μ) :
    iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  nontriviality ι'
  have A (x) : Function.invFun g (g x) = x := Function.leftInverse_invFun hg x
  rw [iIndepFun_iff] at h ⊢
  intro t s' hs'
  simpa [A] using h (t.map ⟨g, hg⟩) (f' := fun i ↦ s' (invFun g i)) (by simpa [A] using hs')

lemma iIndepFun_iff_finset : iIndepFun f μ ↔ ∀ s : Finset ι, iIndepFun (s.restrict f) μ where
  mp h s := h.precomp (g := ((↑) : s → ι)) Subtype.val_injective
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i ∈ s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort, this]
    exact (h s).meas_iInter fun i ↦ hs i i.2

lemma iIndepFun.of_precomp {g : ι' → ι} (hg : g.Surjective)
    (h : iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ) : iIndepFun f μ := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  nontriviality ι
  have := hg.nontrivial
  classical
  rw [iIndepFun_iff] at h ⊢
  intro t s hs
  have A (x) : g (Function.invFun g x) = x := Function.rightInverse_invFun hg x
  have : ∀ i ∈ Finset.image (Function.invFun g) t,
    @MeasurableSet _ (MeasurableSpace.comap (f <| g i) (m <| g i)) (s <| g i) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa [A] using (A j).symm ▸ hs j hj
  have eq : ∏ i ∈ Finset.image (Function.invFun g) t, μ (s (g i)) = ∏ i ∈ t, μ (s i) := by
    rw [Finset.prod_image (fun x hx y hy h => ?_), Finset.prod_congr rfl (fun x _ => by rw [A])]
    rw [← A x, ← A y, h]
  simpa [A, eq] using h (t.image (Function.invFun g)) (f' := fun i ↦ s (g i)) this

lemma iIndepFun_precomp_of_bijective {g : ι' → ι} (hg : g.Bijective) :
    iIndepFun (m := fun i ↦ m (g i)) (fun i ↦ f (g i)) μ ↔ iIndepFun f μ where
  mp := .of_precomp hg.surjective
  mpr := .precomp hg.injective

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_finset_prod_of_notMem (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finset_prod_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2025-05-23")]
alias iIndepFun.indepFun_finset_sum_of_not_mem := iIndepFun.indepFun_finset_sum_of_notMem

@[to_additive existing, deprecated (since := "2025-05-23")]
alias iIndepFun.indepFun_finset_prod_of_not_mem := iIndepFun.indepFun_finset_prod_of_notMem

@[to_additive]
lemma iIndepFun.indepFun_finset_prod_of_notMem₀ (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finset_prod_of_notMem₀ hf_Indep (by simp [hf_meas]) hi

@[deprecated (since := "2025-05-23")]
alias iIndepFun.indepFun_finset_sum_of_not_mem₀ := iIndepFun.indepFun_finset_sum_of_notMem₀

@[to_additive existing, deprecated (since := "2025-05-23")]
alias iIndepFun.indepFun_finset_prod_of_not_mem₀ := iIndepFun.indepFun_finset_prod_of_notMem₀

@[to_additive]
lemma iIndepFun.indepFun_prod_range_succ {f : ℕ → Ω → β} (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) : IndepFun (∏ j ∈ Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

@[to_additive]
lemma iIndepFun.indepFun_prod_range_succ₀ {f : ℕ → Ω → β} (hf_Indep : iIndepFun f μ)
    (hf_meas : ∀ i, AEMeasurable (f i) μ) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFun_finset_prod_of_notMem₀ hf_meas (by simp)

end CommMonoid

theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs

end IndepFun

variable {ι Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {X : ι → Ω → α} {Y : ι → Ω → β} {f : _ → Set Ω}
  {t : ι → Set β} {s : Finset ι}

/-- The probability of an intersection of preimages conditioning on another intersection factors
into a product. -/
lemma cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : ∀ i ∉ s, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    μ[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, μ[f i | Y i in t i] := by
  have : IsProbabilityMeasure (μ : Measure Ω) := hindep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'
  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
      rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      congr
      calc
        _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else .univ := by
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      rw [hindep.meas_iInter]
      exact fun i ↦ ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * ∏ i, μ (g i) := by
      rw [hindep.meas_iInter]
      intro i
      by_cases hi : i ∈ s <;> simp only [hi, ↓reduceIte, g]
      · obtain ⟨A, hA, hA'⟩ := hf i hi
        exact .inter ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
          ⟨A ×ˢ Set.univ, hA.prod .univ, by ext; simp [← hA']⟩
      · exact ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = ∏ i, (μ (Y i ⁻¹' t i))⁻¹ * μ (g i) := by
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ i _ _ ↦ .inr <| measure_ne_top _ _
    _ = ∏ i, if i ∈ s then μ[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top μ _)]
    _ = _ := by simp

lemma iIndepFun.cond [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hy : ∀ i, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    iIndepFun X μ[|⋂ i, Y i ⁻¹' t i] := by
  rw [iIndepFun_iff]
  intro s f hf
  convert cond_iInter hY hindep hf (fun i _ ↦ hy _) ht using 2 with i hi
  simpa using cond_iInter hY hindep (fun j hj ↦ hf _ <| Finset.mem_singleton.1 hj ▸ hi)
    (fun i _ ↦ hy _) ht

section Monoid

variable {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]

@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map₀'
    {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  conv in f * g => change (fun x ↦ x.1 * x.2) ∘ (fun ω ↦ (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg),
    (indepFun_iff_map_prod_eq_prod_map_map' hf hg σf σg).mp hfg, Measure.mconv]

@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map'
    {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀' hf.aemeasurable hg.aemeasurable σf σg

@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map₀
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  apply hfg.map_mul_eq_map_mconv_map₀' hf hg
    <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable

end Monoid

end ProbabilityTheory
