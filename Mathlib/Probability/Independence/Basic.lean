/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Kernel

#align_import probability.independence.basic from "leanprover-community/mathlib"@"001ffdc42920050657fd45bd2b8bfbec8eaaeb29"

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
`ProbabilityTheory.kernel.iIndepSets`. An alternative and equivalent way of defining independence
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
  kernel.iIndepSets π (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets ProbabilityTheory.iIndepSets

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.IndepSets s1 s2 (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
#align probability_theory.indep_sets ProbabilityTheory.IndepSets

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. -/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  kernel.iIndep m (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep ProbabilityTheory.iIndep

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.Indep m₁ m₂ (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
#align probability_theory.indep ProbabilityTheory.Indep

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.iIndepSet s (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set ProbabilityTheory.iIndepSet

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.IndepSet s t (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
#align probability_theory.indep_set ProbabilityTheory.IndepSet

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*} (m : ∀ x : ι, MeasurableSpace (β x))
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.iIndepFun m f (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun ProbabilityTheory.iIndepFun

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`. -/
def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  kernel.IndepFun f g (kernel.const Unit μ) (Measure.dirac () : Measure Unit)
#align probability_theory.indep_fun ProbabilityTheory.IndepFun

end Definitions

section Definition_lemmas
variable {π : ι → Set (Set Ω)} {m : ι → MeasurableSpace Ω} {_ : MeasurableSpace Ω} {μ : Measure Ω}
  {S : Finset ι} {s : ι → Set Ω}

lemma iIndepSets_iff (π : ι → Set (Set Ω)) (μ : Measure Ω) :
    iIndepSets π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
      μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp only [iIndepSets, kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, kernel.const_apply]

lemma iIndepSets.meas_biInter (h : iIndepSets π μ) (s : Finset ι) {f : ι → Set Ω}
    (hf : ∀ i, i ∈ s → f i ∈ π i) : μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) :=
  (iIndepSets_iff _ _).1 h s hf

lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) (hs : ∀ i, s i ∈ π i) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← h.meas_biInter _ fun _i _ ↦ hs _]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.meas_Inter ProbabilityTheory.iIndepSets.meas_iInter

lemma IndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) :
    IndepSets s1 s2 μ ↔ ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (μ (t1 ∩ t2) = μ t1 * μ t2) := by
  simp only [IndepSets, kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, kernel.const_apply]

lemma iIndep_iff_iIndepSets (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := by
  simp only [iIndep, iIndepSets, kernel.iIndep]

lemma iIndep.iIndepSets' {m : ι → MeasurableSpace Ω}
    {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : iIndep m μ) :
    iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) μ := (iIndep_iff_iIndepSets _ _).1 hμ

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
  simp only [Indep, IndepSets, kernel.Indep]

lemma Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ
      ↔ ∀ t1 t2, MeasurableSet[m₁] t1 → MeasurableSet[m₂] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [Indep_iff_IndepSets, IndepSets_iff]; rfl

lemma iIndepSet_iff_iIndep (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ iIndep (fun i ↦ generateFrom {s i}) μ := by
  simp only [iIndepSet, iIndep, kernel.iIndepSet]

lemma iIndepSet_iff (s : ι → Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ ∀ (s' : Finset ι) {f : ι → Set Ω}
      (_H : ∀ i, i ∈ s' → MeasurableSet[generateFrom {s i}] (f i)),
      μ (⋂ i ∈ s', f i) = ∏ i ∈ s', μ (f i) := by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]

lemma IndepSet_iff_Indep (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ Indep (generateFrom {s}) (generateFrom {t}) μ := by
  simp only [IndepSet, Indep, kernel.IndepSet]

lemma IndepSet_iff (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ ∀ t1 t2, MeasurableSet[generateFrom {s}] t1
      → MeasurableSet[generateFrom {t}] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  simp only [IndepSet_iff_Indep, Indep_iff]

lemma iIndepFun_iff_iIndep {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun m f μ ↔ iIndep (fun x ↦ (m x).comap (f x)) μ := by
  simp only [iIndepFun, iIndep, kernel.iIndepFun]

protected lemma iIndepFun.iIndep {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun m f μ) :
    iIndep (fun x ↦ (m x).comap (f x)) μ := hf

lemma iIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x) (μ : Measure Ω) :
    iIndepFun m f μ ↔ ∀ (s : Finset ι) {f' : ι → Set Ω}
      (_H : ∀ i, i ∈ s → MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) := by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]

lemma iIndepFun.meas_biInter {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun m f μ) (hs : ∀ i, i ∈ S → MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i) := hf.iIndep.meas_biInter hs

lemma iIndepFun.meas_iInter [Fintype ι] {m : ∀ i, MeasurableSpace (κ i)} {f : ∀ x : ι, Ω → κ x}
    (hf : iIndepFun m f μ) (hs : ∀ i, MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := hf.iIndep.meas_iInter hs

lemma IndepFun_iff_Indep [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    IndepFun f g μ ↔ Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ := by
  simp only [IndepFun, Indep, kernel.IndepFun]

lemma IndepFun_iff {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    IndepFun f g μ ↔ ∀ t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      → MeasurableSet[MeasurableSpace.comap g mγ] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 := by
  rw [IndepFun_iff_Indep, Indep_iff]

lemma IndepFun.meas_inter [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    (hfg : IndepFun f g μ) {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s)
    (ht : MeasurableSet[mγ.comap g] t) :
    μ (s ∩ t) = μ s * μ t :=
  (IndepFun_iff _ _ _).1 hfg _ _ hs ht

end Definition_lemmas

section Indep

variable {m₁ m₂ m₃ : MeasurableSpace Ω} (m' : MeasurableSpace Ω)
  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

@[symm]
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ :=
  kernel.IndepSets.symm h
#align probability_theory.indep_sets.symm ProbabilityTheory.IndepSets.symm

@[symm]
theorem Indep.symm (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h
#align probability_theory.indep.symm ProbabilityTheory.Indep.symm

theorem indep_bot_right [IsProbabilityMeasure μ] : Indep m' ⊥ μ :=
  kernel.indep_bot_right m'
#align probability_theory.indep_bot_right ProbabilityTheory.indep_bot_right

theorem indep_bot_left [IsProbabilityMeasure μ] : Indep ⊥ m' μ := (indep_bot_right m').symm
#align probability_theory.indep_bot_left ProbabilityTheory.indep_bot_left

theorem indepSet_empty_right [IsProbabilityMeasure μ] (s : Set Ω) : IndepSet s ∅ μ :=
  kernel.indepSet_empty_right s
#align probability_theory.indep_set_empty_right ProbabilityTheory.indepSet_empty_right

theorem indepSet_empty_left [IsProbabilityMeasure μ] (s : Set Ω) : IndepSet ∅ s μ :=
  kernel.indepSet_empty_left s
#align probability_theory.indep_set_empty_left ProbabilityTheory.indepSet_empty_left

theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    IndepSets s₃ s₂ μ :=
  kernel.indepSets_of_indepSets_of_le_left h_indep h31
#align probability_theory.indep_sets_of_indep_sets_of_le_left ProbabilityTheory.indepSets_of_indepSets_of_le_left

theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    IndepSets s₁ s₃ μ :=
  kernel.indepSets_of_indepSets_of_le_right h_indep h32
#align probability_theory.indep_sets_of_indep_sets_of_le_right ProbabilityTheory.indepSets_of_indepSets_of_le_right

theorem indep_of_indep_of_le_left (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
    Indep m₃ m₂ μ :=
  kernel.indep_of_indep_of_le_left h_indep h31
#align probability_theory.indep_of_indep_of_le_left ProbabilityTheory.indep_of_indep_of_le_left

theorem indep_of_indep_of_le_right (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
    Indep m₁ m₃ μ :=
  kernel.indep_of_indep_of_le_right h_indep h32
#align probability_theory.indep_of_indep_of_le_right ProbabilityTheory.indep_of_indep_of_le_right

theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ) :
    IndepSets (s₁ ∪ s₂) s' μ :=
  kernel.IndepSets.union h₁ h₂
#align probability_theory.indep_sets.union ProbabilityTheory.IndepSets.union

@[simp]
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    IndepSets (s₁ ∪ s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  kernel.IndepSets.union_iff
#align probability_theory.indep_sets.union_iff ProbabilityTheory.IndepSets.union_iff

theorem IndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ n, IndepSets (s n) s' μ) :
    IndepSets (⋃ n, s n) s' μ :=
  kernel.IndepSets.iUnion hyp
#align probability_theory.indep_sets.Union ProbabilityTheory.IndepSets.iUnion

theorem IndepSets.bUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋃ n ∈ u, s n) s' μ :=
  kernel.IndepSets.bUnion hyp
#align probability_theory.indep_sets.bUnion ProbabilityTheory.IndepSets.bUnion

theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) (h₁ : IndepSets s₁ s' μ) :
    IndepSets (s₁ ∩ s₂) s' μ :=
  kernel.IndepSets.inter s₂ h₁
#align probability_theory.indep_sets.inter ProbabilityTheory.IndepSets.inter

theorem IndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, IndepSets (s n) s' μ) :
    IndepSets (⋂ n, s n) s' μ :=
  kernel.IndepSets.iInter h
#align probability_theory.indep_sets.Inter ProbabilityTheory.IndepSets.iInter

theorem IndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋂ n ∈ u, s n) s' μ :=
  kernel.IndepSets.bInter h
#align probability_theory.indep_sets.bInter ProbabilityTheory.IndepSets.bInter

theorem indepSets_singleton_iff {s t : Set Ω} :
    IndepSets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t := by
  simp only [IndepSets, kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    kernel.const_apply]
#align probability_theory.indep_sets_singleton_iff ProbabilityTheory.indepSets_singleton_iff

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromIndepToIndep

variable {m : ι → MeasurableSpace Ω}  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem iIndepSets.indepSets {s : ι → Set (Set Ω)}
    (h_indep : iIndepSets s μ) {i j : ι} (hij : i ≠ j) : IndepSets (s i) (s j) μ :=
  kernel.iIndepSets.indepSets h_indep hij
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.indep_sets ProbabilityTheory.iIndepSets.indepSets

theorem iIndep.indep
    (h_indep : iIndep m μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) μ :=
  kernel.iIndep.indep h_indep hij
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep.indep ProbabilityTheory.iIndep.indep

theorem iIndepFun.indepFun {β : ι → Type*}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun m f μ) {i j : ι}
    (hij : i ≠ j) :
    IndepFun (f i) (f j) μ :=
  kernel.iIndepFun.indepFun hf_Indep hij
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun ProbabilityTheory.iIndepFun.indepFun

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
  kernel.iIndep.iIndepSets hms h_indep
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep.Indep_sets ProbabilityTheory.iIndep.iIndepSets

theorem Indep.indepSets {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) :
    IndepSets s1 s2 μ :=
  kernel.Indep.indepSets h_indep
#align probability_theory.indep.indep_sets ProbabilityTheory.Indep.indepSets

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

variable {m : ι → MeasurableSpace Ω} {m1 m2 _mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

theorem IndepSets.indep [IsProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ _mΩ) (h2 : m2 ≤ _mΩ) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) :
    Indep m1 m2 μ :=
  kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp
#align probability_theory.indep_sets.indep ProbabilityTheory.IndepSets.indep

theorem IndepSets.indep' [IsProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
    Indep (generateFrom p1) (generateFrom p2) μ :=
  kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp
#align probability_theory.indep_sets.indep' ProbabilityTheory.IndepSets.indep'

theorem indepSets_piiUnionInter_of_disjoint [IsProbabilityMeasure μ] {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) μ :=
  kernel.indepSets_piiUnionInter_of_disjoint h_indep hST
#align probability_theory.indep_sets_pi_Union_Inter_of_disjoint ProbabilityTheory.indepSets_piiUnionInter_of_disjoint

theorem iIndepSet.indep_generateFrom_of_disjoint [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ :=
  kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_of_disjoint ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint

theorem indep_iSup_of_disjoint [IsProbabilityMeasure μ]
    (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
  kernel.indep_iSup_of_disjoint h_le h_indep hST
#align probability_theory.indep_supr_of_disjoint ProbabilityTheory.indep_iSup_of_disjoint

theorem indep_iSup_of_directed_le
    [IsProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m1 μ)
    (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m1 μ :=
  kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm
#align probability_theory.indep_supr_of_directed_le ProbabilityTheory.indep_iSup_of_directed_le

theorem iIndepSet.indep_generateFrom_lt [Preorder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ :=
  kernel.iIndepSet.indep_generateFrom_lt hsm hs i
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_lt ProbabilityTheory.iIndepSet.indep_generateFrom_lt

theorem iIndepSet.indep_generateFrom_le [LinearOrder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ :=
  kernel.iIndepSet.indep_generateFrom_le hsm hs i hk
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_le ProbabilityTheory.iIndepSet.indep_generateFrom_le

theorem iIndepSet.indep_generateFrom_le_nat [IsProbabilityMeasure μ] {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_le_nat ProbabilityTheory.iIndepSet.indep_generateFrom_le_nat

theorem indep_iSup_of_monotone [SemilatticeSup ι] [IsProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Monotone m) :
    Indep (⨆ i, m i) m1 μ :=
  kernel.indep_iSup_of_monotone h_indep h_le h_le' hm
#align probability_theory.indep_supr_of_monotone ProbabilityTheory.indep_iSup_of_monotone

theorem indep_iSup_of_antitone [SemilatticeInf ι] [IsProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m1 μ) (h_le : ∀ i, m i ≤ _mΩ) (h_le' : m1 ≤ _mΩ) (hm : Antitone m) :
    Indep (⨆ i, m i) m1 μ :=
  kernel.indep_iSup_of_antitone h_indep h_le h_le' hm
#align probability_theory.indep_supr_of_antitone ProbabilityTheory.indep_iSup_of_antitone

theorem iIndepSets.piiUnionInter_of_not_mem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) μ :=
  kernel.iIndepSets.piiUnionInter_of_not_mem hp_ind haS
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.pi_Union_Inter_of_not_mem ProbabilityTheory.iIndepSets.piiUnionInter_of_not_mem

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem iIndepSets.iIndep [IsProbabilityMeasure μ]
    (h_le : ∀ i, m i ≤ _mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π μ) :
    iIndep m μ :=
  kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.Indep ProbabilityTheory.iIndepSets.iIndep

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
    [IsProbabilityMeasure μ] : IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _
#align probability_theory.indep_set_iff_indep_sets_singleton ProbabilityTheory.indepSet_iff_indepSets_singleton

theorem indepSet_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff
#align probability_theory.indep_set_iff_measure_inter_eq_mul ProbabilityTheory.indepSet_iff_measure_inter_eq_mul

theorem IndepSets.indepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) :
    IndepSet s t μ :=
  kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep
#align probability_theory.indep_sets.indep_set_of_mem ProbabilityTheory.IndepSets.indepSet_of_mem

theorem Indep.indepSet_of_measurableSet
    (h_indep : Indep m₁ m₂ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s) (ht : MeasurableSet[m₂] t) :
    IndepSet s t μ :=
  kernel.Indep.indepSet_of_measurableSet h_indep hs ht
#align probability_theory.indep.indep_set_of_measurable_set ProbabilityTheory.Indep.indepSet_of_measurableSet

theorem indep_iff_forall_indepSet (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ :=
  kernel.indep_iff_forall_indepSet m₁ m₂ _ _
#align probability_theory.indep_iff_forall_indep_set ProbabilityTheory.indep_iff_forall_indepSet

theorem iIndep_comap_mem_iff {f : ι → Set Ω} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) μ ↔ iIndepSet f μ :=
  kernel.iIndep_comap_mem_iff
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_comap_mem_iff ProbabilityTheory.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.Indep_comap_mem ProbabilityTheory.iIndepSet.iIndep_comap_mem

theorem iIndepSets_singleton_iff {s : ι → Set Ω} :
    iIndepSets (fun i ↦ {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i ∈ t, μ (s i) := by
  simp_rw [iIndepSets, kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    kernel.const_apply]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets_singleton_iff ProbabilityTheory.iIndepSets_singleton_iff

variable [IsProbabilityMeasure μ]

theorem iIndepSet_iff_iIndepSets_singleton {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ iIndepSets (fun i ↦ {f i}) μ :=
  kernel.iIndepSet_iff_iIndepSets_singleton hf
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set_iff_Indep_sets_singleton ProbabilityTheory.iIndepSet_iff_iIndepSets_singleton

theorem iIndepSet_iff_meas_biInter {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ ∀ s, μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
  simp_rw [iIndepSet, kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    kernel.const_apply]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set_iff_measure_Inter_eq_prod ProbabilityTheory.iIndepSet_iff_meas_biInter

theorem iIndepSets.iIndepSet_of_mem {π : ι → Set (Set Ω)} {f : ι → Set Ω}
    (hfπ : ∀ i, f i ∈ π i) (hf : ∀ i, MeasurableSet (f i))
    (hπ : iIndepSets π μ) : iIndepSet f μ :=
  kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.Indep_set_of_mem ProbabilityTheory.iIndepSets.iIndepSet_of_mem

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFun f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  simp only [IndepFun, kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, kernel.const_apply]
#align probability_theory.indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    iIndepFun m f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i ∈ S, μ (f i ⁻¹' sets i) := by
  simp only [iIndepFun, kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, kernel.const_apply]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul

theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [IndepFun, IndepSet, kernel.indepFun_iff_indepSet_preimage hf hg, ae_dirac_eq,
    Filter.eventually_pure, kernel.const_apply]
#align probability_theory.indep_fun_iff_indep_set_preimage ProbabilityTheory.indepFun_iff_indepSet_preimage

theorem indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    IndepFun f g μ ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ.map (fun ω ↦ (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg ht],
      (Measure.map_apply_of_aemeasurable (hf.prod_mk hg) (hs.prod ht)).symm⟩
  constructor
  · refine fun h ↦ (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [← (h₀ hs ht).1, ← (h₀ hs ht).2, h s t hs ht]
  · intro h s t hs ht
    rw [(h₀ hs ht).1, (h₀ hs ht).2, h, Measure.prod_prod]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g μ) : IndepFun g f μ := hfg.symm
#align probability_theory.indep_fun.symm ProbabilityTheory.IndepFun.symm

theorem IndepFun.ae_eq {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : IndepFun f g μ)
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') : IndepFun f' g' μ := by
  refine kernel.IndepFun.ae_eq hfg ?_ ?_ <;>
    simp only [ae_dirac_eq, Filter.eventually_pure, kernel.const_apply]
  exacts [hf, hg]
#align probability_theory.indep_fun.ae_eq ProbabilityTheory.IndepFun.ae_eq

theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) μ :=
  kernel.IndepFun.comp hfg hφ hψ
#align probability_theory.indep_fun.comp ProbabilityTheory.IndepFun.comp

theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : IndepFun f g μ) :
    IndepFun f (-g) μ := hfg.comp measurable_id measurable_neg

theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : IndepFun f g μ) :
    IndepFun (-f) g μ := hfg.comp measurable_neg measurable_id

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

@[nontriviality]
lemma iIndepFun.of_subsingleton [IsProbabilityMeasure μ] [Subsingleton ι] : iIndepFun m f μ :=
  kernel.iIndepFun.of_subsingleton

lemma iIndepFun.isProbabilityMeasure (h : iIndepFun m f μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ ↦ univ)⟩

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun m f μ)
    (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ :=
  have := hf_Indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset ProbabilityTheory.iIndepFun.indepFun_finset

lemma iIndepFun.indepFun_prod_mk (hf_Indep : iIndepFun m f μ) (hf_meas : ∀ i, Measurable (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  have := hf_Indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_prod_mk hf_Indep hf_meas i j k hik hjk
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_prod ProbabilityTheory.iIndepFun.indepFun_prod_mk

open Finset in
lemma iIndepFun.indepFun_prod_mk_prod_mk (h_indep : iIndepFun m f μ) (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by
    -- NB: `measurability proves this, but is slow
    -- TODO(#13864): reinstate faster automation, e.g. by making `fun_prop` work here
    simp only [ne_eq, g]
    apply Measurable.prod
    · exact measurable_pi_apply _
    · exact measurable_pi_apply _
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l)

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.mul ProbabilityTheory.iIndepFun.indepFun_mul_left
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.add ProbabilityTheory.iIndepFun.indepFun_add_left

@[to_additive]
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  have := hf_indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_finset_prod_of_not_mem (hf_Indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) μ :=
  have := hf_Indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_finset_prod_of_not_mem hf_Indep hf_meas hi
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset_prod_of_not_mem ProbabilityTheory.iIndepFun.indepFun_finset_prod_of_not_mem
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset_sum_of_not_mem ProbabilityTheory.iIndepFun.indepFun_finset_sum_of_not_mem

@[to_additive]
lemma iIndepFun.indepFun_prod_range_succ {f : ℕ → Ω → β} (hf_Indep : iIndepFun (fun _ ↦ m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) : IndepFun (∏ j ∈ Finset.range n, f j) (f n) μ :=
  have := hf_Indep.isProbabilityMeasure
  kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_prod_range_succ ProbabilityTheory.iIndepFun.indepFun_prod_range_succ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_sum_range_succ ProbabilityTheory.iIndepFun.indepFun_sum_range_succ

end CommMonoid

theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s μ) :
    iIndepFun (fun _n => m) (fun n => (s n).indicator fun _ω => 1) μ :=
  kernel.iIndepSet.iIndepFun_indicator hs
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.Indep_fun_indicator ProbabilityTheory.iIndepSet.iIndepFun_indicator

end IndepFun

end ProbabilityTheory
