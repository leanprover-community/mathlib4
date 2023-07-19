/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.Pi

#align_import probability.independence.basic from "leanprover-community/mathlib"@"2f8347015b12b0864dfaf366ec4909eb70c78740"

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → MeasurableSpace Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
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

We provide one main definition of independence:
* `iIndepSets`: independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
Three other independence notions are defined using `iIndepSets`:
* `iIndep`: independence of a family of measurable space structures `m : ι → MeasurableSpace Ω`,
* `iIndepSet`: independence of a family of sets `s : ι → Set Ω`,
* `iIndepFun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `IndepFun` is the version of `iIndepFun`
for two functions.

The definition of independence for `iIndepSets` uses finite sets (`Finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma Indep.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `MeasurableSpace` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[MeasurableSpace Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open MeasureTheory MeasurableSpace

open scoped BigOperators MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type _}

section Definitions

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def iIndepSets [MeasurableSpace Ω] (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
    ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
    μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets ProbabilityTheory.iIndepSets

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSets [MeasurableSpace Ω] (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop
    := ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2
#align probability_theory.indep_sets ProbabilityTheory.IndepSets

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def iIndep (m : ι → MeasurableSpace Ω) [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac) :
    Prop := iIndepSets (fun x => { s | MeasurableSet[m x] s }) μ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep ProbabilityTheory.iIndep

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω) [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac) : Prop
    := IndepSets { s | MeasurableSet[m₁] s } { s | MeasurableSet[m₂] s } μ
#align probability_theory.indep ProbabilityTheory.Indep

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def iIndepSet [MeasurableSpace Ω] (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
    iIndep (fun i => generateFrom {s i}) μ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set ProbabilityTheory.iIndepSet

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet [MeasurableSpace Ω] (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
    Indep (generateFrom {s}) (generateFrom {t}) μ
#align probability_theory.indep_set ProbabilityTheory.IndepSet

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
def iIndepFun [MeasurableSpace Ω] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x))
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop :=
    iIndep (fun x => MeasurableSpace.comap (f x) (m x)) μ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun ProbabilityTheory.iIndepFun

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`. -/
def IndepFun {β γ} [MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
    Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ
#align probability_theory.indep_fun ProbabilityTheory.IndepFun

end Definitions

section Indep

@[symm]
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.inter_comm, mul_comm]; exact h t2 t1 ht2 ht1
#align probability_theory.indep_sets.symm ProbabilityTheory.IndepSets.symm

@[symm]
theorem Indep.symm {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h
#align probability_theory.indep.symm ProbabilityTheory.Indep.symm

theorem indep_bot_right (m' : MeasurableSpace Ω) {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : Indep m' ⊥ μ := by
  intro s t _hs ht
  rw [Set.mem_setOf_eq, MeasurableSpace.measurableSet_bot_iff] at ht
  cases' ht with ht ht
  · rw [ht, Set.inter_empty, measure_empty, MulZeroClass.mul_zero]
  · rw [ht, Set.inter_univ, measure_univ, mul_one]
#align probability_theory.indep_bot_right ProbabilityTheory.indep_bot_right

theorem indep_bot_left (m' : MeasurableSpace Ω) {_m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : Indep ⊥ m' μ := (indep_bot_right m').symm
#align probability_theory.indep_bot_left ProbabilityTheory.indep_bot_left

theorem indepSet_empty_right {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) : IndepSet s ∅ μ := by
  simp only [IndepSet, generateFrom_singleton_empty];
  exact indep_bot_right _
#align probability_theory.indep_set_empty_right ProbabilityTheory.indepSet_empty_right

theorem indepSet_empty_left {_m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) : IndepSet ∅ s μ := (indepSet_empty_right s).symm
#align probability_theory.indep_set_empty_left ProbabilityTheory.indepSet_empty_left

theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : IndepSets s₃ s₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2
#align probability_theory.indep_sets_of_indep_sets_of_le_left ProbabilityTheory.indepSets_of_indepSets_of_le_left

theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : IndepSets s₁ s₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)
#align probability_theory.indep_sets_of_indep_sets_of_le_right ProbabilityTheory.indepSets_of_indepSets_of_le_right

theorem indep_of_indep_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) : Indep m₃ m₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2
#align probability_theory.indep_of_indep_of_le_left ProbabilityTheory.indep_of_indep_of_le_left

theorem indep_of_indep_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indep m₁ m₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)
#align probability_theory.indep_of_indep_of_le_right ProbabilityTheory.indep_of_indep_of_le_right

theorem IndepSets.union [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω}
    (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ) : IndepSets (s₁ ∪ s₂) s' μ := by
  intro t1 t2 ht1 ht2
  cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
  · exact h₂ t1 t2 ht1₂ ht2
#align probability_theory.indep_sets.union ProbabilityTheory.IndepSets.union

@[simp]
theorem IndepSets.union_iff [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω} :
    IndepSets (s₁ ∪ s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  ⟨fun h =>
    ⟨indepSets_of_indepSets_of_le_left h (Set.subset_union_left s₁ s₂),
      indepSets_of_indepSets_of_le_left h (Set.subset_union_right s₁ s₂)⟩,
    fun h => IndepSets.union h.left h.right⟩
#align probability_theory.indep_sets.union_iff ProbabilityTheory.IndepSets.union_iff

theorem IndepSets.iUnion [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} (hyp : ∀ n, IndepSets (s n) s' μ) : IndepSets (⋃ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_iUnion] at ht1
  cases' ht1 with n ht1
  exact hyp n t1 t2 ht1 ht2
#align probability_theory.indep_sets.Union ProbabilityTheory.IndepSets.iUnion

theorem IndepSets.bUnion [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋃ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_iUnion] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2
#align probability_theory.indep_sets.bUnion ProbabilityTheory.IndepSets.bUnion

theorem IndepSets.inter [MeasurableSpace Ω] {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    {μ : Measure Ω} (h₁ : IndepSets s₁ s' μ) : IndepSets (s₁ ∩ s₂) s' μ :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2
#align probability_theory.indep_sets.inter ProbabilityTheory.IndepSets.inter

theorem IndepSets.iInter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} (h : ∃ n, IndepSets (s n) s' μ) : IndepSets (⋂ n, s n) s' μ := by
  intro t1 t2 ht1 ht2; cases' h with n h; exact h t1 t2 (Set.mem_iInter.mp ht1 n) ht2
#align probability_theory.indep_sets.Inter ProbabilityTheory.IndepSets.iInter

theorem IndepSets.bInter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' μ) :
    IndepSets (⋂ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.biInter_subset_of_mem hn ht1) ht2
#align probability_theory.indep_sets.bInter ProbabilityTheory.IndepSets.bInter

theorem indepSets_singleton_iff [MeasurableSpace Ω] {s t : Set Ω} {μ : Measure Ω} :
    IndepSets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
  ⟨fun h => h s t rfl rfl, fun h s1 t1 hs1 ht1 => by
    rwa [Set.mem_singleton_iff.mp hs1, Set.mem_singleton_iff.mp ht1]⟩
#align probability_theory.indep_sets_singleton_iff ProbabilityTheory.indepSets_singleton_iff

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromIndepToIndep

theorem iIndepSets.indepSets {s : ι → Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : iIndepSets s μ) {i j : ι} (hij : i ≠ j) : IndepSets (s i) (s j) μ := by
  classical
    intro t₁ t₂ ht₁ ht₂
    have hf_m : ∀ x : ι, x ∈ ({i, j} : Finset ι) → ite (x = i) t₁ t₂ ∈ s x := by
      intro x hx
      cases' Finset.mem_insert.mp hx with hx hx
      · simp [hx, ht₁]
      · simp [Finset.mem_singleton.mp hx, hij.symm, ht₂]
    have h1 : t₁ = ite (i = i) t₁ t₂ := by simp only [if_true, eq_self_iff_true]
    have h2 : t₂ = ite (j = i) t₁ t₂ := by simp only [hij.symm, if_false]
    have h_inter :
      ⋂ (t : ι) (_ : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂ =
        ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ :=
      by simp only [Finset.set_biInter_singleton, Finset.set_biInter_insert]
    have h_prod :
      (∏ t : ι in ({i, j} : Finset ι), μ (ite (t = i) t₁ t₂)) =
        μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂) := by
      simp only [hij, Finset.prod_singleton, Finset.prod_insert, not_false_iff,
        Finset.mem_singleton]
    rw [h1]
    nth_rw 2 [h2]
    nth_rw 4 [h2]
    rw [← h_inter, ← h_prod, h_indep {i, j} hf_m]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.indep_sets ProbabilityTheory.iIndepSets.indepSets

theorem iIndep.indep {m : ι → MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : iIndep m μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) μ := by
  change IndepSets ((fun x => MeasurableSet[m x]) i) ((fun x => MeasurableSet[m x]) j) μ
  exact iIndepSets.indepSets h_indep hij
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep.indep ProbabilityTheory.iIndep.indep

theorem iIndepFun.indepFun {_m₀ : MeasurableSpace Ω} {μ : Measure Ω} {β : ι → Type _}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun m f μ) {i j : ι}
    (hij : i ≠ j) : IndepFun (f i) (f j) μ :=
  hf_Indep.indep hij
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun ProbabilityTheory.iIndepFun.indepFun

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem iIndep.iIndepSets [MeasurableSpace Ω] {μ : Measure Ω} {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : iIndep m μ) :
    iIndepSets s μ := fun S f hfs =>
  h_indep S fun x hxS =>
    ((hms x).symm ▸ measurableSet_generateFrom (hfs x hxS) : MeasurableSet[m x] (f x))
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep.Indep_sets ProbabilityTheory.iIndep.iIndepSets

theorem Indep.indepSets [MeasurableSpace Ω] {μ : Measure Ω} {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) : IndepSets s1 s2 μ :=
  fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSet_generateFrom ht1) (measurableSet_generateFrom ht2)
#align probability_theory.indep.indep_sets ProbabilityTheory.Indep.indepSets

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


private theorem IndepSets.indep_aux {m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h2 : m2 ≤ m)
    (hp2 : IsPiSystem p2) (hpm2 : m2 = generateFrom p2) (hyp : IndepSets p1 p2 μ) {t1 t2 : Set Ω}
    (ht1 : t1 ∈ p1) (ht2m : MeasurableSet[m2] t2) : μ (t1 ∩ t2) = μ t1 * μ t2 := by
  let μ_inter := μ.restrict t1
  let ν := μ t1 • μ
  have h_univ : μ_inter Set.univ = ν Set.univ := by
    rw [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : IsFiniteMeasure μ_inter := @Restrict.isFiniteMeasure Ω _ t1 μ ⟨measure_lt_top μ t1⟩
  rw [Set.inter_comm, ← Measure.restrict_apply (h2 t2 ht2m)]
  refine' ext_on_measurableSpace_of_generate_finite m p2 (fun t ht => _) h2 hpm2 hp2 h_univ ht2m
  have ht2 : MeasurableSet[m] t := by
    refine' h2 _ _
    rw [hpm2]
    exact measurableSet_generateFrom ht
  rw [Measure.restrict_apply ht2, Measure.smul_apply, Set.inter_comm]
  exact hyp t1 t ht1 ht

theorem IndepSets.indep {m1 m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) : Indep m1 m2 μ := by
  intro t1 t2 ht1 ht2
  let μ_inter := μ.restrict t2
  let ν := μ t2 • μ
  have h_univ : μ_inter Set.univ = ν Set.univ := by
    rw [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : IsFiniteMeasure μ_inter := @Restrict.isFiniteMeasure Ω _ t2 μ ⟨measure_lt_top μ t2⟩
  rw [mul_comm, ← Measure.restrict_apply (h1 t1 ht1)]
  refine' ext_on_measurableSpace_of_generate_finite m p1 (fun t ht => _) h1 hpm1 hp1 h_univ ht1
  have ht1 : MeasurableSet[m] t := by
    refine' h1 _ _
    rw [hpm1]
    exact measurableSet_generateFrom ht
  rw [Measure.restrict_apply ht1, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact IndepSets.indep_aux h2 hp2 hpm2 hyp ht ht2
#align probability_theory.indep_sets.indep ProbabilityTheory.IndepSets.indep

theorem IndepSets.indep' {_m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
    Indep (generateFrom p1) (generateFrom p2) μ :=
  hyp.indep (generateFrom_le hp1m) (generateFrom_le hp2m) hp1 hp2 rfl rfl
#align probability_theory.indep_sets.indep' ProbabilityTheory.IndepSets.indep'

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem indepSets_piiUnionInter_of_disjoint [IsProbabilityMeasure μ] {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) μ := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
    let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
    have h_P_inter : μ (t1 ∩ t2) = ∏ n in p1 ∪ p2, μ (g n) := by
      have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
        intro i hi_mem_union
        rw [Finset.mem_union] at hi_mem_union
        cases' hi_mem_union with hi1 hi2
        · have hi2 : i ∉ p2 := fun hip2 => Set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
          simp_rw [if_pos hi1, if_neg hi2, Set.inter_univ]
          exact ht1_m i hi1
        · have hi1 : i ∉ p1 := fun hip1 => Set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
          simp_rw [if_neg hi1, if_pos hi2, Set.univ_inter]
          exact ht2_m i hi2
      have h_p1_inter_p2 :
        ((⋂ x ∈ p1, f1 x) ∩ ⋂ x ∈ p2, f2 x) =
          ⋂ i ∈ p1 ∪ p2, ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ := by
        ext1 x
        simp only [Set.mem_ite_univ_right, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
        exact
          ⟨fun h i _ => ⟨h.1 i, h.2 i⟩, fun h =>
            ⟨fun i hi => (h i (Or.inl hi)).1 hi, fun i hi => (h i (Or.inr hi)).2 hi⟩⟩
      rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← h_indep _ hgm]
    have h_μg : ∀ n, μ (g n) = ite (n ∈ p1) (μ (f1 n)) 1 * ite (n ∈ p2) (μ (f2 n)) 1 := by
      intro n
      dsimp only
      split_ifs with h1 h2
      · exact absurd rfl (Set.disjoint_iff_forall_ne.mp hST (hp1 h1) (hp2 h2))
      all_goals simp only [measure_univ, one_mul, mul_one, Set.inter_univ, Set.univ_inter]
    simp_rw [h_P_inter, h_μg, Finset.prod_mul_distrib,
      Finset.prod_ite_mem (p1 ∪ p2) p1 fun x => μ (f1 x), Finset.union_inter_cancel_left,
      Finset.prod_ite_mem (p1 ∪ p2) p2 fun x => μ (f2 x), Finset.union_inter_cancel_right, ht1_eq, ←
      h_indep p1 ht1_m, ht2_eq, ← h_indep p2 ht2_m]
#align probability_theory.indep_sets_pi_Union_Inter_of_disjoint ProbabilityTheory.indepSets_piiUnionInter_of_disjoint

theorem iIndepSet.indep_generateFrom_of_disjoint [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ := by
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  refine'
    IndepSets.indep'
      (fun t ht => generateFrom_piiUnionInter_le _ _ _ _ (measurableSet_generateFrom ht))
      (fun t ht => generateFrom_piiUnionInter_le _ _ _ _ (measurableSet_generateFrom ht)) _ _ _
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · classical exact indepSets_piiUnionInter_of_disjoint (iIndep.iIndepSets (fun n => rfl) hs) hST
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_of_disjoint ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint

theorem indep_iSup_of_disjoint [IsProbabilityMeasure μ] {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ m0) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ := by
  refine'
    IndepSets.indep (iSup₂_le fun i _ => h_le i) (iSup₂_le fun i _ => h_le i) _ _
      (generateFrom_piiUnionInter_measurableSet m S).symm
      (generateFrom_piiUnionInter_measurableSet m T).symm _
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · classical exact indepSets_piiUnionInter_of_disjoint h_indep hST
#align probability_theory.indep_supr_of_disjoint ProbabilityTheory.indep_iSup_of_disjoint

theorem indep_iSup_of_directed_le {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m' μ)
    (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m' μ := by
  let p : ι → Set (Set Ω) := fun n => { t | MeasurableSet[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @isPiSystem_measurableSet Ω (m n)
  have h_gen_n : ∀ n, m n = generateFrom (p n) := fun n =>
    (@generateFrom_measurableSet Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hm
  let p' := { t : Set Ω | MeasurableSet[m'] t }
  have hp'_pi : IsPiSystem p' := @isPiSystem_measurableSet Ω m'
  have h_gen' : m' = generateFrom p' := (@generateFrom_measurableSet Ω m').symm
  -- the π-systems defined are independent
  have h_pi_system_indep : IndepSets (⋃ n, p n) p' μ := by
    refine IndepSets.iUnion ?_
    conv at h_indep =>
      intro i
      rw [h_gen_n i, h_gen']
    exact fun n => (h_indep n).indepSets
  -- now go from π-systems to σ-algebras
  refine' IndepSets.indep (iSup_le h_le) h_le' hp_supr_pi hp'_pi _ h_gen' h_pi_system_indep
  exact (generateFrom_iUnion_measurableSet _).symm
#align probability_theory.indep_supr_of_directed_le ProbabilityTheory.indep_iSup_of_directed_le

theorem iIndepSet.indep_generateFrom_lt [Preorder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ := by
  convert iIndepSet.indep_generateFrom_of_disjoint hsm hs {i} { j | j < i }
    (Set.disjoint_singleton_left.mpr (lt_irrefl _))
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.setOf_eq_eq_singleton']
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_lt ProbabilityTheory.iIndepSet.indep_generateFrom_lt

theorem iIndepSet.indep_generateFrom_le [LinearOrder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ := by
  convert iIndepSet.indep_generateFrom_of_disjoint hsm hs {k} { j | j ≤ i }
      (Set.disjoint_singleton_left.mpr hk.not_le)
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.setOf_eq_eq_singleton']
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_le ProbabilityTheory.iIndepSet.indep_generateFrom_le

theorem iIndepSet.indep_generateFrom_le_nat [IsProbabilityMeasure μ] {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  iIndepSet.indep_generateFrom_le hsm hs _ n.lt_succ_self
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.indep_generate_from_le_nat ProbabilityTheory.iIndepSet.indep_generateFrom_le_nat

theorem indep_iSup_of_monotone [SemilatticeSup ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Monotone m) : Indep (⨆ i, m i) m' μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' (Monotone.directed_le hm)
#align probability_theory.indep_supr_of_monotone ProbabilityTheory.indep_iSup_of_monotone

theorem indep_iSup_of_antitone [SemilatticeInf ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h_indep : ∀ i, Indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Antitone m) : Indep (⨆ i, m i) m' μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' (directed_of_inf hm)
#align probability_theory.indep_supr_of_antitone ProbabilityTheory.indep_iSup_of_antitone

theorem iIndepSets.piiUnionInter_of_not_mem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π μ) (haS : a ∉ S) : IndepSets (piiUnionInter π S) (π a) μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
    let f := fun n => ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
    have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
      intro n hn_mem_insert
      dsimp only
      cases' Finset.mem_insert.mp hn_mem_insert with hn_mem hn_mem
      · simp [hn_mem, ht2_mem_pia]
      · have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hn_mem)
        simp [hn_ne_a, hn_mem, hft1_mem n hn_mem]
    have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
    have h_t1 : t1 = ⋂ n ∈ s, f n := by
      suffices h_forall : ∀ n ∈ s, f n = ft1 n
      · rw [ht1_eq]
        ext x
        simp_rw [Set.mem_iInter]
        conv => lhs; intro i hns; rw [← h_forall i hns]
      intro n hnS
      have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
      simp_rw [if_pos hnS, if_neg hn_ne_a]
    have h_μ_t1 : μ t1 = ∏ n in s, μ (f n) := by rw [h_t1, ← hp_ind s h_f_mem_pi]
    have h_t2 : t2 = f a := by simp
    have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a s, μ (f n) := by
      have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
        rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
      rw [h_t1_inter_t2, ← hp_ind (insert a s) h_f_mem]
    have has : a ∉ s := fun has_mem => haS (hs_mem has_mem)
    rw [h_μ_inter, Finset.prod_insert has, h_t2, mul_comm, h_μ_t1]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.pi_Union_Inter_of_not_mem ProbabilityTheory.iIndepSets.piiUnionInter_of_not_mem

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem iIndepSets.iIndep [IsProbabilityMeasure μ] (m : ι → MeasurableSpace Ω)
    (h_le : ∀ i, m i ≤ m0) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π μ) : iIndep m μ := by
  classical
    intro s f
    refine Finset.induction ?_ ?_ s
    · simp only [Finset.not_mem_empty, Set.mem_setOf_eq, IsEmpty.forall_iff, implies_true,
      Set.iInter_of_empty, Set.iInter_univ, measure_univ, Finset.prod_empty, forall_true_left]
    · intro a S ha_notin_S h_rec hf_m
      have hf_m_S : ∀ x ∈ S, MeasurableSet[m x] (f x) := fun x hx => hf_m x (by simp [hx])
      rw [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S, ← h_rec hf_m_S]
      let p := piiUnionInter π S
      set m_p := generateFrom p with hS_eq_generate
      have h_indep : @Indep Ω m_p (m a) m0 μ := by
        have hp : IsPiSystem p := isPiSystem_piiUnionInter π h_pi S
        have h_le' : ∀ i, generateFrom (π i) ≤ m0 := fun i => (h_generate i).symm.trans_le (h_le i)
        have hm_p : m_p ≤ m0 := generateFrom_piiUnionInter_le π h_le' S
        exact IndepSets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
            (iIndepSets.piiUnionInter_of_not_mem h_ind ha_notin_S)
      refine @Indep.symm Ω _ _ m0 μ h_indep (f a) (⋂ n ∈ S, f n)
        (hf_m a (Finset.mem_insert_self a S)) ?_
      have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
        intro n hn
        rw [hS_eq_generate, h_generate n]
        exact le_generateFrom_piiUnionInter _ hn
      have h_S_f : ∀ i ∈ S, MeasurableSet[m_p] (f i) :=
        fun i hi => (h_le_p i hi) (f i) (hf_m_S i hi)
      exact S.measurableSet_biInter h_S_f
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_sets.Indep ProbabilityTheory.IndepSets.indep

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `IndepSet s t μ ↔ IndepSets {s} {t} μ`.
-/


variable {s t : Set Ω} (S T : Set (Set Ω))

theorem indepSet_iff_indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsProbabilityMeasure μ] : IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  ⟨Indep.indepSets, fun h =>
    IndepSets.indep (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu]) (IsPiSystem.singleton s)
      (IsPiSystem.singleton t) rfl rfl h⟩
#align probability_theory.indep_set_iff_indep_sets_singleton ProbabilityTheory.indepSet_iff_indepSets_singleton

theorem indepSet_iff_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff
#align probability_theory.indep_set_iff_measure_inter_eq_mul ProbabilityTheory.indepSet_iff_measure_inter_eq_mul

theorem IndepSets.indepSet_of_mem {_m0 : MeasurableSpace Ω} (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) : IndepSet s t μ :=
  (indepSet_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)
#align probability_theory.indep_sets.indep_set_of_mem ProbabilityTheory.IndepSets.indepSet_of_mem

theorem Indep.indepSet_of_measurableSet {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (h_indep : Indep m₁ m₂ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) : IndepSet s t μ := by
  refine fun s' t' hs' ht' => h_indep s' t' ?_ ?_
  · refine @generateFrom_induction _ (fun u => MeasurableSet[m₁] u) {s} ?_ ?_ ?_ ?_ _ hs'
    · simp only [Set.mem_singleton_iff, forall_eq, hs]
    · exact @MeasurableSet.empty _ m₁
    · exact fun u hu => hu.compl
    · exact fun f hf => MeasurableSet.iUnion hf
  · refine @generateFrom_induction _ (fun u => MeasurableSet[m₂] u) {t} ?_ ?_ ?_ ?_ _ ht'
    · simp only [Set.mem_singleton_iff, forall_eq, ht]
    · exact @MeasurableSet.empty _ m₂
    · exact fun u hu => hu.compl
    · exact fun f hf => MeasurableSet.iUnion hf
#align probability_theory.indep.indep_set_of_measurable_set ProbabilityTheory.Indep.indepSet_of_measurableSet

theorem indep_iff_forall_indepSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpace Ω}
    (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ :=
  ⟨fun h => fun _s _t hs ht => h.indepSet_of_measurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSet_generateFrom (Set.mem_singleton s))
      (measurableSet_generateFrom (Set.mem_singleton t))⟩
#align probability_theory.indep_iff_forall_indep_set ProbabilityTheory.indep_iff_forall_indepSet

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type _} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFun f g μ ↔
      ∀ s t,
        MeasurableSet s → MeasurableSet t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  constructor <;> intro h
  · refine' fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht
#align probability_theory.indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type _} {β : ι → Type _}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    iIndepFun m f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i in S, μ (f i ⁻¹' sets i) := by
  refine' ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, _⟩
  intro h S setsΩ h_meas
  classical
    let setsβ : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
    have h_measβ : ∀ i ∈ S, MeasurableSet[m i] (setsβ i) := by
      intro i hi_mem
      simp_rw [dif_pos hi_mem]
      exact (h_meas i hi_mem).choose_spec.1
    have h_preim : ∀ i ∈ S, setsΩ i = f i ⁻¹' setsβ i := by
      intro i hi_mem
      simp_rw [dif_pos hi_mem]
      exact (h_meas i hi_mem).choose_spec.2.symm
    have h_left_eq : μ (⋂ i ∈ S, setsΩ i) = μ (⋂ i ∈ S, f i ⁻¹' setsβ i) := by
      congr with x
      simp_rw [Set.mem_iInter]
      constructor <;> intro h i hi_mem <;> specialize h i hi_mem
      · rwa [h_preim i hi_mem] at h
      · rwa [h_preim i hi_mem]
    have h_right_eq : (∏ i in S, μ (setsΩ i)) = ∏ i in S, μ (f i ⁻¹' setsβ i) := by
      refine' Finset.prod_congr rfl fun i hi_mem => _
      rw [h_preim i hi_mem]
    rw [h_left_eq, h_right_eq]
    exact h S h_measβ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul

theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  refine' indepFun_iff_measure_inter_preimage_eq_mul.trans _
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
#align probability_theory.indep_fun_iff_indep_set_preimage ProbabilityTheory.indepFun_iff_indepSet_preimage

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {f g : Ω → β} (hfg : IndepFun f g μ) :
    IndepFun g f μ := hfg.symm
#align probability_theory.indep_fun.symm ProbabilityTheory.IndepFun.symm

theorem IndepFun.ae_eq {mβ : MeasurableSpace β} {f g f' g' : Ω → β} (hfg : IndepFun f g μ)
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') : IndepFun f' g' μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩
#align probability_theory.indep_fun.ae_eq ProbabilityTheory.IndepFun.ae_eq

theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩
#align probability_theory.indep_fun.comp ProbabilityTheory.IndepFun.comp

/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem iIndepFun.indepFun_finset [IsProbabilityMeasure μ] {ι : Type _} {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ := by
  -- We introduce π-systems, build from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hs1 ht1
  rw [← hs2, ← ht2]
  classical
    let sets_s' : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
    have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by
      intro i hi; simp_rw [dif_pos hi]
    have h_sets_s'_univ : ∀ {i} (_hi : i ∈ T), sets_s' i = Set.univ := by
      intro i hi; simp_rw [dif_neg (Finset.disjoint_right.mp hST hi)]
    let sets_t' : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
    have h_sets_t'_univ : ∀ {i} (_hi : i ∈ S), sets_t' i = Set.univ := by
      intro i hi; simp_rw [dif_neg (Finset.disjoint_left.mp hST hi)]
    have h_meas_s' : ∀ i ∈ S, MeasurableSet (sets_s' i) := by
      intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
    have h_meas_t' : ∀ i ∈ T, MeasurableSet (sets_t' i) := by
      intro i hi; simp_rw [dif_pos hi]; exact ht1 _
    have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
      f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
      ext1 x
      simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
      constructor <;> intro h
      · intro i hi; simp only [h_sets_s'_eq hi, Set.mem_preimage]; exact h ⟨i, hi⟩
      · rintro ⟨i, hi⟩; specialize h i hi; rwa [dif_pos hi] at h
    have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
      = ⋂ i ∈ T, f i ⁻¹' sets_t' i := by
      ext1 x
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
      constructor <;> intro h
      · intro i hi; simp_rw [dif_pos hi]; exact h ⟨i, hi⟩
      · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [dif_pos hi] at h; exact h
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
    rw [h_eq_inter_S, h_eq_inter_T, hf_Indep S h_meas_s', hf_Indep T h_meas_t']
    have h_Inter_inter :
      ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) =
        ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
      ext1 x
      simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
      constructor <;> intro h
      · intro i hi
        cases' hi with hiS hiT
        · replace h := h.1 i hiS
          simp_rw [dif_pos hiS, dif_neg (Finset.disjoint_left.mp hST hiS)]
          exact ⟨by rwa [dif_pos hiS] at h, Set.mem_univ _⟩
        · replace h := h.2 i hiT
          simp_rw [dif_pos hiT, dif_neg (Finset.disjoint_right.mp hST hiT)]
          exact ⟨Set.mem_univ _, by rwa [dif_pos hiT] at h⟩
      · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
    rw [h_Inter_inter, hf_Indep (S ∪ T)]
    swap
    · intro i hi_mem
      rw [Finset.mem_union] at hi_mem
      cases' hi_mem with hi_mem hi_mem
      · rw [h_sets_t'_univ hi_mem, Set.inter_univ]; exact h_meas_s' i hi_mem
      · rw [h_sets_s'_univ hi_mem, Set.univ_inter]; exact h_meas_t' i hi_mem
    rw [Finset.prod_union hST]
    congr 1
    · refine' Finset.prod_congr rfl fun i hi => _
      rw [h_sets_t'_univ hi, Set.inter_univ]
    · refine' Finset.prod_congr rfl fun i hi => _
      rw [h_sets_s'_univ hi, Set.univ_inter]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset ProbabilityTheory.iIndepFun.indepFun_finset

theorem iIndepFun.indepFun_prod [IsProbabilityMeasure μ] {ι : Type _} {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun m f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ := by
  classical
    have h_right : f k =
      (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
      fun a (j : ({k} : Finset ι)) => f j a := rfl
    have h_meas_right :  Measurable fun p : ∀ j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ := measurable_pi_apply _
    let s : Finset ι := {i, j}
    have h_left : (fun ω => (f i ω, f j ω)) = (fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
      p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘ fun a (j : s) => f j a := by
      ext1 a
      simp only [Prod.mk.inj_iff]
      constructor
    have h_meas_left : Measurable fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
      p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
        Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
    rw [h_left, h_right]
    refine' (hf_Indep.indepFun_finset s {k} _ hf_meas).comp h_meas_left h_meas_right
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hik.symm, hjk.symm⟩
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_prod ProbabilityTheory.iIndepFun.indepFun_prod

@[to_additive]
theorem iIndepFun.mul [IsProbabilityMeasure μ] {ι : Type _} {β : Type _} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) μ :=
    hf_Indep.indepFun_prod hf_meas i j k hik hjk
  change IndepFun ((fun p : β × β => p.fst * p.snd) ∘ fun ω => (f i ω, f j ω)) (id ∘ f k) μ
  exact IndepFun.comp this (measurable_fst.mul measurable_snd) measurable_id
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.mul ProbabilityTheory.iIndepFun.mul
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.add ProbabilityTheory.iIndepFun.add

@[to_additive]
theorem iIndepFun.indepFun_finset_prod_of_not_mem [IsProbabilityMeasure μ] {ι : Type _} {β : Type _}
    {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}
    (hf_Indep : iIndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι}
    (hi : i ∉ s) : IndepFun (∏ j in s, f j) (f i) μ := by
  classical
    have h_right : f i =
      (fun p : ∀ _j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
      fun a (j : ({i} : Finset ι)) => f j a := rfl
    have h_meas_right : Measurable fun p : ∀ _j : ({i} : Finset ι), β
      => p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩
    have h_left : ∏ j in s, f j = (fun p : ∀ _j : s, β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
      ext1 a
      simp only [Function.comp_apply]
      have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
      rw [this, Finset.prod_coe_sort]
    have h_meas_left : Measurable fun p : ∀ _j : s, β => ∏ j, p j :=
      Finset.univ.measurable_prod fun (j : ↥s) (_H : j ∈ Finset.univ) => measurable_pi_apply j
    rw [h_left, h_right]
    exact
      (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
        h_meas_left h_meas_right
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset_prod_of_not_mem ProbabilityTheory.iIndepFun.indepFun_finset_prod_of_not_mem
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_finset_sum_of_not_mem ProbabilityTheory.iIndepFun.indepFun_finset_sum_of_not_mem

@[to_additive]
theorem iIndepFun.indepFun_prod_range_succ [IsProbabilityMeasure μ] {β : Type _}
    {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ℕ → Ω → β}
    (hf_Indep : iIndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    IndepFun (∏ j in Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFun_finset_prod_of_not_mem hf_meas Finset.not_mem_range_self
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_prod_range_succ ProbabilityTheory.iIndepFun.indepFun_prod_range_succ
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_fun_sum_range_succ ProbabilityTheory.iIndepFun.indepFun_sum_range_succ

theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s μ) : iIndepFun (fun _n => m) (fun n => (s n).indicator fun _ω => 1) μ := by
  classical
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    rintro S π _hπ
    simp_rw [Set.indicator_const_preimage_eq_union]
    refine' @hs S (fun i => ite (1 ∈ π i) (s i) ∅ ∪ ite ((0 : β) ∈ π i) (s i)ᶜ ∅) fun i _hi => _
    have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
      measurableSet_generateFrom (Set.mem_singleton _)
    refine'
      MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => _)
        (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => _)
    · exact @MeasurableSet.empty _ (generateFrom {s i})
    · exact @MeasurableSet.empty _ (generateFrom {s i})
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.Indep_fun_indicator ProbabilityTheory.iIndepSet.iIndepFun_indicator

end IndepFun

end ProbabilityTheory
