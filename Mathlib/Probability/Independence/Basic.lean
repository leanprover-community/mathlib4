/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.independence.basic
! leanprover-community/mathlib commit 2f8347015b12b0864dfaf366ec4909eb70c78740
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `indep_sets.indep`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set Ω)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space Ω`,
* `Indep_set`: independence of a family of sets `s : ι → set Ω`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {Ω} {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/


open MeasureTheory MeasurableSpace

open scoped BigOperators MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type _}

section Definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def IndepSets [MeasurableSpace Ω] (π : ι → Set (Set Ω))
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (H : ∀ i, i ∈ s → f i ∈ π i),
    μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)
#align probability_theory.Indep_sets ProbabilityTheory.IndepSets

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSetsCat [MeasurableSpace Ω] (s1 s2 : Set (Set Ω))
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2
#align probability_theory.indep_sets ProbabilityTheory.IndepSetsCat

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep (m : ι → MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepSets (fun x => { s | measurable_set[m x] s }) μ
#align probability_theory.Indep ProbabilityTheory.Indep

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepCat (m₁ m₂ : MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepSetsCat { s | measurable_set[m₁] s } { s | measurable_set[m₂] s } μ
#align probability_theory.indep ProbabilityTheory.IndepCat

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet [MeasurableSpace Ω] (s : ι → Set Ω)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  Indep (fun i => generateFrom {s i}) μ
#align probability_theory.Indep_set ProbabilityTheory.IndepSet

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSetCat [MeasurableSpace Ω] (s t : Set Ω)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepCat (generateFrom {s}) (generateFrom {t}) μ
#align probability_theory.indep_set ProbabilityTheory.IndepSetCat

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def IndepFun [MeasurableSpace Ω] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x))
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  Indep (fun x => MeasurableSpace.comap (f x) (m x)) μ
#align probability_theory.Indep_fun ProbabilityTheory.IndepFun

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def IndepFunCat {β γ} [MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepCat (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ
#align probability_theory.indep_fun ProbabilityTheory.IndepFunCat

end Definitions

section Indep

@[symm]
theorem IndepSetsCat.symm {s₁ s₂ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : IndepSetsCat s₁ s₂ μ) : IndepSetsCat s₂ s₁ μ := by intro t1 t2 ht1 ht2;
  rw [Set.inter_comm, mul_comm]; exact h t2 t1 ht2 ht1
#align probability_theory.indep_sets.symm ProbabilityTheory.IndepSetsCat.symm

@[symm]
theorem IndepCat.symm {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : IndepCat m₁ m₂ μ) : IndepCat m₂ m₁ μ :=
  IndepSetsCat.symm h
#align probability_theory.indep.symm ProbabilityTheory.IndepCat.symm

theorem indepCat_bot_right (m' : MeasurableSpace Ω) {m : MeasurableSpace Ω} {μ : Measure Ω}
    [ProbabilityMeasure μ] : IndepCat m' ⊥ μ := by
  intro s t hs ht
  rw [Set.mem_setOf_eq, MeasurableSpace.measurableSet_bot_iff] at ht
  cases ht
  · rw [ht, Set.inter_empty, measure_empty, MulZeroClass.mul_zero]
  · rw [ht, Set.inter_univ, measure_univ, mul_one]
#align probability_theory.indep_bot_right ProbabilityTheory.indepCat_bot_right

theorem indepCat_bot_left (m' : MeasurableSpace Ω) {m : MeasurableSpace Ω} {μ : Measure Ω}
    [ProbabilityMeasure μ] : IndepCat ⊥ m' μ :=
  (indepCat_bot_right m').symm
#align probability_theory.indep_bot_left ProbabilityTheory.indepCat_bot_left

theorem indepSetCat_empty_right {m : MeasurableSpace Ω} {μ : Measure Ω} [ProbabilityMeasure μ]
    (s : Set Ω) : IndepSetCat s ∅ μ := by simp only [indep_set, generate_from_singleton_empty];
  exact indep_bot_right _
#align probability_theory.indep_set_empty_right ProbabilityTheory.indepSetCat_empty_right

theorem indepSetCat_empty_left {m : MeasurableSpace Ω} {μ : Measure Ω} [ProbabilityMeasure μ]
    (s : Set Ω) : IndepSetCat ∅ s μ :=
  (indepSetCat_empty_right s).symm
#align probability_theory.indep_set_empty_left ProbabilityTheory.indepSetCat_empty_left

theorem indepSetsCat_of_indepSetsCat_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepSetsCat s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : IndepSetsCat s₃ s₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2
#align probability_theory.indep_sets_of_indep_sets_of_le_left ProbabilityTheory.indepSetsCat_of_indepSetsCat_of_le_left

theorem indepSetsCat_of_indepSetsCat_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepSetsCat s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : IndepSetsCat s₁ s₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)
#align probability_theory.indep_sets_of_indep_sets_of_le_right ProbabilityTheory.indepSetsCat_of_indepSetsCat_of_le_right

theorem indepCat_of_indepCat_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepCat m₁ m₂ μ) (h31 : m₃ ≤ m₁) : IndepCat m₃ m₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2
#align probability_theory.indep_of_indep_of_le_left ProbabilityTheory.indepCat_of_indepCat_of_le_left

theorem indepCat_of_indepCat_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} (h_indep : IndepCat m₁ m₂ μ) (h32 : m₃ ≤ m₂) : IndepCat m₁ m₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)
#align probability_theory.indep_of_indep_of_le_right ProbabilityTheory.indepCat_of_indepCat_of_le_right

theorem IndepSetsCat.union [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω}
    (h₁ : IndepSetsCat s₁ s' μ) (h₂ : IndepSetsCat s₂ s' μ) : IndepSetsCat (s₁ ∪ s₂) s' μ := by
  intro t1 t2 ht1 ht2
  cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
  · exact h₂ t1 t2 ht1₂ ht2
#align probability_theory.indep_sets.union ProbabilityTheory.IndepSetsCat.union

@[simp]
theorem IndepSetsCat.union_iff [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω} :
    IndepSetsCat (s₁ ∪ s₂) s' μ ↔ IndepSetsCat s₁ s' μ ∧ IndepSetsCat s₂ s' μ :=
  ⟨fun h =>
    ⟨indepSetsCat_of_indepSetsCat_of_le_left h (Set.subset_union_left s₁ s₂),
      indepSetsCat_of_indepSetsCat_of_le_left h (Set.subset_union_right s₁ s₂)⟩,
    fun h => IndepSetsCat.union h.left h.right⟩
#align probability_theory.indep_sets.union_iff ProbabilityTheory.IndepSetsCat.union_iff

theorem IndepSetsCat.iUnion [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} (hyp : ∀ n, IndepSetsCat (s n) s' μ) : IndepSetsCat (⋃ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_iUnion] at ht1
  cases' ht1 with n ht1
  exact hyp n t1 t2 ht1 ht2
#align probability_theory.indep_sets.Union ProbabilityTheory.IndepSetsCat.iUnion

theorem IndepSetsCat.bUnion [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} {u : Set ι} (hyp : ∀ n ∈ u, IndepSetsCat (s n) s' μ) :
    IndepSetsCat (⋃ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_iUnion] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2
#align probability_theory.indep_sets.bUnion ProbabilityTheory.IndepSetsCat.bUnion

theorem IndepSetsCat.inter [MeasurableSpace Ω] {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    {μ : Measure Ω} (h₁ : IndepSetsCat s₁ s' μ) : IndepSetsCat (s₁ ∩ s₂) s' μ :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2
#align probability_theory.indep_sets.inter ProbabilityTheory.IndepSetsCat.inter

theorem IndepSetsCat.iInter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} (h : ∃ n, IndepSetsCat (s n) s' μ) : IndepSetsCat (⋂ n, s n) s' μ := by
  intro t1 t2 ht1 ht2; cases' h with n h; exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2
#align probability_theory.indep_sets.Inter ProbabilityTheory.IndepSetsCat.iInter

theorem IndepSetsCat.bInter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {μ : Measure Ω} {u : Set ι} (h : ∃ n ∈ u, IndepSetsCat (s n) s' μ) :
    IndepSetsCat (⋂ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.biInter_subset_of_mem hn ht1) ht2
#align probability_theory.indep_sets.bInter ProbabilityTheory.IndepSetsCat.bInter

theorem indepSetsCat_singleton_iff [MeasurableSpace Ω] {s t : Set Ω} {μ : Measure Ω} :
    IndepSetsCat {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
  ⟨fun h => h s t rfl rfl, fun h s1 t1 hs1 ht1 => by
    rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩
#align probability_theory.indep_sets_singleton_iff ProbabilityTheory.indepSetsCat_singleton_iff

end Indep

/-! ### Deducing `indep` from `Indep` -/


section FromIndepToIndep

theorem IndepSets.indepSetsCat {s : ι → Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : IndepSets s μ) {i j : ι} (hij : i ≠ j) : IndepSetsCat (s i) (s j) μ := by
  classical
    intro t₁ t₂ ht₁ ht₂
    have hf_m : ∀ x : ι, x ∈ {i, j} → ite (x = i) t₁ t₂ ∈ s x := by
      intro x hx
      cases' finset.mem_insert.mp hx with hx hx
      · simp [hx, ht₁]
      · simp [finset.mem_singleton.mp hx, hij.symm, ht₂]
    have h1 : t₁ = ite (i = i) t₁ t₂ := by simp only [if_true, eq_self_iff_true]
    have h2 : t₂ = ite (j = i) t₁ t₂ := by simp only [hij.symm, if_false]
    have h_inter :
      (⋂ (t : ι) (H : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂) =
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
#align probability_theory.Indep_sets.indep_sets ProbabilityTheory.IndepSets.indepSetsCat

theorem Indep.indepCat {m : ι → MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : Indep m μ) {i j : ι} (hij : i ≠ j) : IndepCat (m i) (m j) μ := by
  change indep_sets ((fun x => measurable_set[m x]) i) ((fun x => measurable_set[m x]) j) μ
  exact Indep_sets.indep_sets h_indep hij
#align probability_theory.Indep.indep ProbabilityTheory.Indep.indepCat

theorem IndepFun.indepFunCat {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {β : ι → Type _}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ) {i j : ι}
    (hij : i ≠ j) : IndepFunCat (f i) (f j) μ :=
  hf_Indep.indep hij
#align probability_theory.Indep_fun.indep_fun ProbabilityTheory.IndepFun.indepFunCat

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem Indep.indepSets [MeasurableSpace Ω] {μ : Measure Ω} {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : Indep m μ) :
    IndepSets s μ := fun S f hfs =>
  h_indep S fun x hxS =>
    ((hms x).symm ▸ measurableSet_generateFrom (hfs x hxS) : measurable_set[m x] (f x))
#align probability_theory.Indep.Indep_sets ProbabilityTheory.Indep.indepSets

theorem IndepCat.indepSetsCat [MeasurableSpace Ω] {μ : Measure Ω} {s1 s2 : Set (Set Ω)}
    (h_indep : IndepCat (generateFrom s1) (generateFrom s2) μ) : IndepSetsCat s1 s2 μ :=
  fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSet_generateFrom ht1) (measurableSet_generateFrom ht2)
#align probability_theory.indep.indep_sets ProbabilityTheory.IndepCat.indepSetsCat

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


private theorem indep_sets.indep_aux {m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [ProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h2 : m2 ≤ m) (hp2 : IsPiSystem p2)
    (hpm2 : m2 = generateFrom p2) (hyp : IndepSetsCat p1 p2 μ) {t1 t2 : Set Ω} (ht1 : t1 ∈ p1)
    (ht2m : measurable_set[m2] t2) : μ (t1 ∩ t2) = μ t1 * μ t2 := by
  let μ_inter := μ.restrict t1
  let ν := μ t1 • μ
  have h_univ : μ_inter Set.univ = ν Set.univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t1 μ ⟨measure_lt_top μ t1⟩
  rw [Set.inter_comm, ← measure.restrict_apply (h2 t2 ht2m)]
  refine' ext_on_measurable_space_of_generate_finite m p2 (fun t ht => _) h2 hpm2 hp2 h_univ ht2m
  have ht2 : measurable_set[m] t := by
    refine' h2 _ _
    rw [hpm2]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht2, measure.smul_apply, Set.inter_comm]
  exact hyp t1 t ht1 ht

theorem IndepSetsCat.indepCat {m1 m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [ProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSetsCat p1 p2 μ) : IndepCat m1 m2 μ := by
  intro t1 t2 ht1 ht2
  let μ_inter := μ.restrict t2
  let ν := μ t2 • μ
  have h_univ : μ_inter Set.univ = ν Set.univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t2 μ ⟨measure_lt_top μ t2⟩
  rw [mul_comm, ← measure.restrict_apply (h1 t1 ht1)]
  refine' ext_on_measurable_space_of_generate_finite m p1 (fun t ht => _) h1 hpm1 hp1 h_univ ht1
  have ht1 : measurable_set[m] t := by
    refine' h1 _ _
    rw [hpm1]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht1, measure.smul_apply, smul_eq_mul, mul_comm]
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2
#align probability_theory.indep_sets.indep ProbabilityTheory.IndepSetsCat.indepCat

theorem IndepSetsCat.indep' {m : MeasurableSpace Ω} {μ : Measure Ω} [ProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSetsCat p1 p2 μ) :
    IndepCat (generateFrom p1) (generateFrom p2) μ :=
  hyp.indep (generateFrom_le hp1m) (generateFrom_le hp2m) hp1 hp2 rfl rfl
#align probability_theory.indep_sets.indep' ProbabilityTheory.IndepSetsCat.indep'

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem indepSetsCat_piiUnionInter_of_disjoint [ProbabilityMeasure μ] {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : IndepSets s μ) (hST : Disjoint S T) :
    IndepSetsCat (piiUnionInter s S) (piiUnionInter s T) μ := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
    let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
    have h_P_inter : μ (t1 ∩ t2) = ∏ n in p1 ∪ p2, μ (g n) := by
      have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
        intro i hi_mem_union
        rw [Finset.mem_union] at hi_mem_union
        cases' hi_mem_union with hi1 hi2
        · have hi2 : i ∉ p2 := fun hip2 => set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
          simp_rw [g, if_pos hi1, if_neg hi2, Set.inter_univ]
          exact ht1_m i hi1
        · have hi1 : i ∉ p1 := fun hip1 => set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
          simp_rw [g, if_neg hi1, if_pos hi2, Set.univ_inter]
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
      simp_rw [g]
      split_ifs
      · exact absurd rfl (set.disjoint_iff_forall_ne.mp hST _ (hp1 h) _ (hp2 h_1))
      all_goals simp only [measure_univ, one_mul, mul_one, Set.inter_univ, Set.univ_inter]
    simp_rw [h_P_inter, h_μg, Finset.prod_mul_distrib,
      Finset.prod_ite_mem (p1 ∪ p2) p1 fun x => μ (f1 x), Finset.union_inter_cancel_left,
      Finset.prod_ite_mem (p1 ∪ p2) p2 fun x => μ (f2 x), Finset.union_inter_cancel_right, ht1_eq, ←
      h_indep p1 ht1_m, ht2_eq, ← h_indep p2 ht2_m]
#align probability_theory.indep_sets_pi_Union_Inter_of_disjoint ProbabilityTheory.indepSetsCat_piiUnionInter_of_disjoint

theorem IndepSet.indepCat_generateFrom_of_disjoint [ProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    IndepCat (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ := by
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  refine'
    indep_sets.indep'
      (fun t ht => generateFrom_piiUnionInter_le _ _ _ _ (measurable_set_generate_from ht))
      (fun t ht => generateFrom_piiUnionInter_le _ _ _ _ (measurable_set_generate_from ht)) _ _ _
  · exact fun k => generate_from_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact fun k => generate_from_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · classical exact indep_sets_pi_Union_Inter_of_disjoint (Indep.Indep_sets (fun n => rfl) hs) hST
#align probability_theory.Indep_set.indep_generate_from_of_disjoint ProbabilityTheory.IndepSet.indepCat_generateFrom_of_disjoint

theorem indepCat_iSup_of_disjoint [ProbabilityMeasure μ] {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ m0) (h_indep : Indep m μ) {S T : Set ι} (hST : Disjoint S T) :
    IndepCat (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ := by
  refine'
    indep_sets.indep (iSup₂_le fun i _ => h_le i) (iSup₂_le fun i _ => h_le i) _ _
      (generateFrom_piiUnionInter_measurableSet m S).symm
      (generateFrom_piiUnionInter_measurableSet m T).symm _
  · exact isPiSystem_piiUnionInter _ (fun n => @is_pi_system_measurable_set Ω (m n)) _
  · exact isPiSystem_piiUnionInter _ (fun n => @is_pi_system_measurable_set Ω (m n)) _
  · classical exact indep_sets_pi_Union_Inter_of_disjoint h_indep hST
#align probability_theory.indep_supr_of_disjoint ProbabilityTheory.indepCat_iSup_of_disjoint

theorem indepCat_iSup_of_directed_le {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [ProbabilityMeasure μ] (h_indep : ∀ i, IndepCat (m i) m' μ)
    (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : Directed (· ≤ ·) m) : IndepCat (⨆ i, m i) m' μ :=
  by
  let p : ι → Set (Set Ω) := fun n => { t | measurable_set[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @is_pi_system_measurable_set Ω (m n)
  have h_gen_n : ∀ n, m n = generate_from (p n) := fun n =>
    (@generate_from_measurable_set Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hm
  let p' := { t : Set Ω | measurable_set[m'] t }
  have hp'_pi : IsPiSystem p' := @is_pi_system_measurable_set Ω m'
  have h_gen' : m' = generate_from p' := (@generate_from_measurable_set Ω m').symm
  -- the π-systems defined are independent
  have h_pi_system_indep : indep_sets (⋃ n, p n) p' μ := by
    refine' indep_sets.Union _
    simp_rw [h_gen_n, h_gen'] at h_indep
    exact fun n => (h_indep n).IndepSetsCat
  -- now go from π-systems to σ-algebras
  refine' indep_sets.indep (iSup_le h_le) h_le' hp_supr_pi hp'_pi _ h_gen' h_pi_system_indep
  exact (generate_from_Union_measurable_set _).symm
#align probability_theory.indep_supr_of_directed_le ProbabilityTheory.indepCat_iSup_of_directed_le

theorem IndepSet.indepCat_generateFrom_lt [Preorder ι] [ProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (i : ι) :
    IndepCat (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ := by
  convert hs.indep_generate_from_of_disjoint hsm {i} { j | j < i }
      (set.disjoint_singleton_left.mpr (lt_irrefl _))
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.setOf_eq_eq_singleton']
#align probability_theory.Indep_set.indep_generate_from_lt ProbabilityTheory.IndepSet.indepCat_generateFrom_lt

theorem IndepSet.indepCat_generateFrom_le [LinearOrder ι] [ProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    IndepCat (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ := by
  convert hs.indep_generate_from_of_disjoint hsm {k} { j | j ≤ i }
      (set.disjoint_singleton_left.mpr hk.not_le)
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.setOf_eq_eq_singleton']
#align probability_theory.Indep_set.indep_generate_from_le ProbabilityTheory.IndepSet.indepCat_generateFrom_le

theorem IndepSet.indepCat_generateFrom_le_nat [ProbabilityMeasure μ] {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (n : ℕ) :
    IndepCat (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  hs.indepCat_generateFrom_le hsm _ n.lt_succ_self
#align probability_theory.Indep_set.indep_generate_from_le_nat ProbabilityTheory.IndepSet.indepCat_generateFrom_le_nat

theorem indepCat_iSup_of_monotone [SemilatticeSup ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {μ : Measure Ω} [ProbabilityMeasure μ]
    (h_indep : ∀ i, IndepCat (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Monotone m) : IndepCat (⨆ i, m i) m' μ :=
  indepCat_iSup_of_directed_le h_indep h_le h_le' (Monotone.directed_le hm)
#align probability_theory.indep_supr_of_monotone ProbabilityTheory.indepCat_iSup_of_monotone

theorem indepCat_iSup_of_antitone [SemilatticeInf ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {μ : Measure Ω} [ProbabilityMeasure μ]
    (h_indep : ∀ i, IndepCat (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Antitone m) : IndepCat (⨆ i, m i) m' μ :=
  indepCat_iSup_of_directed_le h_indep h_le h_le' (directed_of_inf hm)
#align probability_theory.indep_supr_of_antitone ProbabilityTheory.indepCat_iSup_of_antitone

theorem IndepSets.piiUnionInter_of_not_mem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : IndepSets π μ) (haS : a ∉ S) : IndepSetsCat (piiUnionInter π S) (π a) μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
    let f n := ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
    have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
      intro n hn_mem_insert
      simp_rw [f]
      cases' finset.mem_insert.mp hn_mem_insert with hn_mem hn_mem
      · simp [hn_mem, ht2_mem_pia]
      · have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hn_mem)
        simp [hn_ne_a, hn_mem, hft1_mem n hn_mem]
    have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
    have h_t1 : t1 = ⋂ n ∈ s, f n := by
      suffices h_forall : ∀ n ∈ s, f n = ft1 n
      · rw [ht1_eq]
        congr with (n x)
        congr with (hns y)
        simp only [(h_forall n hns).symm]
      intro n hnS
      have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
      simp_rw [f, if_pos hnS, if_neg hn_ne_a]
    have h_μ_t1 : μ t1 = ∏ n in s, μ (f n) := by rw [h_t1, ← hp_ind s h_f_mem_pi]
    have h_t2 : t2 = f a := by simp_rw [f]; simp
    have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a s, μ (f n) := by
      have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
        rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
      rw [h_t1_inter_t2, ← hp_ind (insert a s) h_f_mem]
    have has : a ∉ s := fun has_mem => haS (hs_mem Membership)
    rw [h_μ_inter, Finset.prod_insert has, h_t2, mul_comm, h_μ_t1]
#align probability_theory.Indep_sets.pi_Union_Inter_of_not_mem ProbabilityTheory.IndepSets.piiUnionInter_of_not_mem

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem IndepSets.indep [ProbabilityMeasure μ] (m : ι → MeasurableSpace Ω) (h_le : ∀ i, m i ≤ m0)
    (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : IndepSets π μ) : Indep m μ := by
  classical
    refine' Finset.induction _ _
    ·
      simp only [measure_univ, imp_true_iff, Set.iInter_false, Set.iInter_univ, Finset.prod_empty,
        eq_self_iff_true]
    intro a S ha_notin_S h_rec f hf_m
    have hf_m_S : ∀ x ∈ S, measurable_set[m x] (f x) := fun x hx => hf_m x (by simp [hx])
    rw [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S, ← h_rec hf_m_S]
    let p := piiUnionInter π S
    set m_p := generate_from p with hS_eq_generate
    have h_indep : indep m_p (m a) μ := by
      have hp : IsPiSystem p := isPiSystem_piiUnionInter π h_pi S
      have h_le' : ∀ i, generate_from (π i) ≤ m0 := fun i => (h_generate i).symm.trans_le (h_le i)
      have hm_p : m_p ≤ m0 := generateFrom_piiUnionInter_le π h_le' S
      exact
        indep_sets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
          (h_ind.pi_Union_Inter_of_not_mem ha_notin_S)
    refine' h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) _
    have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
      intro n hn
      rw [hS_eq_generate, h_generate n]
      exact le_generateFrom_piiUnionInter S hn
    have h_S_f : ∀ i ∈ S, measurable_set[m_p] (f i) := fun i hi => (h_le_p i hi) (f i) (hf_m_S i hi)
    exact S.measurable_set_bInter h_S_f
#align probability_theory.Indep_sets.Indep ProbabilityTheory.IndepSets.indep

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/


variable {s t : Set Ω} (S T : Set (Set Ω))

theorem indepSetCat_iff_indepSetsCat_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume)
    [ProbabilityMeasure μ] : IndepSetCat s t μ ↔ IndepSetsCat {s} {t} μ :=
  ⟨IndepCat.indepSetsCat, fun h =>
    IndepSetsCat.indepCat (generateFrom_le fun u hu => by rwa [set.mem_singleton_iff.mp hu])
      (generateFrom_le fun u hu => by rwa [set.mem_singleton_iff.mp hu]) (IsPiSystem.singleton s)
      (IsPiSystem.singleton t) rfl rfl h⟩
#align probability_theory.indep_set_iff_indep_sets_singleton ProbabilityTheory.indepSetCat_iff_indepSetsCat_singleton

theorem indepSetCat_iff_measure_inter_eq_mul {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume)
    [ProbabilityMeasure μ] : IndepSetCat s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indepSetCat_iff_indepSetsCat_singleton hs_meas ht_meas μ).trans indepSetsCat_singleton_iff
#align probability_theory.indep_set_iff_measure_inter_eq_mul ProbabilityTheory.indepSetCat_iff_measure_inter_eq_mul

theorem IndepSetsCat.indepSetCat_of_mem {m0 : MeasurableSpace Ω} (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) [ProbabilityMeasure μ]
    (h_indep : IndepSetsCat S T μ) : IndepSetCat s t μ :=
  (indepSetCat_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)
#align probability_theory.indep_sets.indep_set_of_mem ProbabilityTheory.IndepSetsCat.indepSetCat_of_mem

theorem IndepCat.indepSetCat_of_measurableSet {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (h_indep : IndepCat m₁ m₂ μ) {s t : Set Ω} (hs : measurable_set[m₁] s)
    (ht : measurable_set[m₂] t) : IndepSetCat s t μ := by
  refine' fun s' t' hs' ht' => h_indep s' t' _ _
  · refine' generate_from_induction (fun u => measurable_set[m₁] u) {s} _ _ _ _ hs'
    · simp only [hs, Set.mem_singleton_iff, Set.mem_setOf_eq, forall_eq]
    · exact @MeasurableSet.empty _ m₁
    · exact fun u hu => hu.compl
    · exact fun f hf => MeasurableSet.iUnion hf
  · refine' generate_from_induction (fun u => measurable_set[m₂] u) {t} _ _ _ _ ht'
    · simp only [ht, Set.mem_singleton_iff, Set.mem_setOf_eq, forall_eq]
    · exact @MeasurableSet.empty _ m₂
    · exact fun u hu => hu.compl
    · exact fun f hf => MeasurableSet.iUnion hf
#align probability_theory.indep.indep_set_of_measurable_set ProbabilityTheory.IndepCat.indepSetCat_of_measurableSet

theorem indepCat_iff_forall_indepSetCat (m₁ m₂ : MeasurableSpace Ω) {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) :
    IndepCat m₁ m₂ μ ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → IndepSetCat s t μ :=
  ⟨fun h => fun s t hs ht => h.indepSetCat_of_measurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSet_generateFrom (Set.mem_singleton s))
      (measurableSet_generateFrom (Set.mem_singleton t))⟩
#align probability_theory.indep_iff_forall_indep_set ProbabilityTheory.indepCat_iff_forall_indepSetCat

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type _} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem indepFunCat_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFunCat f g μ ↔
      ∀ s t,
        MeasurableSet s → MeasurableSet t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  constructor <;> intro h
  · refine' fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht
#align probability_theory.indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.indepFunCat_iff_measure_inter_preimage_eq_mul

theorem indepFun_iff_measure_inter_preimage_eq_mul {ι : Type _} {β : ι → Type _}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    IndepFun m f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i in S, μ (f i ⁻¹' sets i) := by
  refine' ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, _⟩
  intro h S setsΩ h_meas
  classical
    let setsβ : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).some) fun _ => Set.univ
    have h_measβ : ∀ i ∈ S, measurable_set[m i] (setsβ i) := by
      intro i hi_mem
      simp_rw [setsβ, dif_pos hi_mem]
      exact (h_meas i hi_mem).choose_spec.1
    have h_preim : ∀ i ∈ S, setsΩ i = f i ⁻¹' setsβ i := by
      intro i hi_mem
      simp_rw [setsβ, dif_pos hi_mem]
      exact (h_meas i hi_mem).choose_spec.2.symm
    have h_left_eq : μ (⋂ i ∈ S, setsΩ i) = μ (⋂ i ∈ S, f i ⁻¹' setsβ i) := by
      congr with (i x)
      simp only [Set.mem_iInter]
      constructor <;> intro h hi_mem <;> specialize h hi_mem
      · rwa [h_preim i hi_mem] at h
      · rwa [h_preim i hi_mem]
    have h_right_eq : (∏ i in S, μ (setsΩ i)) = ∏ i in S, μ (f i ⁻¹' setsβ i) := by
      refine' Finset.prod_congr rfl fun i hi_mem => _
      rw [h_preim i hi_mem]
    rw [h_left_eq, h_right_eq]
    exact h S h_measβ
#align probability_theory.Indep_fun_iff_measure_inter_preimage_eq_mul ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul

theorem indepFunCat_iff_indepSetCat_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [ProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    IndepFunCat f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSetCat (f ⁻¹' s) (g ⁻¹' t) μ := by
  refine' indep_fun_iff_measure_inter_preimage_eq_mul.trans _
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
  · rwa [← indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
#align probability_theory.indep_fun_iff_indep_set_preimage ProbabilityTheory.indepFunCat_iff_indepSetCat_preimage

@[symm]
theorem IndepFunCat.symm {mβ : MeasurableSpace β} {f g : Ω → β} (hfg : IndepFunCat f g μ) :
    IndepFunCat g f μ :=
  hfg.symm
#align probability_theory.indep_fun.symm ProbabilityTheory.IndepFunCat.symm

theorem IndepFunCat.ae_eq {mβ : MeasurableSpace β} {f g f' g' : Ω → β} (hfg : IndepFunCat f g μ)
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') : IndepFunCat f' g' μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩
#align probability_theory.indep_fun.ae_eq ProbabilityTheory.IndepFunCat.ae_eq

theorem IndepFunCat.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFunCat f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFunCat (φ ∘ f) (ψ ∘ g) μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
#align probability_theory.indep_fun.comp ProbabilityTheory.IndepFunCat.comp

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem IndepFun.indepFunCat_finset [ProbabilityMeasure μ] {ι : Type _} {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : IndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFunCat (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ := by
  -- We introduce π-systems, build from the π-system of boxes which generates `measurable_space.pi`.
  let πSβ :=
    Set.pi (Set.univ : Set S) ''
      Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := is_pi_system_pi.comap fun a i => f i a
  have hπS_gen : (measurable_space.pi.comap fun a (i : S) => f i a) = generate_from πS := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [Set.mem_image, Set.mem_setOf_eq, exists_prop]
    · infer_instance
  let πTβ :=
    Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := is_pi_system_pi.comap fun a i => f i a
  have hπT_gen : (measurable_space.pi.comap fun a (i : T) => f i a) = generate_from πT := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [Set.mem_image, Set.mem_setOf_eq, exists_prop]
    · infer_instance
  -- To prove independence, we prove independence of the generating π-systems.
  refine'
    indep_sets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
      (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
      _
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hs1 ht1
  rw [← hs2, ← ht2]
  classical
    let sets_s' : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
    have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by intro i hi;
      simp_rw [sets_s', dif_pos hi]
    have h_sets_s'_univ : ∀ {i} (hi : i ∈ T), sets_s' i = Set.univ := by intro i hi;
      simp_rw [sets_s', dif_neg (finset.disjoint_right.mp hST hi)]
    let sets_t' : ∀ i : ι, Set (β i) := fun i =>
      dite (i ∈ T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
    have h_sets_t'_univ : ∀ {i} (hi : i ∈ S), sets_t' i = Set.univ := by intro i hi;
      simp_rw [sets_t', dif_neg (finset.disjoint_left.mp hST hi)]
    have h_meas_s' : ∀ i ∈ S, MeasurableSet (sets_s' i) := by intro i hi; rw [h_sets_s'_eq hi];
      exact hs1 _
    have h_meas_t' : ∀ i ∈ T, MeasurableSet (sets_t' i) := by intro i hi;
      simp_rw [sets_t', dif_pos hi]; exact ht1 _
    have h_eq_inter_S :
      (fun (ω : Ω) (i : ↥S) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i :=
      by
      ext1 x
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
      constructor <;> intro h
      · intro i hi; rw [h_sets_s'_eq hi]; exact h ⟨i, hi⟩
      · rintro ⟨i, hi⟩; specialize h i hi; rw [h_sets_s'_eq hi] at h; exact h
    have h_eq_inter_T :
      (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t = ⋂ i ∈ T, f i ⁻¹' sets_t' i :=
      by
      ext1 x
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
      constructor <;> intro h
      · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
      · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
    rw [Indep_fun_iff_measure_inter_preimage_eq_mul] at hf_Indep
    rw [h_eq_inter_S, h_eq_inter_T, hf_Indep S h_meas_s', hf_Indep T h_meas_t']
    have h_Inter_inter :
      ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) =
        ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
      ext1 x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
      constructor <;> intro h
      · intro i hi
        cases hi
        · rw [h_sets_t'_univ hi]; exact ⟨h.1 i hi, Set.mem_univ _⟩
        · rw [h_sets_s'_univ hi]; exact ⟨Set.mem_univ _, h.2 i hi⟩
      · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
    rw [h_Inter_inter, hf_Indep (S ∪ T)]
    swap
    · intro i hi_mem
      rw [Finset.mem_union] at hi_mem
      cases hi_mem
      · rw [h_sets_t'_univ hi_mem, Set.inter_univ]; exact h_meas_s' i hi_mem
      · rw [h_sets_s'_univ hi_mem, Set.univ_inter]; exact h_meas_t' i hi_mem
    rw [Finset.prod_union hST]
    congr 1
    · refine' Finset.prod_congr rfl fun i hi => _
      rw [h_sets_t'_univ hi, Set.inter_univ]
    · refine' Finset.prod_congr rfl fun i hi => _
      rw [h_sets_s'_univ hi, Set.univ_inter]
#align probability_theory.Indep_fun.indep_fun_finset ProbabilityTheory.IndepFun.indepFunCat_finset

theorem IndepFun.indepFunCat_prod [ProbabilityMeasure μ] {ι : Type _} {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFunCat (fun a => (f i a, f j a)) (f k) μ := by
  classical
    have h_right :
      f k =
        (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
          fun a (j : ({k} : Finset ι)) => f j a :=
      rfl
    have h_meas_right :
      Measurable fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
      measurable_pi_apply ⟨k, Finset.mem_singleton_self k⟩
    let s : Finset ι := {i, j}
    have h_left :
      (fun ω => (f i ω, f j ω)) =
        (fun p : ∀ l : s, β l =>
            (p ⟨i, Finset.mem_insert_self i _⟩,
              p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
          fun a (j : s) => f j a := by
      ext1 a
      simp only [Prod.mk.inj_iff]
      constructor <;> rfl
    have h_meas_left :
      Measurable fun p : ∀ l : s, β l =>
        (p ⟨i, Finset.mem_insert_self i _⟩,
          p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
      Measurable.prod (measurable_pi_apply ⟨i, Finset.mem_insert_self i {j}⟩)
        (measurable_pi_apply ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩)
    rw [h_left, h_right]
    refine' (hf_Indep.indep_fun_finset s {k} _ hf_meas).comp h_meas_left h_meas_right
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hik.symm, hjk.symm⟩
#align probability_theory.Indep_fun.indep_fun_prod ProbabilityTheory.IndepFun.indepFunCat_prod

@[to_additive]
theorem IndepFun.mul [ProbabilityMeasure μ] {ι : Type _} {β : Type _} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFunCat (f i * f j) (f k) μ := by
  have : indep_fun (fun ω => (f i ω, f j ω)) (f k) μ :=
    hf_Indep.indep_fun_prod hf_meas i j k hik hjk
  change indep_fun ((fun p : β × β => p.fst * p.snd) ∘ fun ω => (f i ω, f j ω)) (id ∘ f k) μ
  exact indep_fun.comp this (measurable_fst.mul measurable_snd) measurable_id
#align probability_theory.Indep_fun.mul ProbabilityTheory.IndepFun.mul
#align probability_theory.Indep_fun.add ProbabilityTheory.IndepFun.add

@[to_additive]
theorem IndepFun.indepFunCat_finset_prod_of_not_mem [ProbabilityMeasure μ] {ι : Type _} {β : Type _}
    {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}
    (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι}
    (hi : i ∉ s) : IndepFunCat (∏ j in s, f j) (f i) μ := by
  classical
    have h_right :
      f i =
        (fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
          fun a (j : ({i} : Finset ι)) => f j a :=
      rfl
    have h_meas_right :
      Measurable fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩ :=
      measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩
    have h_left : (∏ j in s, f j) = (fun p : ∀ j : s, β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
      ext1 a
      simp only [Function.comp_apply]
      have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
      rw [this, Finset.prod_coe_sort]
    have h_meas_left : Measurable fun p : ∀ j : s, β => ∏ j, p j :=
      finset.univ.measurable_prod fun (j : ↥s) (H : j ∈ Finset.univ) => measurable_pi_apply j
    rw [h_left, h_right]
    exact
      (hf_Indep.indep_fun_finset s {i} (finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
        h_meas_left h_meas_right
#align probability_theory.Indep_fun.indep_fun_finset_prod_of_not_mem ProbabilityTheory.IndepFun.indepFunCat_finset_prod_of_not_mem
#align probability_theory.Indep_fun.indep_fun_finset_sum_of_not_mem ProbabilityTheory.IndepFun.indepFunCat_finset_sum_of_not_mem

@[to_additive]
theorem IndepFun.indepFunCat_prod_range_succ [ProbabilityMeasure μ] {β : Type _}
    {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ℕ → Ω → β}
    (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    IndepFunCat (∏ j in Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFunCat_finset_prod_of_not_mem hf_meas Finset.not_mem_range_self
#align probability_theory.Indep_fun.indep_fun_prod_range_succ ProbabilityTheory.IndepFun.indepFunCat_prod_range_succ
#align probability_theory.Indep_fun.indep_fun_sum_range_succ ProbabilityTheory.IndepFun.indepFunCat_sum_range_succ

theorem IndepSet.indepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : IndepSet s μ) : IndepFun (fun n => m) (fun n => (s n).indicator fun ω => 1) μ := by
  classical
    rw [Indep_fun_iff_measure_inter_preimage_eq_mul]
    rintro S π hπ
    simp_rw [Set.indicator_const_preimage_eq_union]
    refine' @hs S (fun i => ite (1 ∈ π i) (s i) ∅ ∪ ite ((0 : β) ∈ π i) (s iᶜ) ∅) fun i hi => _
    have hsi : measurable_set[generate_from {s i}] (s i) :=
      measurable_set_generate_from (Set.mem_singleton _)
    refine'
      MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => _)
        (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => _)
    · exact @MeasurableSet.empty _ (generate_from {s i})
    · exact @MeasurableSet.empty _ (generate_from {s i})
#align probability_theory.Indep_set.Indep_fun_indicator ProbabilityTheory.IndepSet.indepFun_indicator

end IndepFun

end ProbabilityTheory

