/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Tactic.Peel
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Independence of families of sets with respect to a kernel and a measure

A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel
`κ : Kernel α Ω` and a measure `μ` on `α` if for any finite set of indices `s = {i_1, ..., i_n}`,
for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then for `μ`-almost every `a : α`,
`κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.

This notion of independence is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

The main purpose of this file is to prove only once the properties that hold for both conditional
and non-conditional independence.

This file contains results about independence of families of sets and `σ`-algebras.
See the `IndepFun` file for results about independence of random variables.

## Main definitions

* `ProbabilityTheory.Kernel.iIndepSets`: independence of a family of sets of sets.
  Variant for two sets of sets: `ProbabilityTheory.Kernel.IndepSets`.
* `ProbabilityTheory.Kernel.iIndep`: independence of a family of σ-algebras. Variant for two
  σ-algebras: `Indep`.
* `ProbabilityTheory.Kernel.iIndepSet`: independence of a family of sets. Variant for two sets:
  `ProbabilityTheory.Kernel.IndepSet`.

See the file `Mathlib/Probability/Kernel/Basic.lean` for a more detailed discussion of these
definitions in the particular case of the usual independence notion.

## Main statements

* `ProbabilityTheory.Kernel.iIndepSets.iIndep`: if π-systems are independent as sets of sets,
  then the measurable space structures they generate are independent.
* `ProbabilityTheory.Kernel.IndepSets.Indep`: variant with two π-systems.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel

variable {α Ω ι : Type*}

section Definitions

variable {_mα : MeasurableSpace α}

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.
It will be used for families of pi_systems. -/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
  ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a measure `μ` if for
any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they define is independent. -/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} κ μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι → Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun i ↦ generateFrom {s i}) κ μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (generateFrom {s}) (generateFrom {t}) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}

@[simp] lemma iIndepSets_zero_right : iIndepSets π κ 0 := by simp [iIndepSets]

@[simp] lemma indepSets_zero_right : IndepSets s1 s2 κ 0 := by simp [IndepSets]

@[simp] lemma indepSets_zero_left : IndepSets s1 s2 (0 : Kernel α Ω) μ := by simp [IndepSets]

@[simp] lemma iIndep_zero_right : iIndep m κ 0 := by simp [iIndep]

@[simp] lemma indep_zero_right {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} : Indep m₁ m₂ κ 0 := by simp [Indep]

@[simp] lemma indep_zero_left {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} :
    Indep m₁ m₂ (0 : Kernel α Ω) μ := by simp [Indep]

@[simp] lemma iIndepSet_zero_right : iIndepSet s κ 0 := by simp [iIndepSet]

@[simp] lemma indepSet_zero_right {s t : Set Ω} : IndepSet s t κ 0 := by simp [IndepSet]

@[simp] lemma indepSet_zero_left {s t : Set Ω} : IndepSet s t (0 : Kernel α Ω) μ := by
  simp [IndepSet]

lemma iIndepSets_congr (h : κ =ᵐ[μ] η) : iIndepSets π κ μ ↔ iIndepSets π η μ := by
  peel 3
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;>
  · filter_upwards [h, h'] with a ha h'a
    simpa [ha] using h'a

alias ⟨iIndepSets.congr, _⟩ := iIndepSets_congr

lemma indepSets_congr (h : κ =ᵐ[μ] η) : IndepSets s1 s2 κ μ ↔ IndepSets s1 s2 η μ := by
  peel 4
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;>
  · filter_upwards [h, h'] with a ha h'a
    simpa [ha] using h'a

alias ⟨IndepSets.congr, _⟩ := indepSets_congr

lemma iIndep_congr (h : κ =ᵐ[μ] η) : iIndep m κ μ ↔ iIndep m η μ :=
  iIndepSets_congr h

alias ⟨iIndep.congr, _⟩ := iIndep_congr

lemma indep_congr {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ η : Kernel α Ω} (h : κ =ᵐ[μ] η) : Indep m₁ m₂ κ μ ↔ Indep m₁ m₂ η μ :=
  indepSets_congr h

alias ⟨Indep.congr, _⟩ := indep_congr

lemma iIndepSet_congr (h : κ =ᵐ[μ] η) : iIndepSet s κ μ ↔ iIndepSet s η μ :=
  iIndep_congr h

alias ⟨iIndepSet.congr, _⟩ := iIndepSet_congr

lemma indepSet_congr {s t : Set Ω} (h : κ =ᵐ[μ] η) : IndepSet s t κ μ ↔ IndepSet s t η μ :=
  indep_congr h

alias ⟨indepSet.congr, _⟩ := indepSet_congr

lemma iIndepSets.meas_biInter (h : iIndepSets π κ μ) (s : Finset ι)
    {f : ι → Set Ω} (hf : ∀ i, i ∈ s → f i ∈ π i) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) := h s hf

lemma iIndepSets.ae_isProbabilityMeasure (h : iIndepSets π κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) := by
  filter_upwards [h.meas_biInter ∅ (f := fun _ ↦ Set.univ) (by simp)] with a ha
  exact ⟨by simpa using ha⟩

lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π κ μ) (hs : ∀ i, s i ∈ π i) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := by
  filter_upwards [h.meas_biInter Finset.univ (fun _i _ ↦ hs _)] with a ha using by simp [← ha]

lemma iIndep.iIndepSets' (hμ : iIndep m κ μ) :
    iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ := hμ

lemma iIndep.ae_isProbabilityMeasure (h : iIndep m κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) :=
  h.iIndepSets'.ae_isProbabilityMeasure

lemma iIndep.meas_biInter (hμ : iIndep m κ μ) (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := hμ _ hs

lemma iIndep.meas_iInter [Fintype ι] (h : iIndep m κ μ) (hs : ∀ i, MeasurableSet[m i] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := by
  filter_upwards [h.meas_biInter (fun i (_ : i ∈ Finset.univ) ↦ hs _)] with a ha
  simp [← ha]

@[nontriviality, simp]
lemma iIndepSets.of_subsingleton [Subsingleton ι] {m : ι → Set (Set Ω)} {κ : Kernel α Ω}
    [IsMarkovKernel κ] : iIndepSets m κ μ := by
  rintro s f hf
  obtain rfl | ⟨i, rfl⟩ : s = ∅ ∨ ∃ i, s = {i} := by
    simpa using (subsingleton_of_subsingleton (s := (s : Set ι))).eq_empty_or_singleton
  all_goals simp

@[nontriviality, simp]
lemma iIndep.of_subsingleton [Subsingleton ι] {m : ι → MeasurableSpace Ω} {κ : Kernel α Ω}
    [IsMarkovKernel κ] : iIndep m κ μ := by simp [iIndep]

lemma iIndepSets.precomp (hg : Function.Injective g) (h : iIndepSets π κ μ) :
    iIndepSets (π ∘ g) κ μ := by
  intro s f hf
  let f' := Function.extend g f fun _ => ∅
  have f'_apply x : f' (g x) = f x := hg.extend_apply ..
  classical
  have hf' : ∀ i ∈ s.image g, f' i ∈ π i := by
    simp_rw [Finset.forall_mem_image, f'_apply]
    exact hf
  filter_upwards [@h (s.image g) f' hf'] with a ha
  simpa [Finset.set_biInter_finset_image, Finset.prod_image hg.injOn, f'_apply] using ha

lemma iIndepSets.of_precomp (hg : Function.Surjective g) (h : iIndepSets (π ∘ g) κ μ) :
    iIndepSets π κ μ := by
  obtain ⟨g', hg'⟩ := hg.hasRightInverse
  convert h.precomp hg'.injective
  rw [Function.comp_assoc, hg'.comp_eq_id, Function.comp_id]

lemma iIndepSets_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSets (π ∘ g) κ μ ↔ iIndepSets π κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

lemma iIndep.precomp (hg : Function.Injective g) (h : iIndep m κ μ) :
    iIndep (m ∘ g) κ μ :=
  (iIndepSets.precomp hg h :)

lemma iIndep.of_precomp (hg : Function.Surjective g) (h : iIndep (m ∘ g) κ μ) :
    iIndep m κ μ :=
  iIndepSets.of_precomp hg h

lemma iIndep_precomp_of_bijective (hg : Function.Bijective g) :
    iIndep (m ∘ g) κ μ ↔ iIndep m κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

lemma iIndepSet.precomp (hg : Function.Injective g) (h : iIndepSet s κ μ) :
    iIndepSet (s ∘ g) κ μ :=
  iIndep.precomp hg h

lemma iIndepSet.of_precomp (hg : Function.Surjective g) (h : iIndepSet (s ∘ g) κ μ) :
    iIndepSet s κ μ :=
  iIndep.of_precomp hg h

lemma iIndepSet_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSet (s ∘ g) κ μ ↔ iIndepSet s κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

section Indep

variable {_mα : MeasurableSpace α}

@[symm]
theorem IndepSets.symm {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
    {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ κ μ) :
    IndepSets s₂ s₁ κ μ := by
  intro t1 t2 ht1 ht2
  filter_upwards [h t2 t1 ht2 ht1] with a ha
  rwa [Set.inter_comm, mul_comm]

@[symm]
theorem Indep.symm {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} (h : Indep m₁ m₂ κ μ) :
    Indep m₂ m₁ κ μ :=
  IndepSets.symm h

theorem indep_bot_right (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] :
    Indep m' ⊥ κ μ := by
  intro s t _ ht
  rw [Set.mem_setOf_eq, MeasurableSpace.measurableSet_bot_iff] at ht
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  refine Filter.Eventually.of_forall (fun a ↦ ?_)
  rcases ht with ht | ht
  · rw [ht, Set.inter_empty, measure_empty, mul_zero]
  · rw [ht, Set.inter_univ, measure_univ, mul_one]

theorem indep_bot_left (m' : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] :
    Indep ⊥ m' κ μ := (indep_bot_right m').symm

theorem indepSet_empty_right {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (s : Set Ω) :
    IndepSet s ∅ κ μ := by
  simp only [IndepSet, generateFrom_singleton_empty]
  exact indep_bot_right _

theorem indepSet_empty_left {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} [IsZeroOrMarkovKernel κ] (s : Set Ω) :
    IndepSet ∅ s κ μ :=
  (indepSet_empty_right s).symm

theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h31 : s₃ ⊆ s₁) :
    IndepSets s₃ s₂ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : IndepSets s₁ s₂ κ μ) (h32 : s₃ ⊆ s₂) :
    IndepSets s₁ s₃ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem indep_of_indep_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h31 : m₃ ≤ m₁) :
    Indep m₃ m₂ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem indep_of_indep_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : Indep m₁ m₂ κ μ) (h32 : m₃ ≤ m₂) :
    Indep m₁ m₃ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α}
    (h₁ : IndepSets s₁ s' κ μ) (h₂ : IndepSets s₂ s' κ μ) :
    IndepSets (s₁ ∪ s₂) s' κ μ := by
  intro t1 t2 ht1 ht2
  rcases (Set.mem_union _ _ _).mp ht1 with ht1₁ | ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
  · exact h₂ t1 t2 ht1₂ ht2

@[simp]
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    IndepSets (s₁ ∪ s₂) s' κ μ ↔ IndepSets s₁ s' κ μ ∧ IndepSets s₂ s' κ μ :=
  ⟨fun h =>
    ⟨indepSets_of_indepSets_of_le_left h Set.subset_union_left,
      indepSets_of_indepSets_of_le_left h Set.subset_union_right⟩,
    fun h => IndepSets.union h.left h.right⟩

theorem IndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (hyp : ∀ n, IndepSets (s n) s' κ μ) :
    IndepSets (⋃ n, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_iUnion] at ht1
  obtain ⟨n, ht1⟩ := ht1
  exact hyp n t1 t2 ht1 ht2

theorem IndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {u : Set ι} (hyp : ∀ n ∈ u, IndepSets (s n) s' κ μ) :
    IndepSets (⋃ n ∈ u, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_iUnion] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2

@[deprecated (since := "2025-11-02")] alias IndepSets.bUnion := IndepSets.biUnion

theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h₁ : IndepSets s₁ s' κ μ) :
    IndepSets (s₁ ∩ s₂) s' κ μ :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

theorem IndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h : ∃ n, IndepSets (s n) s' κ μ) :
    IndepSets (⋂ n, s n) s' κ μ := by
  intro t1 t2 ht1 ht2; obtain ⟨n, h⟩ := h; exact h t1 t2 (Set.mem_iInter.mp ht1 n) ht2

theorem IndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {u : Set ι} (h : ∃ n ∈ u, IndepSets (s n) s' κ μ) :
    IndepSets (⋂ n ∈ u, s n) s' κ μ := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.biInter_subset_of_mem hn ht1) ht2

theorem iIndep_comap_mem_iff {f : ι → Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    iIndep (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) κ μ ↔ iIndepSet f κ μ := by
  simp_rw [← generateFrom_singleton, iIndepSet]

theorem iIndepSets_singleton_iff {s : ι → Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    iIndepSets (fun i ↦ {s i}) κ μ ↔
      ∀ S : Finset ι, ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := by
  refine ⟨fun h S ↦ h S (fun i _ ↦ rfl), fun h S f hf ↦ ?_⟩
  filter_upwards [h S] with a ha
  have : ∀ i ∈ S, κ a (f i) = κ a (s i) := fun i hi ↦ by rw [hf i hi]
  rwa [Finset.prod_congr rfl this, Set.iInter₂_congr hf]

theorem indepSets_singleton_iff {s t : Set Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} :
    IndepSets {s} {t} κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  ⟨fun h ↦ h s t rfl rfl,
   fun h s1 t1 hs1 ht1 ↦ by rwa [Set.mem_singleton_iff.mp hs1, Set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromiIndepToIndep

variable {_mα : MeasurableSpace α}

theorem iIndepSets.indepSets {s : ι → Set (Set Ω)} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} (h_indep : iIndepSets s κ μ) {i j : ι} (hij : i ≠ j) :
    IndepSets (s i) (s j) κ μ := by
  classical
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ ({i, j} : Finset ι) → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simp [hx, ht₁]
    · simp [Finset.mem_singleton.mp hx, hij.symm, ht₂]
  have h_inter : ⋂ (t : ι) (_ : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂ =
      ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ := by
    simp only [Finset.set_biInter_singleton, Finset.set_biInter_insert]
  filter_upwards [h_indep {i, j} hf_m] with a h_indep'
  grind

theorem iIndep.indep {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α}
    (h_indep : iIndep m κ μ) {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) κ μ :=
  iIndepSets.indepSets h_indep hij

end FromiIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variable {_mα : MeasurableSpace α}

theorem iIndep.iIndepSets {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {m : ι → MeasurableSpace Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n)) (h_indep : iIndep m κ μ) :
    iIndepSets s κ μ :=
  fun S f hfs =>
  h_indep S fun x hxS =>
    ((hms x).symm ▸ measurableSet_generateFrom (hfs x hxS) : MeasurableSet[m x] (f x))

theorem Indep.indepSets {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) κ μ) :
    IndepSets s1 s2 κ μ :=
  fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSet_generateFrom ht1) (measurableSet_generateFrom ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

variable {_mα : MeasurableSpace α}

theorem IndepSets.indep_aux {m₂ m : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)} (h2 : m₂ ≤ m)
    (hp2 : IsPiSystem p2) (hpm2 : m₂ = generateFrom p2) (hyp : IndepSets p1 p2 κ μ) {t1 t2 : Set Ω}
    (ht1 : t1 ∈ p1) (ht1m : MeasurableSet[m] t1) (ht2m : MeasurableSet[m₂] t2) :
    ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2 := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  induction t2, ht2m using induction_on_inter hpm2 hp2 with
  | empty => simp
  | basic u hu => exact hyp t1 u ht1 hu
  | compl u hu ihu =>
    filter_upwards [ihu] with a ha
    rw [← Set.diff_eq, ← Set.diff_self_inter,
      measure_diff inter_subset_left (ht1m.inter (h2 _ hu)).nullMeasurableSet (measure_ne_top _ _),
      ha, measure_compl (h2 _ hu) (measure_ne_top _ _), measure_univ, ENNReal.mul_sub, mul_one]
    exact fun _ _ ↦ measure_ne_top _ _
  | iUnion f hfd hfm ihf =>
    rw [← ae_all_iff] at ihf
    filter_upwards [ihf] with a ha
    rw [inter_iUnion, measure_iUnion, measure_iUnion hfd fun i ↦ h2 _ (hfm i)]
    · simp only [ENNReal.tsum_mul_left, ha]
    · exact hfd.mono fun i j h ↦ (h.inter_left' _).inter_right' _
    · exact fun i ↦ .inter ht1m (h2 _ <| hfm i)

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem IndepSets.indep {m1 m2 m : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
    [IsZeroOrMarkovKernel κ] {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 κ μ) :
    Indep m1 m2 κ μ := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp
  intro t1 t2 ht1 ht2
  induction t1, ht1 using induction_on_inter hpm1 hp1 with
  | empty =>
    simp only [Set.empty_inter, measure_empty, zero_mul, Filter.eventually_true]
  | basic t ht =>
    refine IndepSets.indep_aux h2 hp2 hpm2 hyp ht (h1 _ ?_) ht2
    rw [hpm1]
    exact measurableSet_generateFrom ht
  | compl t ht iht =>
    filter_upwards [iht] with a ha
    have : tᶜ ∩ t2 = t2 \ (t ∩ t2) := by
      rw [Set.inter_comm t, Set.diff_self_inter, Set.diff_eq_compl_inter]
    rw [this, Set.inter_comm t t2,
      measure_diff Set.inter_subset_left ((h2 _ ht2).inter (h1 _ ht)).nullMeasurableSet
        (measure_ne_top (κ a) _),
      Set.inter_comm, ha, measure_compl (h1 _ ht) (measure_ne_top (κ a) t), measure_univ,
      mul_comm (1 - κ a t), ENNReal.mul_sub (fun _ _ ↦ measure_ne_top (κ a) _), mul_one, mul_comm]
  | iUnion f hf_disj hf_meas h =>
    rw [← ae_all_iff] at h
    filter_upwards [h] with a ha
    rw [Set.inter_comm, Set.inter_iUnion, measure_iUnion]
    · rw [measure_iUnion hf_disj (fun i ↦ h1 _ (hf_meas i))]
      rw [← ENNReal.tsum_mul_right]
      congr 1 with i
      rw [Set.inter_comm t2, ha i]
    · intro i j hij
      rw [Function.onFun, Set.inter_comm t2, Set.inter_comm t2]
      exact Disjoint.inter_left _ (Disjoint.inter_right _ (hf_disj hij))
    · exact fun i ↦ (h2 _ ht2).inter (h1 _ (hf_meas i))

theorem IndepSets.indep' {_mΩ : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    {p1 p2 : Set (Set Ω)} (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 κ μ) :
    Indep (generateFrom p1) (generateFrom p2) κ μ :=
  hyp.indep (generateFrom_le hp1m) (generateFrom_le hp2m) hp1 hp2 rfl rfl

variable {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}

theorem indepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s κ μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) κ μ := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
  let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
  have h_P_inter : ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = ∏ n ∈ p1 ∪ p2, κ a (g n) := by
    have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
      intro i hi_mem_union
      rw [Finset.mem_union] at hi_mem_union
      rcases hi_mem_union with hi1 | hi2
      · have hi2 : i ∉ p2 := fun hip2 => Set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
        simp_rw [g, if_pos hi1, if_neg hi2, Set.inter_univ]
        exact ht1_m i hi1
      · have hi1 : i ∉ p1 := fun hip1 => Set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
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
    filter_upwards [h_indep _ hgm] with a ha
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← ha]
  filter_upwards [h_P_inter, h_indep p1 ht1_m, h_indep p2 ht2_m, h_indep.ae_isProbabilityMeasure]
    with a h_P_inter ha1 ha2 h'
  have h_μg : ∀ n, κ a (g n) = (ite (n ∈ p1) (κ a (f1 n)) 1) * (ite (n ∈ p2) (κ a (f2 n)) 1) := by
    intro n
    dsimp only [g]
    split_ifs with h1 h2
    · exact absurd rfl (Set.disjoint_iff_forall_ne.mp hST (hp1 h1) (hp2 h2))
    all_goals simp only [measure_univ, one_mul, mul_one, Set.inter_univ, Set.univ_inter]
  simp_rw [h_P_inter, h_μg, Finset.prod_mul_distrib,
    Finset.prod_ite_mem (p1 ∪ p2) p1 (fun x ↦ κ a (f1 x)), Finset.union_inter_cancel_left,
    Finset.prod_ite_mem (p1 ∪ p2) p2 (fun x => κ a (f2 x)), Finset.union_inter_cancel_right, ht1_eq,
      ← ha1, ht2_eq, ← ha2]

theorem iIndepSet.indep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) κ μ := by
  classical
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hs.ae_isProbabilityMeasure hμ
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  refine
    IndepSets.indep'
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht))
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht)) ?_ ?_ ?_
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact indepSets_piiUnionInter_of_disjoint (iIndep.iIndepSets (fun n => rfl) (hs.congr η_eq)) hST

theorem indep_iSup_of_disjoint {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m κ μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) κ μ := by
  classical
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  refine
    IndepSets.indep (iSup₂_le fun i _ => h_le i) (iSup₂_le fun i _ => h_le i) ?_ ?_
      (generateFrom_piiUnionInter_measurableSet m S).symm
      (generateFrom_piiUnionInter_measurableSet m T).symm ?_
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact indepSets_piiUnionInter_of_disjoint (h_indep.congr η_eq) hST

theorem indep_iSup_of_directed_le {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ] (h_indep : ∀ i, Indep (m i) m' κ μ)
    (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : Directed (· ≤ ·) m) :
    Indep (⨆ i, m i) m' κ μ := by
  let p : ι → Set (Set Ω) := fun n => { t | MeasurableSet[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @isPiSystem_measurableSet Ω (m n)
  have h_gen_n : ∀ n, m n = generateFrom (p n) := fun n =>
    (@generateFrom_measurableSet Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hm
  let p' := { t : Set Ω | MeasurableSet[m'] t }
  have hp'_pi : IsPiSystem p' := @isPiSystem_measurableSet Ω m'
  have h_gen' : m' = generateFrom p' := (@generateFrom_measurableSet Ω m').symm
  -- the π-systems defined are independent
  have h_pi_system_indep : IndepSets (⋃ n, p n) p' κ μ := by
    refine IndepSets.iUnion ?_
    conv at h_indep =>
      intro i
      rw [h_gen_n i, h_gen']
    exact fun n => (h_indep n).indepSets
  -- now go from π-systems to σ-algebras
  refine IndepSets.indep (iSup_le h_le) h_le' hp_supr_pi hp'_pi ?_ h_gen' h_pi_system_indep
  exact (generateFrom_iUnion_measurableSet _).symm

theorem iIndepSet.indep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) κ μ := by
  convert iIndepSet.indep_generateFrom_of_disjoint hsm hs {i} { j | j < i }
    (Set.disjoint_singleton_left.mpr (lt_irrefl _)) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.setOf_eq_eq_singleton']

theorem iIndepSet.indep_generateFrom_le [Preorder ι] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) κ μ := by
  convert iIndepSet.indep_generateFrom_of_disjoint hsm hs {k} { j | j ≤ i }
      (Set.disjoint_singleton_left.mpr hk.not_ge) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.setOf_eq_eq_singleton']

theorem iIndepSet.indep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s κ μ) (n : ℕ) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) κ μ :=
  iIndepSet.indep_generateFrom_le hsm hs _ n.lt_succ_self

theorem indep_iSup_of_monotone [SemilatticeSup ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    (h_indep : ∀ i, Indep (m i) m' κ μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Monotone m) :
    Indep (⨆ i, m i) m' κ μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' (Monotone.directed_le hm)

theorem indep_iSup_of_antitone [SemilatticeInf ι] {Ω} {m : ι → MeasurableSpace Ω}
    {m' m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α} [IsZeroOrMarkovKernel κ]
    (h_indep : ∀ i, Indep (m i) m' κ μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Antitone m) :
    Indep (⨆ i, m i) m' κ μ :=
  indep_iSup_of_directed_le h_indep h_le h_le' hm.directed_le

theorem iIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π κ μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) κ μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
  let f := fun n => ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
    intro n hn_mem_insert
    dsimp only [f]
    rcases Finset.mem_insert.mp hn_mem_insert with hn_mem | hn_mem
    · simp [hn_mem, ht2_mem_pia]
    · grind
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀ n ∈ s, f n = ft1 n by grind
    intro n hnS
    have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
    simp_rw [f, if_pos hnS, if_neg hn_ne_a]
  have h_μ_t1 : ∀ᵐ a' ∂μ, κ a' t1 = ∏ n ∈ s, κ a' (f n) := by
    filter_upwards [hp_ind s h_f_mem_pi] with a' ha'
    rw [h_t1, ← ha']
  have h_t2 : t2 = f a := by simp [f]
  have h_μ_inter : ∀ᵐ a' ∂μ, κ a' (t1 ∩ t2) = ∏ n ∈ insert a s, κ a' (f n) := by
    have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
      rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
    filter_upwards [hp_ind (insert a s) h_f_mem] with a' ha'
    rw [h_t1_inter_t2, ← ha']
  have has : a ∉ s := fun has_mem => haS (hs_mem has_mem)
  filter_upwards [h_μ_t1, h_μ_inter] with a' ha1 ha2
  rw [ha2, Finset.prod_insert has, h_t2, mul_comm, ha1]

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem iIndepSets.iIndep (m : ι → MeasurableSpace Ω)
    (h_le : ∀ i, m i ≤ _mΩ) (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n))
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : iIndepSets π κ μ) :
    iIndep m κ μ := by
  classical
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_ind.ae_isProbabilityMeasure hμ
  apply iIndep.congr (Filter.EventuallyEq.symm η_eq)
  intro s f
  refine Finset.induction ?_ ?_ s
  · simp only [Finset.notMem_empty, Set.mem_setOf_eq, IsEmpty.forall_iff, implies_true,
      Set.iInter_of_empty, Set.iInter_univ, measure_univ, Finset.prod_empty,
      Filter.eventually_true]
  · intro a S ha_notin_S h_rec hf_m
    have hf_m_S : ∀ x ∈ S, MeasurableSet[m x] (f x) := fun x hx => hf_m x (by simp [hx])
    let p := piiUnionInter π S
    set m_p := generateFrom p with hS_eq_generate
    have h_indep : Indep m_p (m a) η μ := by
      have hp : IsPiSystem p := isPiSystem_piiUnionInter π h_pi S
      have h_le' : ∀ i, generateFrom (π i) ≤ _mΩ := fun i ↦ (h_generate i).symm.trans_le (h_le i)
      have hm_p : m_p ≤ _mΩ := generateFrom_piiUnionInter_le π h_le' S
      exact IndepSets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
        (iIndepSets.piiUnionInter_of_notMem (h_ind.congr η_eq) ha_notin_S)
    have h := h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) ?_
    · filter_upwards [h_rec hf_m_S, h] with a' ha' h'
      rwa [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S, ← ha']
    · have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
        intro n hn
        rw [hS_eq_generate, h_generate n]
        exact le_generateFrom_piiUnionInter (S : Set ι) hn
      have h_S_f : ∀ i ∈ S, MeasurableSet[m_p] (f i) :=
        fun i hi ↦ (h_le_p i hi) (f i) (hf_m_S i hi)
      exact S.measurableSet_biInter h_S_f

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t`,
* `IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ`.
-/

variable {_mα : MeasurableSpace α}

theorem iIndepSet_iff_iIndepSets_singleton {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f κ μ ↔ iIndepSets (fun i ↦ {f i}) κ μ :=
  ⟨iIndep.iIndepSets fun _ ↦ rfl,
    iIndepSets.iIndep _ (fun i ↦ generateFrom_le <| by rintro t (rfl : t = _); exact hf _) _
      (fun _ ↦ IsPiSystem.singleton _) fun _ ↦ rfl⟩

theorem iIndepSet.meas_biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (h : iIndepSet f κ μ) (s : Finset ι) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) :=
  iIndep.iIndepSets (fun _ ↦ rfl) h _ (by simp)

theorem iIndepSet_iff_meas_biInter {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {f : ι → Set Ω} (hf : ∀ i, MeasurableSet (f i)) :
    iIndepSet f κ μ ↔ ∀ s, ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i) :=
  (iIndepSet_iff_iIndepSets_singleton hf).trans iIndepSets_singleton_iff

theorem iIndepSets.iIndepSet_of_mem {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α} {π : ι → Set (Set Ω)} {f : ι → Set Ω}
    (hfπ : ∀ i, f i ∈ π i) (hf : ∀ i, MeasurableSet (f i)) (hπ : iIndepSets π κ μ) :
    iIndepSet f κ μ :=
  (iIndepSet_iff_meas_biInter hf).2 fun _t ↦ hπ.meas_biInter _ fun _i _ ↦ hfπ _

variable {s t : Set Ω} (S T : Set (Set Ω))

theorem indepSet_iff_indepSets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α)
    [IsZeroOrMarkovKernel κ] :
    IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ :=
  ⟨Indep.indepSets, fun h =>
    IndepSets.indep
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (IsPiSystem.singleton s) (IsPiSystem.singleton t) rfl rfl h⟩

theorem indepSet_iff_measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (κ : Kernel α Ω) (μ : Measure α)
    [IsZeroOrMarkovKernel κ] :
    IndepSet s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas κ μ).trans indepSets_singleton_iff

theorem IndepSet.measure_inter_eq_mul {_m0 : MeasurableSpace Ω} (κ : Kernel α Ω) (μ : Measure α)
    (h : IndepSet s t κ μ) : ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
  Indep.indepSets h _ _ (by simp) (by simp)

theorem IndepSets.indepSet_of_mem {_m0 : MeasurableSpace Ω} (hs : s ∈ S) (ht : t ∈ T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (κ : Kernel α Ω) (μ : Measure α) [IsZeroOrMarkovKernel κ]
    (h_indep : IndepSets S T κ μ) :
    IndepSet s t κ μ :=
  (indepSet_iff_measure_inter_eq_mul hs_meas ht_meas κ μ).mpr (h_indep s t hs ht)

theorem Indep.indepSet_of_measurableSet {m₁ m₂ _ : MeasurableSpace Ω} {κ : Kernel α Ω}
    {μ : Measure α}
    (h_indep : Indep m₁ m₂ κ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) :
    IndepSet s t κ μ := by
  refine fun s' t' hs' ht' => h_indep s' t' ?_ ?_
  · induction s', hs' using generateFrom_induction with
    | hC t ht => exact ht ▸ hs
    | empty => exact @MeasurableSet.empty _ m₁
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf
  · induction t', ht' using generateFrom_induction with
    | hC s hs => exact hs ▸ ht
    | empty => exact @MeasurableSet.empty _ m₂
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf

theorem indep_iff_forall_indepSet (m₁ m₂ : MeasurableSpace Ω) {_m0 : MeasurableSpace Ω}
    (κ : Kernel α Ω) (μ : Measure α) :
    Indep m₁ m₂ κ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t κ μ :=
  ⟨fun h => fun _s _t hs ht => h.indepSet_of_measurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSet_generateFrom (Set.mem_singleton s))
      (measurableSet_generateFrom (Set.mem_singleton t))⟩

end IndepSet

end ProbabilityTheory.Kernel
