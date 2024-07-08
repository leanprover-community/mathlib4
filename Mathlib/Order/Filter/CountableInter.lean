/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Order.Filter.Curry
import Mathlib.Data.Set.Countable

#align_import order.filter.countable_Inter from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Filters with countable intersection property

In this file we define `CountableInterFilter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `Mathlib.Topology.GDelta` and
the `MeasureTheory.ae` filter defined in `Mathlib/MeasureTheory.OuterMeasure/AE`.

We reformulate the definition in terms of indexed intersection and in terms of `Filter.Eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `Filter.principal`, `Filter.map`,
`Filter.comap`, `Inf.inf`). We also provide a custom constructor `Filter.ofCountableInter`
that deduces two axioms of a `Filter` from the countable intersection property.

Note that there also exists a typeclass `CardinalInterFilter`, and thus an alternative spelling of
`CountableInterFilter` as `CardinalInterFilter l (aleph 1)`. The former (defined here) is the
preferred spelling; it has the advantage of not requiring the user to import the theory ordinals.

## Tags
filter, countable
-/


open Set Filter

open Filter

variable {ι : Sort*} {α β : Type*}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l
#align countable_Inter_filter CountableInterFilter

variable {l : Filter α} [CountableInterFilter l]

theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩
#align countable_sInter_mem countable_sInter_mem

theorem countable_iInter_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_mem_range
#align countable_Inter_mem countable_iInter_mem

theorem countable_bInter_mem {ι : Type*} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  haveI := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall
#align countable_bInter_mem countable_bInter_mem

theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }
#align eventually_countable_forall eventually_countable_forall

theorem eventually_countable_ball {ι : Type*} {S : Set ι} (hS : S.Countable)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }
#align eventually_countable_ball eventually_countable_ball

theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 <| (mem_iUnion.1 hs).imp hst
#align eventually_le.countable_Union EventuallyLE.countable_iUnion

theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)
#align eventually_eq.countable_Union EventuallyEq.countable_iUnion

theorem EventuallyLE.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  haveI := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2
#align eventually_le.countable_bUnion EventuallyLE.countable_bUnion

theorem EventuallyEq.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bUnion EventuallyEq.countable_bUnion

theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)
#align eventually_le.countable_Inter EventuallyLE.countable_iInter

theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)
#align eventually_eq.countable_Inter EventuallyEq.countable_iInter

theorem EventuallyLE.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  haveI := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2
#align eventually_le.countable_bInter EventuallyLE.countable_bInter

theorem EventuallyEq.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bInter EventuallyEq.countable_bInter

/-- Construct a filter with countable intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter

instance Filter.countableInter_ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hl h_mono) :=
  ⟨hl⟩
#align filter.countable_Inter_of_countable_Inter Filter.countableInter_ofCountableInter

@[simp]
theorem Filter.mem_ofCountableInter {l : Set (Set α)}
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hl h_mono ↔ s ∈ l :=
  Iff.rfl
#align filter.mem_of_countable_Inter Filter.mem_ofCountableInter

/-- Construct a filter with countable intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCountableInter`,
this constructor deduces some properties from the countable intersection property
which becomes the countable union property because we take complements of all sets. -/
def Filter.ofCountableUnion (l : Set (Set α))
    (hUnion : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCountableInter {s | sᶜ ∈ l} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_setOf_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

instance Filter.countableInter_ofCountableUnion (l : Set (Set α)) (h₁ h₂) :
    CountableInterFilter (Filter.ofCountableUnion l h₁ h₂) :=
  countableInter_ofCountableInter ..

@[simp]
theorem Filter.mem_ofCountableUnion {l : Set (Set α)} {hunion hmono s} :
    s ∈ ofCountableUnion l hunion hmono ↔ l sᶜ :=
  Iff.rfl

instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal

instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]
  apply countableInterFilter_principal
#align countable_Inter_filter_bot countableInterFilter_bot

instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by
  rw [← principal_univ]
  apply countableInterFilter_principal
#align countable_Inter_filter_top countableInterFilter_top

instance (l : Filter β) [CountableInterFilter l] (f : α → β) :
    CountableInterFilter (comap f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  refine ⟨_, this, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (countable_bInter_mem hSc).2 hS

/-- Infimum of two `CountableInterFilter`s is a `CountableInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)
#align countable_Inter_filter_inf countableInterFilter_inf

/-- Supremum of two `CountableInterFilter`s is a `CountableInterFilter`. -/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (countable_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]
#align countable_Inter_filter_sup countableInterFilter_sup

instance CountableInterFilter.curry {α β : Type*} {l : Filter α} {m : Filter β}
    [CountableInterFilter l] [CountableInterFilter m] : CountableInterFilter (l.curry m) := ⟨by
  intro S Sct hS
  simp_rw [mem_curry_iff, mem_sInter, eventually_countable_ball (p := fun _ _ _ => (_ ,_) ∈ _) Sct,
    eventually_countable_ball (p := fun _ _ _ => ∀ᶠ (_ : β) in m, _)  Sct, ← mem_curry_iff]
  exact hS⟩

namespace Filter

variable (g : Set (Set α))

/-- `Filter.CountableGenerateSets g` is the (sets of the)
greatest `countableInterFilter` containing `g`. -/
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
#align filter.countable_generate_sets Filter.CountableGenerateSets

/-- `Filter.countableGenerate g` is the greatest `countableInterFilter` containing `g`. -/
def countableGenerate : Filter α :=
  ofCountableInter (CountableGenerateSets g) (fun _ => CountableGenerateSets.sInter) fun _ _ =>
    CountableGenerateSets.superset
  --deriving CountableInterFilter
#align filter.countable_generate Filter.countableGenerate

-- Porting note: could not de derived
instance : CountableInterFilter (countableGenerate g) := by
  delta countableGenerate; infer_instance

variable {g}

/-- A set is in the `countableInterFilter` generated by `g` if and only if
it contains a countable intersection of elements of `g`. -/
theorem mem_countableGenerate_iff {s : Set α} :
    s ∈ countableGenerate g ↔ ∃ S : Set (Set α), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction' h with s hs s t _ st ih S Sct _ ih
    · exact ⟨{s}, by simp [hs, subset_refl]⟩
    · exact ⟨∅, by simp⟩
    · refine Exists.imp (fun S => ?_) ih
      tauto
    choose T Tg Tct hT using ih
    refine ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, Sct.biUnion Tct, ?_⟩
    apply subset_sInter
    intro s H
    exact subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine mem_of_superset ((countable_sInter_mem Sct).mpr ?_) hS
  intro s H
  exact CountableGenerateSets.basic (Sg H)
#align filter.mem_countable_generate_iff Filter.mem_countableGenerate_iff

theorem le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] :
    f ≤ countableGenerate g ↔ g ⊆ f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
  intro s hs
  induction' hs with s hs s t _ st ih S Sct _ ih
  · exact h hs
  · exact univ_mem
  · exact mem_of_superset ih st
  exact (countable_sInter_mem Sct).mpr ih
#align filter.le_countable_generate_iff_of_countable_Inter_filter Filter.le_countableGenerate_iff_of_countableInterFilter

variable (g)

/-- `countableGenerate g` is the greatest `countableInterFilter` containing `g`. -/
theorem countableGenerate_isGreatest :
    IsGreatest { f : Filter α | CountableInterFilter f ∧ g ⊆ f.sets } (countableGenerate g) := by
  refine ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]
#align filter.countable_generate_is_greatest Filter.countableGenerate_isGreatest

end Filter
