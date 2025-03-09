/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.CountableInter
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Tactic.Linarith

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter l c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality strictly less than `c`,
their intersection belongs to `l` as well.

# Main results
* `Filter.cardinalInterFilter_aleph0` establishes that every filter `l` is a
    `CardinalInterFilter l ℵ₀`
* `CardinalInterFilter.toCountableInterFilter` establishes that every `CardinalInterFilter l c` with
    `c > ℵ₀` is a `CountableInterFilter`.
* `CountableInterFilter.toCardinalInterFilter` establishes that every `CountableInterFilter l` is a
    `CardinalInterFilter l ℵ₁`.
* `CardinalInterFilter.of_CardinalInterFilter_of_lt` establishes that we have
  `CardinalInterFilter l c` → `CardinalInterFilter l a` for all `a < c`.

## Tags
filter, cardinal
-/


open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u} {c : Cardinal.{u}}

/-- A filter `l` has the cardinal `c` intersection property if for any collection
of less than `c` sets `s ∈ l`, their intersection belongs to `l` as well. -/
class CardinalInterFilter (l : Filter α) (c : Cardinal.{u}) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α}

theorem cardinal_sInter_mem {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S < c) :
    ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

/-- Every filter is a CardinalInterFilter with c = ℵ₀ -/
theorem _root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFilter l ℵ₀ where
  cardinal_sInter_mem := by
    simp_all only [aleph_zero, lt_aleph0_iff_subtype_finite, setOf_mem_eq, sInter_mem,
      implies_true, forall_const]

/-- Every CardinalInterFilter with c > ℵ₀ is a CountableInterFilter -/
theorem CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFilter l c]
    (hc : ℵ₀ < c) : CountableInterFilter l where
  countable_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

/-- Every CountableInterFilter is a CardinalInterFilter with c = ℵ₁ -/
instance CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterFilter l] :
    CardinalInterFilter l ℵ₁ where
  cardinal_sInter_mem S hS a :=
    CountableInterFilter.countable_sInter_mem S ((countable_iff_lt_aleph_one S).mpr hS) a

theorem cardinalInterFilter_aleph_one_iff :
    CardinalInterFilter l ℵ₁ ↔ CountableInterFilter l :=
  ⟨fun _ ↦ ⟨fun S h a ↦
    CardinalInterFilter.cardinal_sInter_mem S ((countable_iff_lt_aleph_one S).1 h) a⟩,
   fun _ ↦ CountableInterFilter.toCardinalInterFilter l⟩

/-- Every CardinalInterFilter for some c also is a CardinalInterFilter for some a ≤ c -/
theorem CardinalInterFilter.of_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a ≤ c) :
    CardinalInterFilter l a where
  cardinal_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a

theorem CardinalInterFilter.of_cardinalInterFilter_of_lt (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a < c) : CardinalInterFilter l a :=
  CardinalInterFilter.of_cardinalInterFilter_of_le l (hac.le)

namespace Filter

variable [CardinalInterFilter l c]

theorem cardinal_iInter_mem {s : ι → Set α} (hic : #ι < c) :
    (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l := by
  rw [← sInter_range _]
  apply (cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)).trans
  exact forall_mem_range

theorem cardinal_bInter_mem {S : Set ι} (hS : #S < c)
    {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

theorem eventually_cardinal_forall {p : α → ι → Prop} (hic : #ι < c) :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_iInter_mem hic

theorem eventually_cardinal_ball {S : Set ι} (hS : #S < c)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_bInter_mem hS

theorem EventuallyLE.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2 <|
    (mem_iUnion.1 hs).imp hst

theorem EventuallyEq.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

theorem EventuallyEq.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

theorem EventuallyLE.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

theorem EventuallyEq.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

theorem EventuallyEq.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

/-- Construct a filter with cardinal `c` intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal `c` intersection property. -/
def ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets :=
    sInter_empty ▸ hl ∅ (mk_eq_zero (∅ : Set (Set α)) ▸ lt_trans zero_lt_two hc) (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hl _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) ≤ 2 := by
      calc
      _ ≤ #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc

instance cardinalInter_ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CardinalInterFilter (Filter.ofCardinalInter l hc hl h_mono) c :=
  ⟨hl⟩

@[simp]
theorem mem_ofCardinalInter {l : Set (Set α)} (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCardinalInter l hc hl h_mono ↔ s ∈ l :=
  Iff.rfl

/-- Construct a filter with cardinal `c` intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCardinalInter`,
this constructor deduces some properties from the cardinal `c` intersection property
which becomes the cardinal `c` union property because we take complements of all sets. -/
def ofCardinalUnion (l : Set (Set α)) (hc : 2 < c)
    (hUnion : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCardinalInter {s | sᶜ ∈ l} hc (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    apply hUnion (compl '' S) (lt_of_le_of_lt mk_image_le hSc)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_setOf_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub

instance cardinalInter_ofCardinalUnion (l : Set (Set α)) (hc : 2 < c) (h₁ h₂) :
    CardinalInterFilter (Filter.ofCardinalUnion l hc h₁ h₂) c :=
  cardinalInter_ofCardinalInter ..

@[simp]
theorem mem_ofCardinalUnion {l : Set (Set α)} (hc : 2 < c) {hunion hmono s} :
    s ∈ ofCardinalUnion l hc hunion hmono ↔ l sᶜ :=
  Iff.rfl

instance cardinalInterFilter_principal (s : Set α) : CardinalInterFilter (𝓟 s) c :=
  ⟨fun _ _ hS => subset_sInter hS⟩

instance cardinalInterFilter_bot : CardinalInterFilter (⊥ : Filter α) c := by
  rw [← principal_empty]
  apply cardinalInterFilter_principal

instance cardinalInterFilter_top : CardinalInterFilter (⊤ : Filter α) c := by
  rw [← principal_univ]
  apply cardinalInterFilter_principal

instance (l : Filter β) [CardinalInterFilter l c] (f : α → β) :
    CardinalInterFilter (comap f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  refine ⟨_, (cardinal_bInter_mem hSc).2 htl, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CardinalInterFilter l c] (f : α → β) :
    CardinalInterFilter (map f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (cardinal_bInter_mem hSc).2 hS

/-- Infimum of two `CardinalInterFilter`s is a `CardinalInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance cardinalInterFilter_inf_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊓ l₂) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (cardinal_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

instance cardinalInterFilter_inf (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊓ l₂)
    (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

/-- Supremum of two `CardinalInterFilter`s is a `CardinalInterFilter`. -/
instance cardinalInterFilter_sup_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊔ l₂) c := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (cardinal_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]

instance cardinalInterFilter_sup (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] :
    CardinalInterFilter (l₁ ⊔ l₂) (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

variable (g : Set (Set α))

/-- `Filter.CardinalGenerateSets c g` is the (sets of the)
greatest `cardinalInterFilter c` containing `g`. -/
inductive CardinalGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CardinalGenerateSets s
  | univ : CardinalGenerateSets univ
  | superset {s t : Set α} : CardinalGenerateSets s → s ⊆ t → CardinalGenerateSets t
  | sInter {S : Set (Set α)} :
    (#S < c) → (∀ s ∈ S, CardinalGenerateSets s) → CardinalGenerateSets (⋂₀ S)

/-- `Filter.cardinalGenerate c g` is the greatest `cardinalInterFilter c` containing `g`. -/
def cardinalGenerate (hc : 2 < c) : Filter α :=
  ofCardinalInter (CardinalGenerateSets g) hc (fun _ => CardinalGenerateSets.sInter) fun _ _ =>
    CardinalGenerateSets.superset

lemma cardinalInter_ofCardinalGenerate (hc : 2 < c) :
    CardinalInterFilter (cardinalGenerate g hc) c := by
  delta cardinalGenerate
  apply cardinalInter_ofCardinalInter _ _ _

variable {g}

/-- A set is in the `cardinalInterFilter` generated by `g` if and only if
it contains an intersection of `c` elements of `g`. -/
theorem mem_cardinaleGenerate_iff {s : Set α} {hreg : c.IsRegular} :
    s ∈ cardinalGenerate g (IsRegular.nat_lt hreg 2) ↔
    ∃ S : Set (Set α), S ⊆ g ∧ (#S < c) ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs =>
      refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      simpa [subset_refl] using IsRegular.nat_lt hreg 1
    | univ =>
      exact ⟨∅, ⟨empty_subset g, mk_eq_zero (∅ : Set <| Set α) ▸ IsRegular.nat_lt hreg 0, by simp⟩⟩
    | superset _ _ ih => exact Exists.imp (by tauto) ih
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s ∈ S), T s H, by simpa,
        (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hreg Sct).2 Tct, ?_⟩
      apply subset_sInter
      apply fun s H => subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  have : CardinalInterFilter (cardinalGenerate g (IsRegular.nat_lt hreg 2)) c :=
    cardinalInter_ofCardinalGenerate _ _
  exact mem_of_superset ((cardinal_sInter_mem Sct).mpr
    (fun s H => CardinalGenerateSets.basic (Sg H))) hS

theorem le_cardinalGenerate_iff_of_cardinalInterFilter {f : Filter α} [CardinalInterFilter f c]
    (hc : 2 < c) : f ≤ cardinalGenerate g hc ↔ g ⊆ f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (cardinal_sInter_mem Sct).mpr ih

/-- `cardinalGenerate g hc` is the greatest `cardinalInterFilter c` containing `g`. -/
theorem cardinalGenerate_isGreatest (hc : 2 < c) :
    IsGreatest { f : Filter α | CardinalInterFilter f c ∧ g ⊆ f.sets } (cardinalGenerate g hc) := by
  refine ⟨⟨cardinalInter_ofCardinalGenerate _ _, fun s => CardinalGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [le_cardinalGenerate_iff_of_cardinalInterFilter]

end Filter
