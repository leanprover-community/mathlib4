/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter l c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality strictly less than `c`,
their intersection belongs to `l` as well.

# Main results
* `Filter.cardinalInterFilter_aleph0` establishes that every filter `l` is a
    `CardinalInterFilter l aleph0`
* `CardinalInterFilter.toCountableInterFilter` establishes that every `CardinalInterFilter l c` with
    `c > aleph0` is a `CountableInterFilter`.
* `CountableInterFilter.toCardinalInterFilter` establishes that every `CountableInterFilter l` is a
    `CardinalInterFilter l aleph1`.
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

/-- Every filter is a CardinalInterFilter with c = aleph0 -/
theorem _root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFilter l aleph0 where
  cardinal_sInter_mem := by
    simp_all only [aleph_zero, lt_aleph0_iff_subtype_finite, setOf_mem_eq, sInter_mem,
      implies_true, forall_const]

/-- Every CardinalInterFilter with c > aleph0 is a CountableInterFilter -/
theorem CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFilter l c]
    (hc : aleph0 < c) : CountableInterFilter l where
  countable_sInter_mem := by
    intro S hS
    exact fun a ↦ CardinalInterFilter.cardinal_sInter_mem S
      (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

/-- Every CountableInterFilter is a CardinalInterFilter with c = aleph 1-/
instance CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterFilter l] :
    CardinalInterFilter l (aleph 1) where
  cardinal_sInter_mem := fun S hS a ↦ CountableInterFilter.countable_sInter_mem S
    ((countable_iff_lt_aleph_one S).mpr hS) a

theorem cardinalInterFilter_aleph_one_iff :
    CardinalInterFilter l (aleph 1) ↔ CountableInterFilter l :=
  ⟨fun _ ↦ ⟨fun S h a ↦
    CardinalInterFilter.cardinal_sInter_mem S ((countable_iff_lt_aleph_one S).1 h) a⟩,
   fun _ ↦ CountableInterFilter.toCardinalInterFilter l⟩

/-- Every CardinalInterFilter for some c also is a CardinalInterFilter for some a ≤ c -/
theorem CardinalInterFilter.of_CardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a ≤ c) :
  CardinalInterFilter l a where
    cardinal_sInter_mem :=
      fun S hS a ↦ CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a

theorem CardinalInterFilter.of_CardinalInterFilter_of_lt (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a < c) : CardinalInterFilter l a :=
  CardinalInterFilter.of_CardinalInterFilter_of_le l (hac.le)

namespace Filter

variable [CardinalInterFilter l c]

theorem cardinal_iInter_mem {s : ι → Set α} (hic : #ι < c) :
    (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l := by
  rw [← sInter_range _]
  apply Iff.trans
  apply cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)
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

lemma Cardinal.mk_insert_le {α : Type u} {s : Set α} {a : α} : #↑(insert a s) ≤ #↑s + 1 := by
  by_cases h : a ∈ s
  · simp [h]
  · rw [Cardinal.mk_insert h]

def ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hp : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := by
    apply @sInter_empty α ▸ hp ∅ (?_) (empty_subset _)
    have this : 0 < c := lt_trans zero_lt_two hc
    rwa [mk_eq_zero]
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hp _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) ≤ 2 := by
      calc
      _ ≤ #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 1 + 1 := by rw [Cardinal.mk_singleton]
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc

instance cardinalInter_ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hp : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CardinalInterFilter (Filter.ofCardinalInter l hc hp h_mono) c :=
  ⟨hp⟩

@[simp]
theorem mem_ofCardinalInter {l : Set (Set α)} (hc : 2 < c)
    (hp : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCardinalInter l hc hp h_mono ↔ s ∈ l :=
  Iff.rfl

/-- Construct a filter with cardinal `c` intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCardinalInter`,
this constructor deduces some properties from the cardinal `c` intersection property
which becomes the cardinal `c` union property because we take complements of all sets.

Another small difference from `Filter.ofCardinalInter`
is that this definition takes `p : Set α → Prop` instead of `Set (Set α)`. -/
def ofCardinalUnion (p : Set α → Prop) (hc : 2 < c)
    (hUnion : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hmono : ∀ t, p t → ∀ s ⊆ t, p s) : Filter α := by
  refine .ofCardinalInter {s | p sᶜ} hc (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    apply hUnion _ ?_ (forall_mem_image.2 hSp)
    rwa [Cardinal.mk_image_eq compl_injective]
  · exact hmono _ ht _ (compl_subset_compl.2 hsub)

instance cardinalInter_ofCardinalUnion (p : Set α → Prop) (hc : 2 < c) (h₁ h₂) :
    CardinalInterFilter (Filter.ofCardinalUnion p hc h₁ h₂) c :=
  cardinalInter_ofCardinalInter ..

@[simp]
theorem mem_ofCardinalUnion {p : Set α → Prop} (hc : 2 < c) {hunion hmono s} :
    s ∈ ofCardinalUnion p hc hunion hmono ↔ p sᶜ :=
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
  refine' ⟨fun S hSc hS => _⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (cardinal_bInter_mem hSc).2 htl
  refine' ⟨_, this, _⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CardinalInterFilter l c] (f : α → β) :
    CardinalInterFilter (map f l) c := by
  refine' ⟨fun S hSc hS => _⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (cardinal_bInter_mem hSc).2 hS

/-- Infimum of two `CardinalInterFilter`s is a `CardinalInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance cardinalInterFilter_inf_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊓ l₂) c := by
  refine' ⟨fun S hSc hS => _⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (cardinal_bInter_mem hSc).2 ht
  refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => _)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

instance cardinalInterFilter_inf (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊓ l₂)
    (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_CardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_CardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

/-- Supremum of two `CardinalInterFilter`s is a `CardinalInterFilter`. -/
instance cardinalInterFilter_sup_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊔ l₂) c := by
  refine' ⟨fun S hSc hS => ⟨_, _⟩⟩ <;> refine' (cardinal_sInter_mem hSc).2 fun s hs => _
  exacts [(hS s hs).1, (hS s hs).2]

instance cardinalInterFilter_sup (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] :
    CardinalInterFilter (l₁ ⊔ l₂) (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_CardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_CardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

variable (g : Set (Set α))

/-- `Filter.CardinalGenerateSets c g` is the (sets of the)
greatest `cardinalInterFilter c` containing `g`.-/
inductive CardinalGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CardinalGenerateSets s
  | univ : CardinalGenerateSets univ
  | superset {s t : Set α} : CardinalGenerateSets s → s ⊆ t → CardinalGenerateSets t
  | sInter {S : Set (Set α)} :
    (#S < c) → (∀ s ∈ S, CardinalGenerateSets s) → CardinalGenerateSets (⋂₀ S)

/-- `Filter.cardinalGenerate c g` is the greatest `cardinalInterFilter c` containing `g`.-/
def cardinalGenerate (hc : 2 < c) : Filter α :=
  ofCardinalInter (CardinalGenerateSets g) hc (fun _ => CardinalGenerateSets.sInter) fun _ _ =>
    CardinalGenerateSets.superset

instance (hc : 2 < c) : CardinalInterFilter (cardinalGenerate g hc) c := by
  delta cardinalGenerate; infer_instance

variable {g}

-- Some cardinality related lemmas that I needed
def fin_from_regular (hreg : Cardinal.IsRegular c) (n : ℕ) : n < c:= by
  apply lt_of_lt_of_le (nat_lt_aleph0 n) (Cardinal.IsRegular.aleph0_le hreg)

@[simp]
theorem cardinal_iUnion_iff {hι : #ι < c} {hreg : Cardinal.IsRegular c}  {t : ι → Set α} :
    #(⋃ i, t i) < c ↔ ∀ i, #(t i) < c := by
  constructor
  · exact fun h _ =>  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h
  · intro h
    apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
    apply Cardinal.mul_lt_of_lt (Cardinal.IsRegular.aleph0_le hreg)
    · exact lt_of_le_of_lt Cardinal.mk_range_le hι
    · apply Cardinal.iSup_lt_of_isRegular hreg
      apply lt_of_le_of_lt Cardinal.mk_range_le hι
      simpa

theorem Cardinal.biUnion_iff {s : Set α} {t : ∀ a ∈ s, Set β} {hreg : Cardinal.IsRegular c}
    (hs : #s < c) : #(⋃ a ∈ s, t a ‹_›) < c ↔ ∀ a (ha : a ∈ s), # (t a ha) < c := by
  rw [biUnion_eq_iUnion, cardinal_iUnion_iff, SetCoe.forall']
  · exact hs
  · exact hreg

/-- A set is in the `cardinalInterFilter` generated by `g` if and only if
it contains an intersection of `c` elements of `g`. -/
theorem mem_cardinaleGenerate_iff {s : Set α} {hreg : Cardinal.IsRegular c} :
    s ∈ cardinalGenerate g (fin_from_regular hreg 2) ↔
    ∃ S : Set (Set α), S ⊆ g ∧ (#S < c) ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction' h with s hs s t _ st ih S Sct _ ih
    · refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      norm_num; exact ⟨fin_from_regular hreg 1, subset_rfl⟩
    · exact ⟨∅, by
        refine ⟨empty_subset g, ?_ ⟩
        constructor
        · have : 0 < c := fin_from_regular hreg 0
          rwa [mk_eq_zero]
        · simp
        ⟩
    · refine' Exists.imp (fun S => _) ih
      tauto
    choose T Tg Tct hT using ih
    refine' ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, ?_, _⟩
    · apply (Cardinal.biUnion_iff Sct).2
      · exact Tct
      · exact hreg
    · apply subset_sInter
      intro s H
      exact subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine' mem_of_superset ((cardinal_sInter_mem Sct).mpr _) hS
  intro s H
  exact CardinalGenerateSets.basic (Sg H)

theorem le_cardinalGenerate_iff_of_cardinalInterFilter {f : Filter α} [CardinalInterFilter f c]
    (hc : 2 < c) : f ≤ cardinalGenerate g hc ↔ g ⊆ f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction' hs with s hs s t _ st ih S Sct _ ih
  · exact h hs
  · exact univ_mem
  · exact mem_of_superset ih st
  exact (cardinal_sInter_mem Sct).mpr ih

/-- `cardinalGenerate g hc` is the greatest `cardinalInterFilter c` containing `g`.-/
theorem cardinalGenerate_isGreatest (hc : 2 < c) :
    IsGreatest { f : Filter α | CardinalInterFilter f c ∧ g ⊆ f.sets } (cardinalGenerate g hc) := by
  refine' ⟨⟨inferInstance, fun s => CardinalGenerateSets.basic⟩, _⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_cardinalGenerate_iff_of_cardinalInterFilter _ _ _ fct]

end Filter
