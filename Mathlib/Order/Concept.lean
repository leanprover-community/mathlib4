/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Wrenna Robson, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Set.Lattice

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## TODO

Prove the fundamental theorem of concept lattices.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
* [Birkhoff, Garrett *Lattice Theory*][birkhoff1940]

## Tags

concept, formal concept analysis, intent, extend, attribute
-/

@[expose] public section


open Function OrderDual Order Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Lower and upper polars -/

/-- The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

@[deprecated (since := "2025-07-10")]
alias intentClosure := upperPolar

/-- The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

@[deprecated (since := "2025-07-10")]
alias extentClosure := lowerPolar

variable {r} {a : α} {b : β}

theorem mem_upperPolar_iff : b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b := .rfl
theorem mem_lowerPolar_iff : a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b := .rfl

theorem subset_upperPolar_iff_subset_lowerPolar :
    t ⊆ upperPolar r s ↔ s ⊆ lowerPolar r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

@[deprecated (since := "2025-07-10")]
alias subset_intentClosure_iff_subset_extentClosure := subset_upperPolar_iff_subset_lowerPolar

variable (r)

theorem gc_upperPolar_lowerPolar :
    GaloisConnection (toDual ∘ upperPolar r) (lowerPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

@[deprecated (since := "2025-07-10")]
alias gc_intentClosure_extentClosure := gc_upperPolar_lowerPolar

theorem upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t :=
  rfl

@[deprecated (since := "2025-07-10")]
alias intentClosure_swap := upperPolar_swap

theorem lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s :=
  rfl

@[deprecated (since := "2025-07-10")]
alias extentClosure_swap := lowerPolar_swap

@[simp]
theorem upperPolar_empty : upperPolar r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[deprecated (since := "2025-07-10")]
alias intentClosure_empty := upperPolar_empty

@[simp]
theorem lowerPolar_empty : lowerPolar r ∅ = univ :=
  upperPolar_empty _

@[deprecated (since := "2025-07-10")]
alias extentClosure_empty := lowerPolar_empty

@[simp]
theorem mem_upperPolar_singleton_iff : b ∈ upperPolar r {a} ↔ r a b := by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
theorem mem_lowerPolar_singleton_iff : a ∈ lowerPolar r {b} ↔ r a b := by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
theorem upperPolar_union (s₁ s₂ : Set α) :
    upperPolar r (s₁ ∪ s₂) = upperPolar r s₁ ∩ upperPolar r s₂ :=
  ext fun _ => forall₂_or_left

@[deprecated (since := "2025-07-10")]
alias intentClosure_union := upperPolar_union

@[simp]
theorem lowerPolar_union (t₁ t₂ : Set β) :
    lowerPolar r (t₁ ∪ t₂) = lowerPolar r t₁ ∩ lowerPolar r t₂ :=
  upperPolar_union ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_union := lowerPolar_union

@[simp]
theorem upperPolar_iUnion (f : ι → Set α) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).l_iSup

@[deprecated (since := "2025-07-10")]
alias intentClosure_iUnion := upperPolar_iUnion

@[simp]
theorem lowerPolar_iUnion (f : ι → Set β) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  upperPolar_iUnion ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_iUnion := lowerPolar_iUnion

theorem upperPolar_iUnion₂ (f : ∀ i, κ i → Set α) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).l_iSup₂

@[deprecated (since := "2025-07-10")]
alias intentClosure_iUnion₂ := upperPolar_iUnion₂

theorem lowerPolar_iUnion₂ (f : ∀ i, κ i → Set β) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  upperPolar_iUnion₂ ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_iUnion₂ := lowerPolar_iUnion₂

theorem subset_lowerPolar_upperPolar (s : Set α) :
    s ⊆ lowerPolar r (upperPolar r s) :=
  (gc_upperPolar_lowerPolar r).le_u_l _

@[deprecated (since := "2025-07-10")]
alias subset_extentClosure_intentClosure := subset_lowerPolar_upperPolar

theorem subset_upperPolar_lowerPolar (t : Set β) :
    t ⊆ upperPolar r (lowerPolar r t) :=
  subset_lowerPolar_upperPolar _ t

@[deprecated (since := "2025-07-10")]
alias subset_intentClosure_extentClosure := subset_upperPolar_lowerPolar

@[simp]
theorem upperPolar_lowerPolar_upperPolar (s : Set α) :
    upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s :=
  (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[deprecated (since := "2025-07-10")]
alias intentClosure_extentClosure_intentClosure := upperPolar_lowerPolar_upperPolar

@[simp]
theorem lowerPolar_upperPolar_lowerPolar (t : Set β) :
    lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t :=
  upperPolar_lowerPolar_upperPolar _ t

@[deprecated (since := "2025-07-10")]
alias extentClosure_intentClosure_extentClosure := lowerPolar_upperPolar_lowerPolar

theorem upperPolar_anti : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l

@[deprecated (since := "2025-07-10")]
alias intentClosure_anti := upperPolar_anti

theorem lowerPolar_anti : Antitone (lowerPolar r) :=
  upperPolar_anti _

@[deprecated (since := "2025-07-10")]
alias extentClosure_anti := lowerPolar_anti

/-! ### `IsIntent` and `IsExtent` -/

namespace Order

variable {r}

/-- A set is an extent when either of the following equivalent definitions holds:

- The `lowerPolar` of its `upperPolar` is itself.
- The set is the `lowerPolar` of some other set. -/
def IsExtent (r : α → β → Prop) (s : Set α) := lowerPolar r (upperPolar r s) = s

theorem IsExtent.eq (h : IsExtent r s) : lowerPolar r (upperPolar r s) = s := h

theorem isExtent_iff : IsExtent r s ↔ ∃ t, lowerPolar r t = s :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨t, h⟩ ↦ h ▸ lowerPolar_upperPolar_lowerPolar r t⟩

theorem isExtent_lowerPolar (t : Set β) : IsExtent r (lowerPolar r t) :=
  isExtent_iff.2 ⟨_, rfl⟩

@[simp] theorem isExtent_univ : IsExtent r univ := (gc_upperPolar_lowerPolar r).u_l_top

protected theorem IsExtent.inter {s' : Set α} :
    IsExtent r s → IsExtent r s' → IsExtent r (s ∩ s') := by
  simp_rw [isExtent_iff, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩

protected theorem IsExtent.iInter (f : ι → Set α) (hf : ∀ i, IsExtent r (f i)) :
    IsExtent r (⋂ i, f i) := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr hf)⟩

protected theorem IsExtent.iInter₂ (f : ∀ i, κ i → Set α) (hf : ∀ i j, IsExtent r (f i j)) :
    IsExtent r (⋂ (i) (j), f i j) := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr hf)⟩

/-- A set is an intent when either of the following equivalent definitions holds:

- The `upperPolar` of its `lowerPolar` is itself.
- The set is the `upperPolar` of some other set. -/
def IsIntent (r : α → β → Prop) (t : Set β) := upperPolar r (lowerPolar r t) = t

theorem IsIntent.eq (h : IsIntent r t) : upperPolar r (lowerPolar r t) = t := h

theorem isIntent_iff : IsIntent r t ↔ ∃ s, upperPolar r s = t := isExtent_iff

theorem isIntent_upperPolar (s : Set α) : IsIntent r (upperPolar r s) := isExtent_lowerPolar _

@[simp] theorem isIntent_univ : IsIntent r univ := isExtent_univ

protected theorem IsIntent.inter {t' : Set β} :
    IsIntent r t → IsIntent r t' → IsIntent r (t ∩ t') :=
  IsExtent.inter

protected theorem IsIntent.iInter (f : ι → Set β) (hf : ∀ i, IsIntent r (f i)) :
    IsIntent r (⋂ i, f i) :=
  IsExtent.iInter _ hf

protected theorem IsIntent.iInter₂ (f : ∀ i, κ i → Set β) (hf : ∀ i j, IsIntent r (f i j)) :
    IsIntent r (⋂ (i) (j), f i j) :=
  IsExtent.iInter₂ _ hf

end Order

/-! ### Concepts -/

variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept where
  /-- The extent of a concept. -/
  extent : Set α
  /-- The intent of a concept. -/
  intent : Set β
  /-- The intent consists of all elements related to all elements of the extent. -/
  upperPolar_extent : upperPolar r extent = intent
  /-- The extent consists of all elements related to all elements of the intent. -/
  lowerPolar_intent : lowerPolar r intent = extent

namespace Concept

@[deprecated (since := "2025-07-10")]
alias fst := extent

@[deprecated (since := "2025-07-10")]
alias snd := intent

@[deprecated (since := "2025-07-10")]
alias closure_fst := upperPolar_extent

@[deprecated (since := "2025-07-10")]
alias closure_snd := lowerPolar_intent

variable {r r' α β}
variable {c d : Concept α β r} {c' : Concept α α r'}

attribute [simp] upperPolar_extent lowerPolar_intent

/-- See `Concept.ext'` for a version using the intent. -/
@[ext]
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  substs h
  rfl

/-- See `Concept.ext` for a version using the extent. -/
theorem ext' (h : c.intent = d.intent) : c = d := by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  substs h
  rfl

theorem extent_injective : Injective (@extent α β r) := fun _ _ => ext

@[deprecated (since := "2025-07-10")]
alias fst_injective := extent_injective

theorem intent_injective : Injective (@intent α β r) := fun _ _ => ext'

@[deprecated (since := "2025-07-10")]
alias snd_injective := intent_injective

/-- Copy a concept, adjusting definitional equalities. -/
@[simps!]
def copy (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent) :
    Concept α β r := ⟨e, i, he ▸ hi ▸ c.upperPolar_extent, he ▸ hi ▸ c.lowerPolar_intent⟩

theorem copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he hi) : c.copy e i he hi = c := by
  ext; simp_all

/-- Define a concept from an extent, by setting the intent to its upper polar. -/
@[simps!]
def _root_.Order.IsExtent.concept (hs : IsExtent r s) : Concept α β r :=
  ⟨s, upperPolar r s, rfl, hs⟩

theorem isExtent_extent (c : Concept α β r) : IsExtent r c.extent :=
  lowerPolar_intent c ▸ isExtent_lowerPolar c.intent

theorem isExtent_iff_exists_concept : IsExtent r s ↔ ∃ c : Concept α β r, c.extent = s :=
  ⟨fun h ↦ ⟨h.concept, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isExtent_extent⟩

/-- Define a concept from an intent, by setting the extent to its lower polar. -/
@[simps!]
def _root_.Order.IsIntent.concept (ht : IsIntent r t) : Concept α β r :=
  ⟨lowerPolar r t, t, ht, rfl⟩

theorem isIntent_intent (c : Concept α β r) : IsIntent r c.intent :=
  upperPolar_extent c ▸ isIntent_upperPolar c.extent

theorem isIntent_iff_exists_concept : IsIntent r t ↔ ∃ c : Concept α β r, c.intent = t :=
  ⟨fun h ↦ ⟨h.concept, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isIntent_intent⟩

theorem rel_extent_intent {x y} (hx : x ∈ c.extent) (hy : y ∈ c.intent) : r x y := by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

/-- Note that if `r'` is the `≤` relation, this theorem will often not be true! -/
theorem disjoint_extent_intent [Std.Irrefl r'] : Disjoint c'.extent c'.intent := by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')

theorem mem_extent_of_rel_extent [IsTrans α r'] {x y} (hy : r' y x) (hx : x ∈ c'.extent) :
    y ∈ c'.extent := by
  rw [← lowerPolar_intent]
  exact fun z hz ↦ _root_.trans hy (rel_extent_intent hx hz)

theorem mem_intent_of_intent_rel [IsTrans α r'] {x y} (hy : r' x y) (hx : x ∈ c'.intent) :
    y ∈ c'.intent := by
  rw [← upperPolar_extent]
  exact fun z hz ↦ _root_.trans (rel_extent_intent hz hx) hy

theorem codisjoint_extent_intent [IsTrichotomous α r'] [IsTrans α r'] :
    Codisjoint c'.extent c'.intent := by
  rw [codisjoint_iff_le_sup]
  refine fun x _ ↦ or_iff_not_imp_left.2 fun hx ↦ ?_
  rw [← upperPolar_extent]
  intro y hy
  obtain h | rfl | h := trichotomous_of r' x y
  · cases hx <| mem_extent_of_rel_extent h hy
  · contradiction
  · assumption

instance : PartialOrder (Concept α β r) :=
  PartialOrder.lift _ extent_injective

theorem isCompl_extent_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') :
    IsCompl c'.extent c'.intent :=
  ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]
theorem compl_extent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.extentᶜ = c'.intent :=
  c'.isCompl_extent_intent.compl_eq

@[simp]
theorem compl_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.intentᶜ = c'.extent :=
  c'.isCompl_extent_intent.symm.compl_eq

@[simp]
theorem extent_subset_extent_iff : c.extent ⊆ d.extent ↔ c ≤ d :=
  Iff.rfl

@[deprecated (since := "2025-07-10")]
alias fst_subset_fst_iff := extent_subset_extent_iff

@[simp]
theorem extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d :=
  Iff.rfl

@[deprecated (since := "2025-07-10")]
alias fst_ssubset_fst_iff := extent_ssubset_extent_iff

@[simp]
theorem intent_subset_intent_iff : c.intent ⊆ d.intent ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[deprecated (since := "2025-07-10")]
alias snd_subset_snd_iff := intent_subset_intent_iff

@[simp]
theorem intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_ge,
    intent_subset_intent_iff, intent_subset_intent_iff]

@[deprecated (since := "2025-07-10")]
alias snd_ssubset_snd_iff := intent_ssubset_intent_iff

theorem strictMono_extent : StrictMono (@extent α β r) := fun _ _ =>
  extent_ssubset_extent_iff.2

@[deprecated (since := "2025-07-10")]
alias strictMono_fst := strictMono_extent

theorem strictAnti_intent : StrictAnti (@intent α β r) := fun _ _ =>
  intent_ssubset_intent_iff.2

@[deprecated (since := "2025-07-10")]
alias strictMono_snd := strictAnti_intent

@[simps!]
instance : Max (Concept α β r) where
  max c d := (c.isIntent_intent.inter d.isIntent_intent).concept

alias sup_extent := max_extent
alias sup_intent := max_intent

@[simps!]
instance : Min (Concept α β r) where
  min c d := (c.isExtent_extent.inter d.isExtent_extent).concept

alias inf_extent := min_extent
alias inf_intent := min_intent

instance : SemilatticeInf (Concept α β r) :=
  extent_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

instance : SemilatticeSup (Concept α β r) :=
  show SemilatticeSup (Concept α β r)ᵒᵈ from
    (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ ↦ rfl

instance : Lattice (Concept α β r) where

@[simps!]
instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := isExtent_univ.concept
  le_top _ := subset_univ _
  bot := isIntent_univ.concept
  bot_le _ := intent_subset_intent_iff.1 <| subset_univ _

@[simps!]
instance : InfSet (Concept α β r) where
  sInf S := (IsExtent.iInter₂ _ fun c (_ : c ∈ S) => c.isExtent_extent).concept

@[simps!]
instance : SupSet (Concept α β r) where
  sSup S := (IsIntent.iInter₂ _ fun c (_ : c ∈ S) => c.isIntent_intent).concept

instance : CompleteLattice (Concept α β r) where
  le_sSup _ _ hc := intent_subset_intent_iff.1 <| biInter_subset_of_mem hc
  sSup_le _ _ hc := intent_subset_intent_iff.1 <|
    subset_iInter₂ (intent_subset_intent_iff.2 <| hc · ·)
  sInf_le _ _ := biInter_subset_of_mem
  le_sInf _ _ := subset_iInter₂

@[deprecated (since := "2025-09-26")]
alias extent_top := top_extent

@[deprecated (since := "2025-07-10")]
alias top_fst := extent_top

@[deprecated (since := "2025-09-26")]
alias intent_top := top_intent

@[deprecated (since := "2025-07-10")]
alias top_snd := intent_top

@[deprecated (since := "2025-09-26")]
alias extent_bot := bot_extent

@[deprecated (since := "2025-07-10")]
alias bot_fst := extent_bot

@[deprecated (since := "2025-09-26")]
alias intent_bot := bot_intent

@[deprecated (since := "2025-07-10")]
alias bot_snd := intent_bot

@[deprecated (since := "2025-09-26")]
alias extent_sup := sup_extent

@[deprecated (since := "2025-07-10")]
alias sup_fst := extent_top

@[deprecated (since := "2025-09-26")]
alias intent_sup := sup_intent

@[deprecated (since := "2025-07-10")]
alias sup_snd := intent_sup

@[deprecated (since := "2025-09-26")]
alias extent_inf := inf_extent

@[deprecated (since := "2025-07-10")]
alias inf_fst := extent_inf

@[deprecated (since := "2025-09-26")]
alias intent_inf := inf_intent

@[deprecated (since := "2025-07-10")]
alias inf_snd := intent_inf

@[deprecated (since := "2025-09-26")]
alias extent_sSup := sSup_extent

@[deprecated (since := "2025-07-10")]
alias sSup_fst := extent_sSup

@[deprecated (since := "2025-09-26")]
alias intent_sSup := sSup_intent

@[deprecated (since := "2025-07-10")]
alias sSup_snd := intent_sSup

@[deprecated (since := "2025-09-26")]
alias extent_sInf := sInf_extent

@[deprecated (since := "2025-07-10")]
alias sInf_fst := extent_sInf

@[deprecated (since := "2025-09-26")]
alias intent_sInf := sInf_intent

@[deprecated (since := "2025-07-10")]
alias sInf_snd := intent_sInf

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  intent_subset_intent_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  intent_ssubset_intent_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
