/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Lattice

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


open Function OrderDual Set

variable {ι : Sort*} {α β : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

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

variable {r}

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

@[ext]
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  substs h
  rfl

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

theorem rel_extent_intent {x y} (hx : x ∈ c.extent) (hy : y ∈ c.intent) : r x y := by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

/-- Note that if `r'` is the `≤` relation, this theorem will often not be true! -/
theorem disjoint_extent_intent [IsIrrefl α r'] : Disjoint c'.extent c'.intent := by
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

instance instSupConcept : Max (Concept α β r) :=
  ⟨fun c d =>
    { extent := lowerPolar r (c.intent ∩ d.intent)
      intent := c.intent ∩ d.intent
      upperPolar_extent := by
        rw [← c.upperPolar_extent, ← d.upperPolar_extent, ← upperPolar_union,
          upperPolar_lowerPolar_upperPolar]
      lowerPolar_intent := rfl }⟩

instance instInfConcept : Min (Concept α β r) :=
  ⟨fun c d =>
    { extent := c.extent ∩ d.extent
      intent := upperPolar r (c.extent ∩ d.extent)
      upperPolar_extent := rfl
      lowerPolar_intent := by
        rw [← c.lowerPolar_intent, ← d.lowerPolar_intent, ← lowerPolar_union,
          lowerPolar_upperPolar_lowerPolar] }⟩

instance instSemilatticeInfConcept : PartialOrder (Concept α β r) :=
  PartialOrder.lift _ extent_injective

instance instSemilatticeInfConcept : SemilatticeInf (Concept α β r) :=
  extent_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

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

instance instLatticeConcept : Lattice (Concept α β r) :=
  { Concept.instSemilatticeInfConcept with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => intent_subset_intent_iff.1 inter_subset_left
    le_sup_right := fun _ _ => intent_subset_intent_iff.1 inter_subset_right
    sup_le := fun c d e => by
      simp_rw [← intent_subset_intent_iff]
      exact subset_inter }

instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ⟨univ, upperPolar r univ, rfl, eq_univ_of_forall fun _ _ hb => hb trivial⟩
  le_top _ := subset_univ _
  bot := ⟨lowerPolar r univ, univ, eq_univ_of_forall fun _ _ ha => ha trivial, rfl⟩
  bot_le _ := intent_subset_intent_iff.1 <| subset_univ _

instance : SupSet (Concept α β r) :=
  ⟨fun S =>
    { extent := lowerPolar r (⋂ c ∈ S, intent c)
      intent := ⋂ c ∈ S, intent c
      upperPolar_extent := by
        simp_rw [← upperPolar_extent, ← upperPolar_iUnion₂, upperPolar_lowerPolar_upperPolar]
      lowerPolar_intent := rfl }⟩

instance : InfSet (Concept α β r) :=
  ⟨fun S =>
    { extent := ⋂ c ∈ S, extent c
      intent := upperPolar r (⋂ c ∈ S, extent c)
      upperPolar_extent := rfl
      lowerPolar_intent := by
        simp_rw [← lowerPolar_intent, ← lowerPolar_iUnion₂, lowerPolar_upperPolar_lowerPolar] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.instLatticeConcept,
    Concept.instBoundedOrderConcept with
    sup := Concept.instSupConcept.max
    le_sSup := fun _ _ hc => intent_subset_intent_iff.1 <| biInter_subset_of_mem hc
    sSup_le := fun _ _ hc =>
      intent_subset_intent_iff.1 <| subset_iInter₂ fun d hd => intent_subset_intent_iff.2 <| hc d hd
    inf := Concept.instInfConcept.min
    sInf_le := fun _ _ => biInter_subset_of_mem
    le_sInf := fun _ _ => subset_iInter₂ }

@[simp]
theorem extent_top : (⊤ : Concept α β r).extent = univ :=
  rfl

@[deprecated (since := "2025-07-10")]
alias top_fst := extent_top

@[simp]
theorem intent_top : (⊤ : Concept α β r).intent = upperPolar r univ :=
  rfl

@[deprecated (since := "2025-07-10")]
alias top_snd := intent_top

@[simp]
theorem extent_bot : (⊥ : Concept α β r).extent = lowerPolar r univ :=
  rfl

@[deprecated (since := "2025-07-10")]
alias bot_fst := extent_bot

@[simp]
theorem intent_bot : (⊥ : Concept α β r).intent = univ :=
  rfl

@[deprecated (since := "2025-07-10")]
alias bot_snd := intent_bot

@[simp]
theorem extent_sup (c d : Concept α β r) : (c ⊔ d).extent = lowerPolar r (c.intent ∩ d.intent) :=
  rfl

@[deprecated (since := "2025-07-10")]
alias sup_fst := extent_top

@[simp]
theorem intent_sup (c d : Concept α β r) : (c ⊔ d).intent = c.intent ∩ d.intent :=
  rfl

@[deprecated (since := "2025-07-10")]
alias sup_snd := intent_sup

@[simp]
theorem extent_inf (c d : Concept α β r) : (c ⊓ d).extent = c.extent ∩ d.extent :=
  rfl

@[deprecated (since := "2025-07-10")]
alias inf_fst := extent_inf

@[simp]
theorem intent_inf (c d : Concept α β r) : (c ⊓ d).intent = upperPolar r (c.extent ∩ d.extent) :=
  rfl

@[deprecated (since := "2025-07-10")]
alias inf_snd := intent_inf

@[simp]
theorem extent_sSup (S : Set (Concept α β r)) :
    (sSup S).extent = lowerPolar r (⋂ c ∈ S, intent c) :=
  rfl

@[deprecated (since := "2025-07-10")]
alias sSup_fst := extent_sSup

@[simp]
theorem intent_sSup (S : Set (Concept α β r)) : (sSup S).intent = ⋂ c ∈ S, intent c :=
  rfl

@[deprecated (since := "2025-07-10")]
alias sSup_snd := intent_sSup

@[simp]
theorem extent_sInf (S : Set (Concept α β r)) : (sInf S).extent = ⋂ c ∈ S, extent c :=
  rfl

@[deprecated (since := "2025-07-10")]
alias sInf_fst := extent_sInf

@[simp]
theorem intent_sInf (S : Set (Concept α β r)) :
    (sInf S).intent = upperPolar r (⋂ c ∈ S, extent c) :=
  rfl

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
