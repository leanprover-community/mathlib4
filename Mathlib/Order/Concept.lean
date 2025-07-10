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

## Tags

concept, formal concept analysis, intent, extend, attribute
-/


open Function OrderDual Set

variable {ι : Sort*} {α β : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Intent and extent -/


/-- The lower polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def lowerPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

@[deprecated (since := "2025-07-10")]
alias intentClosure := lowerPolar

/-- The upper polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def upperPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

@[deprecated (since := "2025-07-10")]
alias extentClosure := upperPolar

variable {r}

theorem subset_lowerPolar_iff_subset_upperPolar :
    t ⊆ lowerPolar r s ↔ s ⊆ upperPolar r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

@[deprecated (since := "2025-07-10")]
alias subset_intentClosure_iff_subset_extentClosure := subset_lowerPolar_iff_subset_upperPolar

variable (r)

theorem gc_lowerPolar_upperPolar :
    GaloisConnection (toDual ∘ lowerPolar r) (upperPolar r ∘ ofDual) := fun _ _ =>
  subset_lowerPolar_iff_subset_upperPolar

@[deprecated (since := "2025-07-10")]
alias gc_intentClosure_extentClosure := gc_lowerPolar_upperPolar

theorem lowerPolar_swap (t : Set β) : lowerPolar (swap r) t = upperPolar r t :=
  rfl

@[deprecated (since := "2025-07-10")]
alias intentClosure_swap := lowerPolar_swap

theorem upperPolar_swap (s : Set α) : upperPolar (swap r) s = lowerPolar r s :=
  rfl

@[deprecated (since := "2025-07-10")]
alias extentClosure_swap := upperPolar_swap

@[simp]
theorem lowerPolar_empty : lowerPolar r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[deprecated (since := "2025-07-10")]
alias intentClosure_empty := lowerPolar_empty

@[simp]
theorem upperPolar_empty : upperPolar r ∅ = univ :=
  lowerPolar_empty _

@[deprecated (since := "2025-07-10")]
alias extentClosure_empty := upperPolar_empty

@[simp]
theorem lowerPolar_union (s₁ s₂ : Set α) :
    lowerPolar r (s₁ ∪ s₂) = lowerPolar r s₁ ∩ lowerPolar r s₂ :=
  ext fun _ => forall₂_or_left

@[deprecated (since := "2025-07-10")]
alias intentClosure_union := lowerPolar_union

@[simp]
theorem upperPolar_union (t₁ t₂ : Set β) :
    upperPolar r (t₁ ∪ t₂) = upperPolar r t₁ ∩ upperPolar r t₂ :=
  lowerPolar_union ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_union := upperPolar_union

@[simp]
theorem lowerPolar_iUnion (f : ι → Set α) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  (gc_lowerPolar_upperPolar r).l_iSup

@[deprecated (since := "2025-07-10")]
alias intentClosure_iUnion := lowerPolar_iUnion

@[simp]
theorem upperPolar_iUnion (f : ι → Set β) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  lowerPolar_iUnion ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_iUnion := upperPolar_iUnion

theorem lowerPolar_iUnion₂ (f : ∀ i, κ i → Set α) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  (gc_lowerPolar_upperPolar r).l_iSup₂

@[deprecated (since := "2025-07-10")]
alias intentClosure_iUnion₂ := lowerPolar_iUnion₂

theorem upperPolar_iUnion₂ (f : ∀ i, κ i → Set β) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  lowerPolar_iUnion₂ ..

@[deprecated (since := "2025-07-10")]
alias extentClosure_iUnion₂ := upperPolar_iUnion₂

theorem subset_upperPolar_lowerPolar (s : Set α) :
    s ⊆ upperPolar r (lowerPolar r s) :=
  (gc_lowerPolar_upperPolar r).le_u_l _

@[deprecated (since := "2025-07-10")]
alias subset_extentClosure_intentClosure := subset_upperPolar_lowerPolar

theorem subset_lowerPolar_upperPolar (t : Set β) :
    t ⊆ lowerPolar r (upperPolar r t) :=
  subset_upperPolar_lowerPolar _ t

@[deprecated (since := "2025-07-10")]
alias subset_intentClosure_extentClosure := subset_lowerPolar_upperPolar

@[simp]
theorem lowerPolar_upperPolar_lowerPolar (s : Set α) :
    lowerPolar r (upperPolar r <| lowerPolar r s) = lowerPolar r s :=
  (gc_lowerPolar_upperPolar r).l_u_l_eq_l _

@[deprecated (since := "2025-07-10")]
alias intentClosure_extentClosure_intentClosure := lowerPolar_swap

@[simp]
theorem upperPolar_lowerPolar_upperPolar (t : Set β) :
    upperPolar r (lowerPolar r <| upperPolar r t) = upperPolar r t :=
  lowerPolar_upperPolar_lowerPolar _ t

@[deprecated (since := "2025-07-10")]
alias extentClosure_intentClosure_extentClosure := upperPolar_lowerPolar_upperPolar

theorem lowerPolar_anti : Antitone (lowerPolar r) :=
  (gc_lowerPolar_upperPolar r).monotone_l

@[deprecated (since := "2025-07-10")]
alias intentClosure_anti := lowerPolar_anti

theorem upperPolar_anti : Antitone (upperPolar r) :=
  lowerPolar_anti _

@[deprecated (since := "2025-07-10")]
alias extentClosure_anti := upperPolar_anti

/-! ### Concepts -/


variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept extends Set α × Set β where
  /-- The axiom of a `Concept` stating that the lower polar of the first set is the second set. -/
  lowerPolar_fst : lowerPolar r fst = snd
  /-- The axiom of a `Concept` stating that the upper polar of the second set is the first set. -/
  upperPolar_snd : upperPolar r snd = fst

initialize_simps_projections Concept (+toProd, -fst, -snd)

namespace Concept

@[deprecated (since := "2025-07-10")]
alias closure_fst := lowerPolar_fst

@[deprecated (since := "2025-07-10")]
alias closure_snd := upperPolar_snd

variable {r α β}
variable {c d : Concept α β r}

attribute [simp] lowerPolar_fst upperPolar_snd

@[ext]
theorem ext (h : c.fst = d.fst) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, h₁, _⟩ := c
  obtain ⟨⟨s₂, t₂⟩, h₂, _⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl

theorem ext' (h : c.snd = d.snd) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, _, h₁⟩ := c
  obtain ⟨⟨s₂, t₂⟩, _, h₂⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl

theorem fst_injective : Injective fun c : Concept α β r => c.fst := fun _ _ => ext

theorem snd_injective : Injective fun c : Concept α β r => c.snd := fun _ _ => ext'

instance instSupConcept : Max (Concept α β r) :=
  ⟨fun c d =>
    { fst := upperPolar r (c.snd ∩ d.snd)
      snd := c.snd ∩ d.snd
      lowerPolar_fst := by
        rw [← c.lowerPolar_fst, ← d.lowerPolar_fst, ← lowerPolar_union,
          lowerPolar_upperPolar_lowerPolar]
      upperPolar_snd := rfl }⟩

instance instInfConcept : Min (Concept α β r) :=
  ⟨fun c d =>
    { fst := c.fst ∩ d.fst
      snd := lowerPolar r (c.fst ∩ d.fst)
      lowerPolar_fst := rfl
      upperPolar_snd := by
        rw [← c.upperPolar_snd, ← d.upperPolar_snd, ← upperPolar_union,
          upperPolar_lowerPolar_upperPolar] }⟩

instance instSemilatticeInfConcept : SemilatticeInf (Concept α β r) :=
  (fst_injective.semilatticeInf _) fun _ _ => rfl

@[simp]
theorem fst_subset_fst_iff : c.fst ⊆ d.fst ↔ c ≤ d :=
  Iff.rfl

@[simp]
theorem fst_ssubset_fst_iff : c.fst ⊂ d.fst ↔ c < d :=
  Iff.rfl

@[simp]
theorem snd_subset_snd_iff : c.snd ⊆ d.snd ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fst_subset_fst_iff, ← c.upperPolar_snd, ← d.upperPolar_snd]
    exact upperPolar_anti _ h
  · rw [← c.lowerPolar_fst, ← d.lowerPolar_fst]
    exact lowerPolar_anti _ h

@[simp]
theorem snd_ssubset_snd_iff : c.snd ⊂ d.snd ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_ge, snd_subset_snd_iff, snd_subset_snd_iff]

theorem strictMono_fst : StrictMono (Prod.fst ∘ toProd : Concept α β r → Set α) := fun _ _ =>
  fst_ssubset_fst_iff.2

theorem strictAnti_snd : StrictAnti (Prod.snd ∘ toProd : Concept α β r → Set β) := fun _ _ =>
  snd_ssubset_snd_iff.2

instance instLatticeConcept : Lattice (Concept α β r) :=
  { Concept.instSemilatticeInfConcept with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => snd_subset_snd_iff.1 inter_subset_left
    le_sup_right := fun _ _ => snd_subset_snd_iff.1 inter_subset_right
    sup_le := fun c d e => by
      simp_rw [← snd_subset_snd_iff]
      exact subset_inter }

instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ⟨⟨univ, lowerPolar r univ⟩, rfl, eq_univ_of_forall fun _ _ hb => hb trivial⟩
  le_top _ := subset_univ _
  bot := ⟨⟨upperPolar r univ, univ⟩, eq_univ_of_forall fun _ _ ha => ha trivial, rfl⟩
  bot_le _ := snd_subset_snd_iff.1 <| subset_univ _

instance : SupSet (Concept α β r) :=
  ⟨fun S =>
    { fst := upperPolar r (⋂ c ∈ S, (c : Concept _ _ _).snd)
      snd := ⋂ c ∈ S, (c : Concept _ _ _).snd
      lowerPolar_fst := by
        simp_rw [← lowerPolar_fst, ← lowerPolar_iUnion₂, lowerPolar_upperPolar_lowerPolar]
      upperPolar_snd := rfl }⟩

instance : InfSet (Concept α β r) :=
  ⟨fun S =>
    { fst := ⋂ c ∈ S, (c : Concept _ _ _).fst
      snd := lowerPolar r (⋂ c ∈ S, (c : Concept _ _ _).fst)
      lowerPolar_fst := rfl
      upperPolar_snd := by
        simp_rw [← upperPolar_snd, ← upperPolar_iUnion₂, upperPolar_lowerPolar_upperPolar] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.instLatticeConcept,
    Concept.instBoundedOrderConcept with
    sup := Concept.instSupConcept.max
    le_sSup := fun _ _ hc => snd_subset_snd_iff.1 <| biInter_subset_of_mem hc
    sSup_le := fun _ _ hc =>
      snd_subset_snd_iff.1 <| subset_iInter₂ fun d hd => snd_subset_snd_iff.2 <| hc d hd
    inf := Concept.instInfConcept.min
    sInf_le := fun _ _ => biInter_subset_of_mem
    le_sInf := fun _ _ => subset_iInter₂ }

@[simp]
theorem top_fst : (⊤ : Concept α β r).fst = univ :=
  rfl

@[simp]
theorem top_snd : (⊤ : Concept α β r).snd = lowerPolar r univ :=
  rfl

@[simp]
theorem bot_fst : (⊥ : Concept α β r).fst = upperPolar r univ :=
  rfl

@[simp]
theorem bot_snd : (⊥ : Concept α β r).snd = univ :=
  rfl

@[simp]
theorem sup_fst (c d : Concept α β r) : (c ⊔ d).fst = upperPolar r (c.snd ∩ d.snd) :=
  rfl

@[simp]
theorem sup_snd (c d : Concept α β r) : (c ⊔ d).snd = c.snd ∩ d.snd :=
  rfl

@[simp]
theorem inf_fst (c d : Concept α β r) : (c ⊓ d).fst = c.fst ∩ d.fst :=
  rfl

@[simp]
theorem inf_snd (c d : Concept α β r) : (c ⊓ d).snd = lowerPolar r (c.fst ∩ d.fst) :=
  rfl

@[simp]
theorem sSup_fst (S : Set (Concept α β r)) :
    (sSup S).fst = upperPolar r (⋂ c ∈ S, (c : Concept _ _ _).snd) :=
  rfl

@[simp]
theorem sSup_snd (S : Set (Concept α β r)) : (sSup S).snd = ⋂ c ∈ S, (c : Concept _ _ _).snd :=
  rfl

@[simp]
theorem sInf_fst (S : Set (Concept α β r)) : (sInf S).fst = ⋂ c ∈ S, (c : Concept _ _ _).fst :=
  rfl

@[simp]
theorem sInf_snd (S : Set (Concept α β r)) :
    (sInf S).snd = lowerPolar r (⋂ c ∈ S, (c : Concept _ _ _).fst) :=
  rfl

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.toProd.swap, c.upperPolar_snd, c.lowerPolar_fst⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  snd_subset_snd_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  snd_ssubset_snd_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
