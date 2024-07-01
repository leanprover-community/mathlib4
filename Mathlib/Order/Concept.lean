/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Lattice

#align_import order.concept from "leanprover-community/mathlib"@"1e05171a5e8cf18d98d9cf7b207540acb044acae"

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

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s s₁ s₂ : Set α}
  {t t₁ t₂ : Set β}

/-! ### Intent and extent -/


/-- The intent closure of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def intentClosure (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }
#align intent_closure intentClosure

/-- The extent closure of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def extentClosure (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }
#align extent_closure extentClosure

variable {r}

theorem subset_intentClosure_iff_subset_extentClosure :
    t ⊆ intentClosure r s ↔ s ⊆ extentClosure r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩
#align subset_intent_closure_iff_subset_extent_closure subset_intentClosure_iff_subset_extentClosure

variable (r)

theorem gc_intentClosure_extentClosure :
    GaloisConnection (toDual ∘ intentClosure r) (extentClosure r ∘ ofDual) := fun _ _ =>
  subset_intentClosure_iff_subset_extentClosure
#align gc_intent_closure_extent_closure gc_intentClosure_extentClosure

theorem intentClosure_swap (t : Set β) : intentClosure (swap r) t = extentClosure r t :=
  rfl
#align intent_closure_swap intentClosure_swap

theorem extentClosure_swap (s : Set α) : extentClosure (swap r) s = intentClosure r s :=
  rfl
#align extent_closure_swap extentClosure_swap

@[simp]
theorem intentClosure_empty : intentClosure r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim
#align intent_closure_empty intentClosure_empty

@[simp]
theorem extentClosure_empty : extentClosure r ∅ = univ :=
  intentClosure_empty _
#align extent_closure_empty extentClosure_empty

@[simp]
theorem intentClosure_union (s₁ s₂ : Set α) :
    intentClosure r (s₁ ∪ s₂) = intentClosure r s₁ ∩ intentClosure r s₂ :=
  Set.ext fun _ => forall₂_or_left
#align intent_closure_union intentClosure_union

@[simp]
theorem extentClosure_union (t₁ t₂ : Set β) :
    extentClosure r (t₁ ∪ t₂) = extentClosure r t₁ ∩ extentClosure r t₂ :=
  intentClosure_union _ _ _
#align extent_closure_union extentClosure_union

@[simp]
theorem intentClosure_iUnion (f : ι → Set α) :
    intentClosure r (⋃ i, f i) = ⋂ i, intentClosure r (f i) :=
  (gc_intentClosure_extentClosure r).l_iSup
#align intent_closure_Union intentClosure_iUnion

@[simp]
theorem extentClosure_iUnion (f : ι → Set β) :
    extentClosure r (⋃ i, f i) = ⋂ i, extentClosure r (f i) :=
  intentClosure_iUnion _ _
#align extent_closure_Union extentClosure_iUnion

theorem intentClosure_iUnion₂ (f : ∀ i, κ i → Set α) :
    intentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), intentClosure r (f i j) :=
  (gc_intentClosure_extentClosure r).l_iSup₂
#align intent_closure_Union₂ intentClosure_iUnion₂

theorem extentClosure_iUnion₂ (f : ∀ i, κ i → Set β) :
    extentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), extentClosure r (f i j) :=
  intentClosure_iUnion₂ _ _
#align extent_closure_Union₂ extentClosure_iUnion₂

theorem subset_extentClosure_intentClosure (s : Set α) :
    s ⊆ extentClosure r (intentClosure r s) :=
  (gc_intentClosure_extentClosure r).le_u_l _
#align subset_extent_closure_intent_closure subset_extentClosure_intentClosure

theorem subset_intentClosure_extentClosure (t : Set β) :
    t ⊆ intentClosure r (extentClosure r t) :=
  subset_extentClosure_intentClosure _ t
#align subset_intent_closure_extent_closure subset_intentClosure_extentClosure

@[simp]
theorem intentClosure_extentClosure_intentClosure (s : Set α) :
    intentClosure r (extentClosure r <| intentClosure r s) = intentClosure r s :=
  (gc_intentClosure_extentClosure r).l_u_l_eq_l _
#align intent_closure_extent_closure_intent_closure intentClosure_extentClosure_intentClosure

@[simp]
theorem extentClosure_intentClosure_extentClosure (t : Set β) :
    extentClosure r (intentClosure r <| extentClosure r t) = extentClosure r t :=
  intentClosure_extentClosure_intentClosure _ t
#align extent_closure_intent_closure_extent_closure extentClosure_intentClosure_extentClosure

theorem intentClosure_anti : Antitone (intentClosure r) :=
  (gc_intentClosure_extentClosure r).monotone_l
#align intent_closure_anti intentClosure_anti

theorem extentClosure_anti : Antitone (extentClosure r) :=
  intentClosure_anti _
#align extent_closure_anti extentClosure_anti

/-! ### Concepts -/


variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept extends Set α × Set β where
  /-- The axiom of a `Concept` stating that the closure of the first set is the second set. -/
  closure_fst : intentClosure r fst = snd
  /-- The axiom of a `Concept` stating that the closure of the second set is the first set. -/
  closure_snd : extentClosure r snd = fst
#align concept Concept

initialize_simps_projections Concept (+toProd, -fst, -snd)

namespace Concept

variable {r α β}
variable {c d : Concept α β r}

attribute [simp] closure_fst closure_snd

@[ext]
theorem ext (h : c.fst = d.fst) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, h₁, _⟩ := c
  obtain ⟨⟨s₂, t₂⟩, h₂, _⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl
#align concept.ext Concept.ext

theorem ext' (h : c.snd = d.snd) : c = d := by
  obtain ⟨⟨s₁, t₁⟩, _, h₁⟩ := c
  obtain ⟨⟨s₂, t₂⟩, _, h₂⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl
#align concept.ext' Concept.ext'

theorem fst_injective : Injective fun c : Concept α β r => c.fst := fun _ _ => ext
#align concept.fst_injective Concept.fst_injective

theorem snd_injective : Injective fun c : Concept α β r => c.snd := fun _ _ => ext'
#align concept.snd_injective Concept.snd_injective

instance instSupConcept : Sup (Concept α β r) :=
  ⟨fun c d =>
    { fst := extentClosure r (c.snd ∩ d.snd)
      snd := c.snd ∩ d.snd
      closure_fst := by
        rw [← c.closure_fst, ← d.closure_fst, ← intentClosure_union,
          intentClosure_extentClosure_intentClosure]
      closure_snd := rfl }⟩

instance instInfConcept : Inf (Concept α β r) :=
  ⟨fun c d =>
    { fst := c.fst ∩ d.fst
      snd := intentClosure r (c.fst ∩ d.fst)
      closure_fst := rfl
      closure_snd := by
        rw [← c.closure_snd, ← d.closure_snd, ← extentClosure_union,
          extentClosure_intentClosure_extentClosure] }⟩

instance instSemilatticeInfConcept : SemilatticeInf (Concept α β r) :=
  (fst_injective.semilatticeInf _) fun _ _ => rfl

@[simp]
theorem fst_subset_fst_iff : c.fst ⊆ d.fst ↔ c ≤ d :=
  Iff.rfl
#align concept.fst_subset_fst_iff Concept.fst_subset_fst_iff

@[simp]
theorem fst_ssubset_fst_iff : c.fst ⊂ d.fst ↔ c < d :=
  Iff.rfl
#align concept.fst_ssubset_fst_iff Concept.fst_ssubset_fst_iff

@[simp]
theorem snd_subset_snd_iff : c.snd ⊆ d.snd ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fst_subset_fst_iff, ← c.closure_snd, ← d.closure_snd]
    exact extentClosure_anti _ h
  · rw [← c.closure_fst, ← d.closure_fst]
    exact intentClosure_anti _ h
#align concept.snd_subset_snd_iff Concept.snd_subset_snd_iff

@[simp]
theorem snd_ssubset_snd_iff : c.snd ⊂ d.snd ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_le, snd_subset_snd_iff, snd_subset_snd_iff]
#align concept.snd_ssubset_snd_iff Concept.snd_ssubset_snd_iff

theorem strictMono_fst : StrictMono (Prod.fst ∘ toProd : Concept α β r → Set α) := fun _ _ =>
  fst_ssubset_fst_iff.2
#align concept.strict_mono_fst Concept.strictMono_fst

theorem strictAnti_snd : StrictAnti (Prod.snd ∘ toProd : Concept α β r → Set β) := fun _ _ =>
  snd_ssubset_snd_iff.2
#align concept.strict_anti_snd Concept.strictAnti_snd

instance instLatticeConcept : Lattice (Concept α β r) :=
  { Concept.instSemilatticeInfConcept with
    sup := (· ⊔ ·)
    le_sup_left := fun c d => snd_subset_snd_iff.1 inter_subset_left
    le_sup_right := fun c d => snd_subset_snd_iff.1 inter_subset_right
    sup_le := fun c d e => by
      simp_rw [← snd_subset_snd_iff]
      exact subset_inter }

instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ⟨⟨univ, intentClosure r univ⟩, rfl, eq_univ_of_forall fun _ _ hb => hb trivial⟩
  le_top _ := subset_univ _
  bot := ⟨⟨extentClosure r univ, univ⟩, eq_univ_of_forall fun _ _ ha => ha trivial, rfl⟩
  bot_le _ := snd_subset_snd_iff.1 <| subset_univ _

instance : SupSet (Concept α β r) :=
  ⟨fun S =>
    { fst := extentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd)
      snd := ⋂ c ∈ S, (c : Concept _ _ _).snd
      closure_fst := by
        simp_rw [← closure_fst, ← intentClosure_iUnion₂,
          intentClosure_extentClosure_intentClosure]
      closure_snd := rfl }⟩

instance : InfSet (Concept α β r) :=
  ⟨fun S =>
    { fst := ⋂ c ∈ S, (c : Concept _ _ _).fst
      snd := intentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst)
      closure_fst := rfl
      closure_snd := by
        simp_rw [← closure_snd, ← extentClosure_iUnion₂,
          extentClosure_intentClosure_extentClosure] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.instLatticeConcept,
    Concept.instBoundedOrderConcept with
    sup := Concept.instSupConcept.sup
    le_sSup := fun _ _ hc => snd_subset_snd_iff.1 <| biInter_subset_of_mem hc
    sSup_le := fun _ _ hc =>
      snd_subset_snd_iff.1 <| subset_iInter₂ fun d hd => snd_subset_snd_iff.2 <| hc d hd
    inf := Concept.instInfConcept.inf
    sInf_le := fun _ _ => biInter_subset_of_mem
    le_sInf := fun _ _ => subset_iInter₂ }

@[simp]
theorem top_fst : (⊤ : Concept α β r).fst = univ :=
  rfl
#align concept.top_fst Concept.top_fst

@[simp]
theorem top_snd : (⊤ : Concept α β r).snd = intentClosure r univ :=
  rfl
#align concept.top_snd Concept.top_snd

@[simp]
theorem bot_fst : (⊥ : Concept α β r).fst = extentClosure r univ :=
  rfl
#align concept.bot_fst Concept.bot_fst

@[simp]
theorem bot_snd : (⊥ : Concept α β r).snd = univ :=
  rfl
#align concept.bot_snd Concept.bot_snd

@[simp]
theorem sup_fst (c d : Concept α β r) : (c ⊔ d).fst = extentClosure r (c.snd ∩ d.snd) :=
  rfl
#align concept.sup_fst Concept.sup_fst

@[simp]
theorem sup_snd (c d : Concept α β r) : (c ⊔ d).snd = c.snd ∩ d.snd :=
  rfl
#align concept.sup_snd Concept.sup_snd

@[simp]
theorem inf_fst (c d : Concept α β r) : (c ⊓ d).fst = c.fst ∩ d.fst :=
  rfl
#align concept.inf_fst Concept.inf_fst

@[simp]
theorem inf_snd (c d : Concept α β r) : (c ⊓ d).snd = intentClosure r (c.fst ∩ d.fst) :=
  rfl
#align concept.inf_snd Concept.inf_snd

@[simp]
theorem sSup_fst (S : Set (Concept α β r)) :
    (sSup S).fst = extentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd) :=
  rfl
#align concept.Sup_fst Concept.sSup_fst

@[simp]
theorem sSup_snd (S : Set (Concept α β r)) : (sSup S).snd = ⋂ c ∈ S, (c : Concept _ _ _).snd :=
  rfl
#align concept.Sup_snd Concept.sSup_snd

@[simp]
theorem sInf_fst (S : Set (Concept α β r)) : (sInf S).fst = ⋂ c ∈ S, (c : Concept _ _ _).fst :=
  rfl
#align concept.Inf_fst Concept.sInf_fst

@[simp]
theorem sInf_snd (S : Set (Concept α β r)) :
    (sInf S).snd = intentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst) :=
  rfl
#align concept.Inf_snd Concept.sInf_snd

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.toProd.swap, c.closure_snd, c.closure_fst⟩
#align concept.swap Concept.swap
#align concept.swap_to_prod Concept.swap_toProd

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl
#align concept.swap_swap Concept.swap_swap

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  snd_subset_snd_iff
#align concept.swap_le_swap_iff Concept.swap_le_swap_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  snd_ssubset_snd_iff
#align concept.swap_lt_swap_iff Concept.swap_lt_swap_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff
#align concept.swap_equiv Concept.swapEquiv
#align concept.swap_equiv_symm_apply Concept.swapEquiv_symm_apply
#align concept.swap_equiv_apply Concept.swapEquiv_apply

end Concept
