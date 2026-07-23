/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Order.Directed
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

@[expose] public section

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

/-- Structure containing the minimal axioms required to check that an order is a frame. Do NOT use,
except for implementing `Order.Frame` via `Order.Frame.ofMinimalAxioms`.

This structure omits the `himp`, `compl` fields, which can be recovered using
`Order.Frame.ofMinimalAxioms`. -/
class Order.Frame.MinimalAxioms (α : Type u) extends CompleteLattice α where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

/-- Structure containing the minimal axioms required to check that an order is a coframe. Do NOT
use, except for implementing `Order.Coframe` via `Order.Coframe.ofMinimalAxioms`.

This structure omits the `sdiff`, `hnot` fields, which can be recovered using
`Order.Coframe.ofMinimalAxioms`. -/
class Order.Coframe.MinimalAxioms (α : Type u) extends CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type*) extends CompleteLattice α, HeytingAlgebra α where

/-- `⊓` distributes over `⨆`. -/
theorem inf_sSup_eq {α : Type*} [Order.Frame α] {s : Set α} {a : α} :
    a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  gc_inf_himp.l_sSup

set_option linter.translate.warnInvalid false in
/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
@[to_dual]
class Order.Coframe (α : Type*) extends CompleteLattice α, CoheytingAlgebra α where

/-- `⊔` distributes over `⨅`. -/
theorem sup_sInf_eq {α : Type*} [Order.Coframe α] {s : Set α} {a : α} :
    a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  gc_sdiff_sup.u_sInf

open Order

/-- Structure containing the minimal axioms required to check that an order is a complete
distributive lattice. Do NOT use, except for implementing `CompleteDistribLattice` via
`CompleteDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompleteDistribLattice.ofMinimalAxioms`. -/
structure CompleteDistribLattice.MinimalAxioms (α : Type u)
    extends CompleteLattice α,
      toFrameMinimalAxioms : Frame.MinimalAxioms α,
      toCoframeMinimalAxioms : Coframe.MinimalAxioms α where

-- We give those projections better name further down
attribute [nolint docBlame] CompleteDistribLattice.MinimalAxioms.toFrameMinimalAxioms
  CompleteDistribLattice.MinimalAxioms.toCoframeMinimalAxioms

/-- A complete distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type*) extends Frame α, Coframe α, BiheytingAlgebra α

attribute [to_dual existing] CompleteDistribLattice.toFrame

/-- Structure containing the minimal axioms required to check that an order is a completely
distributive. Do NOT use, except for implementing `CompletelyDistribLattice` via
`CompletelyDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompletelyDistribLattice.ofMinimalAxioms`. -/
structure CompletelyDistribLattice.MinimalAxioms (α : Type u) extends CompleteLattice α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

/-- A completely distributive lattice is a complete lattice whose `⨅` and `⨆`
distribute over each other. -/
class CompletelyDistribLattice (α : Type u) extends CompleteLattice α, BiheytingAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

theorem le_iInf_iSup [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ g : ∀ a, κ a, ⨅ a, f a (g a)) ≤ ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

lemma iSup_iInf_le [CompleteLattice α] {f : ∀ a, κ a → α} :
    ⨆ a, ⨅ b, f a b ≤ ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

namespace Order.Frame.MinimalAxioms
variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

lemma inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (minAx.inf_sSup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup

lemma sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

lemma iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

lemma inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

lemma inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [inf_iSup_eq]

/-- The `Order.Frame.MinimalAxioms` element corresponding to a frame. -/
@[instance_reducible]
def of [Frame α] : MinimalAxioms α where
  __ := ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le

end MinimalAxioms

/-- Construct a frame instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}` and `aᶜ := a ⇨ ⊥`. -/
-- See note [reducible non-instances]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : Frame α where
  __ := minAx
  compl a := sSup {c | c ⊓ a ≤ ⊥}
  himp a b := sSup {c | c ⊓ a ≤ b}
  le_himp_iff _ b c :=
    ⟨fun h ↦ (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h ↦ le_sSup h⟩
  himp_bot _ := rfl

end Order.Frame

namespace Order.Coframe.MinimalAxioms
variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

lemma sup_sInf_eq : a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  sup_sInf_le_iInf_sup.antisymm (minAx.iInf_sup_le_sup_sInf _ _)

lemma sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b := by
  simpa only [sup_comm] using @sup_sInf_eq α _ s b

lemma iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a := by
  rw [iInf, sInf_sup_eq, iInf_range]

lemma sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i := by
  simpa only [sup_comm] using minAx.iInf_sup_eq f a

lemma sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ i, ⨅ j, f i j) = ⨅ i, ⨅ j, a ⊔ f i j := by
  simp only [sup_iInf_eq]

/-- The `Order.Coframe.MinimalAxioms` element corresponding to a frame. -/
@[instance_reducible]
def of [Coframe α] : MinimalAxioms α where
  __ := ‹Coframe α›
  iInf_sup_le_sup_sInf a s := _root_.sup_sInf_eq.ge

end MinimalAxioms

/-- Construct a coframe instance using the minimal amount of work needed.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : Coframe α where
  __ := minAx
  hnot a := sInf {c | ⊤ ≤ a ⊔ c}
  sdiff a b := sInf {c | a ≤ b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h ↦ (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h ↦ sInf_le h⟩
  top_sdiff _ := rfl

end Order.Coframe

namespace CompleteDistribLattice.MinimalAxioms
variable (minAx : MinimalAxioms α)

/-- The `CompleteDistribLattice.MinimalAxioms` element corresponding to a complete distrib lattice.
-/
@[instance_reducible]
def of [CompleteDistribLattice α] : MinimalAxioms α where
  __ := ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Frame`. -/
abbrev toFrame : Frame.MinimalAxioms α := minAx.toFrameMinimalAxioms

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Coframe`. -/
abbrev toCoframe : Coframe.MinimalAxioms α where __ := minAx

end MinimalAxioms

/-- Construct a complete distrib lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : CompleteDistribLattice α where
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice

namespace CompletelyDistribLattice.MinimalAxioms
variable (minAx : MinimalAxioms α)

lemma iInf_iSup_eq' (f : ∀ a, κ a → α) :
    let _ := minAx.toCompleteLattice
    ⨅ i, ⨆ j, f i j = ⨆ g : ∀ i, κ i, ⨅ i, f i (g i) := by
  let _ := minAx.toCompleteLattice
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ ≤ _ := iSup_le fun g => by
      refine le_trans ?_ <| le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      rw [← Classical.choose_spec (g ⟨_, a, rfl⟩).2]

lemma iSup_iInf_eq (f : ∀ i, κ i → α) :
    let _ := minAx.toCompleteLattice
    ⨆ i, ⨅ j, f i j = ⨅ g : ∀ i, κ i, ⨆ i, f i (g i) := by
  let _ := minAx.toCompleteLattice
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f, ∃ h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  refine le_iInf fun b => ?_
  obtain ⟨h, rfl, rfl⟩ := ha b
  exact iInf_le _ _

/-- Turn minimal axioms for `CompletelyDistribLattice` into minimal axioms for
`CompleteDistribLattice`. -/
abbrev toCompleteDistribLattice : CompleteDistribLattice.MinimalAxioms α where
  __ := minAx
  inf_sSup_le_iSup_inf a s := by
    let _ := minAx.toCompleteLattice
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ ≤ _ := by
        simp only [minAx.iInf_iSup_eq, iInf_ulift, iInf_bool_eq, iSup_le_iff]
        exact fun x ↦ le_biSup _ (x (.up false)).2
  iInf_sup_le_sup_sInf a s := by
    let _ := minAx.toCompleteLattice
    calc
      _ ≤ ⨆ i : ULift.{u} Bool, ⨅ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by
        simp only [minAx.iSup_iInf_eq, iSup_ulift, iSup_bool_eq, le_iInf_iff]
        exact fun x ↦ biInf_le _ (x (.up false)).2
      _ = _ := by simp [sInf_eq_iInf', iInf_unique, iSup_bool_eq]

/-- The `CompletelyDistribLattice.MinimalAxioms` element corresponding to a frame. -/
@[instance_reducible]
def of [CompletelyDistribLattice α] : MinimalAxioms α := { ‹CompletelyDistribLattice α› with }

end MinimalAxioms

/-- Construct a completely distributive lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : CompletelyDistribLattice α where
  __ := minAx
  __ := CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice

end CompletelyDistribLattice

theorem iInf_iSup_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _

theorem iSup_iInf_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨆ a, ⨅ b, f a b) = ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iSup_iInf_eq _

theorem biSup_iInter_of_pairwise_disjoint [CompletelyDistribLattice α] {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι → α} (h : Pairwise (Disjoint on f)) (s : κ → Set ι) :
    (⨆ i ∈ (⋂ j, s j), f i) = ⨅ j, (⨆ i ∈ s j, f i) := by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi ↦ le_iSup₂_of_le (fun _ ↦ i) hi (le_iInf fun _ ↦ le_rfl))
    (iSup₂_le fun I hI ↦ ?_)
  by_cases! H : ∀ k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k ↦ (H k) ▸ (hI k)) (iInf_le _ _)
  · rcases H with ⟨k, hk⟩
    calc ⨅ l, f (I l)
    _ ≤ f (I k) ⊓ f (I j) := le_inf (iInf_le _ _) (iInf_le _ _)
    _ = ⊥ := (h hk).eq_bot
    _ ≤ _ := bot_le

instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  __ := ‹CompletelyDistribLattice α›

-- See note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toCompletelyDistribLattice [CompleteLinearOrder α] :
    CompletelyDistribLattice α where
  __ := ‹CompleteLinearOrder α›
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    let rhs := ⨆ h : ∀ a, β a, ⨅ a, g a (h a)
    suffices lhs ≤ rhs from le_antisymm this le_iInf_iSup
    if h : ∃ x, rhs < x ∧ x < lhs then
      rcases h with ⟨x, hr, hl⟩
      suffices rhs ≥ x from nomatch not_lt.2 this hr
      have : ∀ a, ∃ b, x < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_not_ge fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => le_of_lt (hf a)
    else
      refine le_of_not_gt fun hrl : rhs < lhs => not_le_of_gt hrl ?_
      replace h : ∀ x, x ≤ rhs ∨ lhs ≤ x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : ∀ a, ∃ b, rhs < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : ∀ a, lhs ≤ g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => this _

section Frame

variable [Frame α] {s t : Set α} {a b c d : α}

instance OrderDual.instCoframe : Coframe αᵒᵈ where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a

theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) :
    (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a := by
  simp only [iSup_inf_eq]

theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) :
    (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j := by
  simp only [inf_iSup_eq]

theorem himp_iInf_eq {f : ι → α} : a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x :=
  eq_of_forall_le_iff fun b => by simp

theorem iSup_himp_eq {f : ι → α} : (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a :=
  eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

theorem iSup_inf_iSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

theorem biSup_inf_biSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

theorem biSup_inter_of_pairwise_disjoint {ι : Type*} {f : ι → α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⨆ i ∈ (s ∩ t), f i) = (⨆ i ∈ s, f i) ⊓ (⨆ i ∈ t, f i) := by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ ↦ le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ ↦ ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]

theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]

theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

theorem himp_eq_sSup : a ⇨ b = sSup {w | w ⊓ a ≤ b} :=
  (isGreatest_himp a b).isLUB.sSup_eq.symm

theorem compl_eq_sSup_disjoint : aᶜ = sSup {w | Disjoint w a} :=
  (isGreatest_compl a).isLUB.sSup_eq.symm

lemma himp_le_iff : a ⇨ b ≤ c ↔ ∀ d, d ⊓ a ≤ b → d ≤ c := by simp [himp_eq_sSup]

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]

instance Prod.instFrame [Frame β] : Frame (α × β) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

instance Pi.instFrame {ι : Type*} {π : ι → Type*} [∀ i, Frame (π i)] : Frame (∀ i, π i) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

section bihimp

variable {f : ι → α}
open scoped symmDiff

/-- The bihimp of two `iInf`s is at least the `iInf` of the bihimps. -/
theorem le_iInf_bihimp_iInf {g : ι → α} : ⨅ i, ((f i) ⇔ (g i)) ≤ (⨅ i, f i) ⇔ (⨅ i, g i) := by
  simp_rw [le_bihimp_iff, ← iInf_inf_eq]
  exact ⟨iInf_mono fun i ↦ (inf_le_inf_right _
      (bihimp_def _ _ |>.le.trans inf_le_right)).trans himp_inf_le,
    iInf_mono fun i ↦ (inf_le_inf_right _
      (bihimp_def _ _ |>.le.trans inf_le_left)).trans himp_inf_le⟩

theorem le_iInf_bihimp [Nonempty ι] {a : α} : ⨅ i, f i ⇔ a ≤ (⨅ i, f i) ⇔ a := by
  simpa [iInf_const] using le_iInf_bihimp_iInf (g := fun _ : ι ↦ a)

theorem le_bihimp_iInf [Nonempty ι] {a : α} : ⨅ i, a ⇔ f i ≤ a ⇔ (⨅ i, f i) := by
  simpa [bihimp_comm] using le_iInf_bihimp (a := a)

theorem le_sInf_bihimp (hs : s.Nonempty) {a : α} : sInf ((· ⇔ a) '' s) ≤ sInf s ⇔ a := by
  rw [sInf_image', sInf_eq_iInf']
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  exact le_iInf_bihimp

theorem le_bihimp_sInf (hs : s.Nonempty) {a : α} : sInf ((a ⇔ ·) '' s) ≤ a ⇔ sInf s := by
  simpa [bihimp_comm] using le_sInf_bihimp (a := a) hs

theorem le_sInf_bihimp_sInf {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty) :
    sInf (image2 (· ⇔ ·) s t) ≤ sInf s ⇔ sInf t := by
  rw [sInf_image2]
  calc
  _ ≤ ⨅ a ∈ s, a ⇔ sInf t :=
    iInf₂_mono fun a _ ↦ by simpa [sInf_image] using le_bihimp_sInf ht
  _ ≤ _ := by simpa [sInf_image] using le_sInf_bihimp hs

/-- A `biInf` version of `le_sInf_bihimp_sInf`. -/
theorem le_biInf_bihimp_biInf {p : ι → Prop} {f g : (i : ι) → p i → α} :
    ⨅ i, ⨅ (h : p i), ((f i h) ⇔ (g i h)) ≤
    (⨅ i, ⨅ (h : p i), f i h) ⇔ (⨅ i, ⨅ (h : p i), g i h) :=
  le_trans (iInf_mono fun _ ↦ le_iInf_bihimp_iInf) le_iInf_bihimp_iInf

end bihimp

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b c d : α}

instance OrderDual.instFrame : Frame αᵒᵈ where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

theorem sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @sSup_inf_eq αᵒᵈ _ _ _

theorem iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @iSup_inf_eq αᵒᵈ _ _ _ _

theorem sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_iSup_eq αᵒᵈ _ _ _ _

theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _

theorem sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_iSup₂_eq αᵒᵈ _ _ _ _ _

theorem iSup_sdiff_eq {f : ι → α} : (⨆ x, f x) \ a = ⨆ x, f x \ a :=
  eq_of_forall_ge_iff fun _ => by simp

theorem sdiff_iSup_eq {f : ι → α} : a \ ⨅ x, f x = ⨆ x, a \ f x :=
  eq_of_forall_ge_iff fun _ => by simp [iInf_sup_eq]

@[to_dual existing]
theorem iInf_sup_iInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _

theorem biInf_sup_biInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _

theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _

@[to_dual existing]
theorem iInf_sup_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_antitone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right

theorem iInf_sup_of_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_monotone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right

theorem sdiff_eq_sInf : a \ b = sInf {w | a ≤ b ⊔ w} :=
  (isLeast_sdiff a b).isGLB.sInf_eq.symm

theorem hnot_eq_sInf_codisjoint : ￢a = sInf {w | Codisjoint a w} :=
  (isLeast_hnot a).isGLB.sInf_eq.symm

lemma le_sdiff_iff : a ≤ b \ c ↔ ∀ d, b ≤ c ⊔ d → a ≤ d := by simp [sdiff_eq_sInf]

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α where
  __ := ‹Coframe α›
  le_sup_inf a b c := by
    rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair]

instance Prod.instCoframe [Coframe β] : Coframe (α × β) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

instance Pi.instCoframe {ι : Type*} {π : ι → Type*} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

section symmDiff

variable {f : ι → α}
open scoped symmDiff

/-- The symmetric difference of two `iSup`s is at most the `iSup` of the symmetric differences. -/
theorem iSup_symmDiff_iSup_le {g : ι → α} : (⨆ i, f i) ∆ (⨆ i, g i) ≤ ⨆ i, ((f i) ∆ (g i)) :=
  @le_iInf_bihimp_iInf αᵒᵈ _ _ _ _

theorem iSup_symmDiff_le [Nonempty ι] {a : α} : (⨆ i, f i) ∆ a ≤ ⨆ i, f i ∆ a :=
  @le_iInf_bihimp αᵒᵈ _ _ _ _ _

theorem symmDiff_iSup_le [Nonempty ι] {a : α} : a ∆ (⨆ i, f i) ≤ ⨆ i, a ∆ f i :=
  @le_bihimp_iInf αᵒᵈ _ _ _ _ _

theorem sSup_symmDiff_le (hs : s.Nonempty) {a : α} : sSup s ∆ a ≤ sSup ((· ∆ a) '' s) :=
  @le_sInf_bihimp αᵒᵈ _ _ hs _

theorem symmDiff_sSup_le (hs : s.Nonempty) {a : α} : a ∆ sSup s ≤ sSup ((a ∆ ·) '' s) :=
  @le_bihimp_sInf αᵒᵈ _ _ hs _

theorem sSup_symmDiff_sSup_le {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup s ∆ sSup t ≤ sSup (image2 (· ∆ ·) s t) :=
  @le_sInf_bihimp_sInf αᵒᵈ _ _ _ hs ht

/-- A `biSup` version of `iSup_symmDiff_iSup_le`. -/
theorem biSup_symmDiff_biSup_le {p : ι → Prop} {f g : (i : ι) → p i → α} :
    (⨆ i, ⨆ (h : p i), f i h) ∆ (⨆ i, ⨆ (h : p i), g i h) ≤
    ⨆ i, ⨆ (h : p i), ((f i h) ∆ (g i h)) :=
  @le_biInf_bihimp_biInf αᵒᵈ _ _ _ _ _

end symmDiff

end Coframe

section CompleteDistribLattice

instance OrderDual.instCompleteDistribLattice [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe

instance Prod.instCompleteDistribLattice [CompleteDistribLattice α] [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe

instance Pi.instCompleteDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe

end CompleteDistribLattice

section CompletelyDistribLattice

instance OrderDual.instCompletelyDistribLattice [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

instance Prod.instCompletelyDistribLattice [CompletelyDistribLattice α]
    [CompletelyDistribLattice β] : CompletelyDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

instance Pi.instCompletelyDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompletelyDistribLattice (π i)] : CompletelyDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

end CompletelyDistribLattice

/--
A complete Boolean algebra is a Boolean algebra that is also a complete distributive lattice.

It is only completely distributive if it is also atomic.
-/
-- We do not directly extend `CompleteDistribLattice` to avoid having the `hnot` field
class CompleteBooleanAlgebra (α) extends CompleteLattice α, BooleanAlgebra α

-- See note [lower instance priority]
instance (priority := 100) CompleteBooleanAlgebra.toCompleteDistribLattice
    [CompleteBooleanAlgebra α] : CompleteDistribLattice α where
  __ := ‹CompleteBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

instance Prod.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β] :
    CompleteBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

instance Pi.instCompleteBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

instance OrderDual.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra αᵒᵈ where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {s : Set α} {f : ι → α}

theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])

theorem compl_sInf : (sInf s)ᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]

theorem compl_sSup : (sSup s)ᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]

theorem compl_sInf' : (sInf s)ᶜ = sSup (Compl.compl '' s) :=
  compl_sInf.trans sSup_image.symm

theorem compl_sSup' : (sSup s)ᶜ = sInf (Compl.compl '' s) :=
  compl_sSup.trans sInf_image.symm

end CompleteBooleanAlgebra

/--
A complete atomic Boolean algebra is a complete Boolean algebra
that is also completely distributive.

We take iSup_iInf_eq as the definition here,
and prove later on that this implies atomicity.
-/
-- We do not directly extend `CompletelyDistribLattice` to avoid having the `hnot` field
class CompleteAtomicBooleanAlgebra (α : Type u) extends CompleteBooleanAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

-- See note [lower instance priority]
instance (priority := 100) CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice
    [CompleteAtomicBooleanAlgebra α] : CompletelyDistribLattice α where
  __ := ‹CompleteAtomicBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

instance Prod.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α]
    [CompleteAtomicBooleanAlgebra β] : CompleteAtomicBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompletelyDistribLattice

instance Pi.instCompleteAtomicBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (∀ i, π i) where
  __ := Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]

instance OrderDual.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra αᵒᵈ where
  __ := instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice

instance Prop.instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]

instance Prop.instCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop := inferInstance

section lift

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame.MinimalAxioms` along an injection. -/
protected abbrev Function.Injective.frameMinimalAxioms [Max α] [Min α] [LE α] [LT α]
    [SupSet α] [InfSet α] [Top α] [Bot α] (minAx : Frame.MinimalAxioms β)
    (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Frame.MinimalAxioms α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  inf_sSup_le_iSup_inf a s := by
    rw [← le, ← sSup_image, map_inf, map_sSup s, minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe.MinimalAxioms` along an injection. -/
protected abbrev Function.Injective.coframeMinimalAxioms [Max α] [Min α] [LE α] [LT α]
    [SupSet α] [InfSet α] [Top α] [Bot α] (minAx : Coframe.MinimalAxioms β)
    (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Coframe.MinimalAxioms α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_sup_le_sup_sInf a s := by
    rw [← le, ← sInf_image, map_sup, map_sInf s, minAx.sup_iInf₂_eq]
    simp_rw [← map_sup]
    exact ((map_sInf _).trans iInf_image).le

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame` along an injection. -/
protected abbrev Function.Injective.frame [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [Compl α] [HImp α] [Frame β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : Frame α where
  __ := hf.frameMinimalAxioms .of f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe` along an injection. -/
protected abbrev Function.Injective.coframe [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HNot α] [SDiff α] [Coframe β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : Coframe α where
  __ := hf.coframeMinimalAxioms .of f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice.MinimalAxioms` along an injection. -/
protected abbrev Function.Injective.completeDistribLatticeMinimalAxioms [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α]
    (minAx : CompleteDistribLattice.MinimalAxioms β) (f : α → β) (hf : Injective f)
    (le : let _ := minAx.toCompleteLattice; ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (lt : let _ := minAx.toCompleteLattice; ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : let _ := minAx.toCompleteLattice; ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : let _ := minAx.toCompleteLattice; ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : let _ := minAx.toCompleteLattice; ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : let _ := minAx.toCompleteLattice; ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : let _ := minAx.toCompleteLattice; f ⊤ = ⊤)
    (map_bot : let _ := minAx.toCompleteLattice; f ⊥ = ⊥) :
    CompleteDistribLattice.MinimalAxioms α where
  __ := hf.frameMinimalAxioms minAx.toFrame f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coframeMinimalAxioms minAx.toCoframe f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice` along an injection. -/
protected abbrev Function.Injective.completeDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteDistribLattice β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteDistribLattice α where
  __ := hf.frame f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff

-- See note [reducible non-instances]
/-- Pullback a `CompletelyDistribLattice.MinimalAxioms` along an injection. -/
protected abbrev Function.Injective.completelyDistribLatticeMinimalAxioms [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α]
    (minAx : CompletelyDistribLattice.MinimalAxioms β) (f : α → β) (hf : Injective f)
    (le : let _ := minAx.toCompleteLattice; ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (lt : let _ := minAx.toCompleteLattice; ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : let _ := minAx.toCompleteLattice; ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : let _ := minAx.toCompleteLattice; ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : let _ := minAx.toCompleteLattice; ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : let _ := minAx.toCompleteLattice; ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : let _ := minAx.toCompleteLattice; f ⊤ = ⊤)
    (map_bot : let _ := minAx.toCompleteLattice; f ⊥ = ⊥) :
    CompletelyDistribLattice.MinimalAxioms α where
  __ := hf.completeDistribLatticeMinimalAxioms minAx.toCompleteDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']

-- See note [reducible non-instances]
/-- Pullback a `CompletelyDistribLattice` along an injection. -/
protected abbrev Function.Injective.completelyDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompletelyDistribLattice β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompletelyDistribLattice α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f
    le lt map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.completeBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [SDiff α]
    [CompleteBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

-- See note [reducible non-instances]
/-- Pullback a `CompleteAtomicBooleanAlgebra` along an injection. -/
protected abbrev Function.Injective.completeAtomicBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteAtomicBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `Frame` across an `Equiv`. -/
protected abbrev frame [Frame β] : Frame α := by
  let completeLattice := e.completeLattice
  let heytingAlgebra := e.heytingAlgebra
  apply e.injective.frame <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `Coframe` across an `Equiv`. -/
protected abbrev coframe [Coframe β] : Coframe α := by
  let completeLattice := e.completeLattice
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.coframe <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteDistribLattice` across an `Equiv`. -/
protected abbrev completeDistribLattice [CompleteDistribLattice β] : CompleteDistribLattice α := by
  let completeLattice := e.completeLattice
  let biheytingAlgebra := e.biheytingAlgebra
  apply e.injective.completeDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompletelyDistribLattice` across an `Equiv`. -/
protected abbrev completelyDistribLattice [CompletelyDistribLattice β] :
    CompletelyDistribLattice α := by
  let completeDistribLattice := e.completeDistribLattice
  apply e.injective.completelyDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteBooleanAlgebra` across an `Equiv`. -/
protected abbrev completeBooleanAlgebra [CompleteBooleanAlgebra β] : CompleteBooleanAlgebra α := by
  let completeLattice := e.completeLattice
  let booleanAlgebra := e.booleanAlgebra
  apply e.injective.completeBooleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteAtomicBooleanAlgebra` across an `Equiv`. -/
protected abbrev completeAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra β] :
    CompleteAtomicBooleanAlgebra α := by
  let completeBooleanAlgebra := e.completeBooleanAlgebra
  apply e.injective.completeAtomicBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1})

instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra PUnit where

instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit where
  iInf_iSup_eq _ := rfl

@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl

@[simp]
theorem sInf_eq : sInf s = unit :=
  rfl

end PUnit
