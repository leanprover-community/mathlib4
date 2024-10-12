
/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Order.CompleteLattice
import Mathlib.Data.Set.Subset
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.Irreducible
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Sets.Closeds

/-

In Order/SupClosed

def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s

structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

In Order/Sublattice

structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

abbrev ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α := ⟨s, hs.1, hs.2⟩

/-- A sublattice of a lattice inherits a lattice structure. -/
instance instLatticeCoe (L : Sublattice α) : Lattice L :=
  Subtype.coe_injective.lattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

In Order/CompleteSublattice

structure CompleteSublattice extends Sublattice α where
  sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier
  sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier

variable {L : CompleteSublattice α}

instance instCompleteLattice : CompleteLattice L :=
  Subtype.coe_injective.completeLattice _
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

-/

δₑA^*₁  ∈

kₙ(ker x)


variable {α : Type*}

open Set
open Set.Notation

section CompleteSemilatticeSup

variable [CompleteLattice α]

/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def sSupClosed (s : Set α) : Prop := ∀ ⦃t⦄, t ⊆ s → sSup t ∈ s

def CompleteSublattice.closed (s : Set α) : Prop := ∀ ⦃t⦄, t ⊆ s → sSup t ∈ s

-- If s is complete closed, is it a sublattice?

lemma complete_closed_SupClosed (s : Set α) (hs : CompleteSublattice.closed s ) : SupClosed s := by
  intro a ha b hb
  rw [← sSup_pair]
  apply hs (pair_subset ha hb)

lemma complete_closed_InfClosed (s : Set α) (hs : CompleteSublattice.closed s ) : InfClosed s := by
  intro a ha b hb



lemma CompleteSublattice.closed_iff_sInf_closed (s : Set α) :
  CompleteSublattice.closed s ↔ ∀ ⦃t⦄, t ⊆ s → sInf t ∈ s := by
  constructor
  · intro hs t hts
    rw [CompleteSublattice.closed] at hs

    have e2: IsGLB (α :=  s) ⟨t,hts⟩ (sInf t) := by
      rw [IsGLB, IsGreatest]
      constructor
      · rw [lowerBounds]
        simp only [mem_setOf_eq]
        exact fun ⦃a⦄ a_1 ↦ CompleteSemilatticeInf.sInf_le t a a_1
      · rw [upperBounds]
        simp only [mem_setOf_eq, le_sInf_iff]
        intro a ha b hb
        exact ha hb


    have e1 : sSup (lowerBounds t) = sInf t := by
      rw [sInf, sSup,lowerBounds]
      sorry



    --apply isGLB_sInf

def sSupClosed.toCompleteSemilatticeSup (s : Set α) (h : sSupClosed s) : CompleteSemilatticeSup s where
  sSup t := ⟨sSup t, h (Subtype.coe_image_subset s t)
  ⟩
  le_sSup t a ha := by exact?
  sSup_le := sorry

end CompleteSemilatticeSup
