/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
import Mathlib.Data.Finset.Order
import Mathlib.Order.Atoms.Finite

#align_import data.fintype.order from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `Fintype`, we can construct
* an `OrderBot` from `SemilatticeInf`.
* an `OrderTop` from `SemilatticeSup`.
* a `BoundedOrder` from `Lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `sSup` and `sInf` use `Set.toFinset`
and set membership is undecidable in general.

On a `Fintype`, we can promote:
* a `Lattice` to a `CompleteLattice`.
* a `DistribLattice` to a `CompleteDistribLattice`.
* a `LinearOrder` to a `CompleteLinearOrder`.
* a `BooleanAlgebra` to a `CompleteAtomicBooleanAlgebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `Fin.completeLinearOrder`
* `Bool.completeLinearOrder`
* `Bool.completeBooleanAlgebra`
-/


open Finset

namespace Fintype

variable {ι α : Type*} [Fintype ι] [Fintype α]

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/-- Constructs the `⊥` of a finite nonempty `SemilatticeInf`. -/
abbrev toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le a := inf'_le _ <| mem_univ a
#align fintype.to_order_bot Fintype.toOrderBot

-- See note [reducible non-instances]
/-- Constructs the `⊤` of a finite nonempty `SemilatticeSup` -/
abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  -- Porting note: needed to make `id` explicit
  le_top a := le_sup' id <| mem_univ a
#align fintype.to_order_top Fintype.toOrderTop

-- See note [reducible non-instances]
/-- Constructs the `⊤` and `⊥` of a finite nonempty `Lattice`. -/
abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }
#align fintype.to_bounded_order Fintype.toBoundedOrder

end Nonempty

section BoundedOrder

variable (α)

open scoped Classical

-- See note [reducible non-instances]
/-- A finite bounded lattice is complete. -/
noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  le_sSup := fun _ _ ha => Finset.le_sup (f := id) (Set.mem_toFinset.mpr ha)
  sSup_le := fun s _ ha => Finset.sup_le fun b hb => ha _ <| Set.mem_toFinset.mp hb
  sInf_le := fun _ _ ha => Finset.inf_le (Set.mem_toFinset.mpr ha)
  le_sInf := fun s _ ha => Finset.le_inf fun b hb => ha _ <| Set.mem_toFinset.mp hb
#align fintype.to_complete_lattice Fintype.toCompleteLattice

-- Porting note: `convert` doesn't work as well as it used to.
-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α where
  __ := toCompleteLattice α
  iInf_sup_le_sup_sInf := fun a s => by
    convert (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl
#align fintype.to_complete_distrib_lattice Fintype.toCompleteDistribLattice

-- See note [reducible non-instances]
/-- A finite bounded linear order is complete. -/
noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α› with }
#align fintype.to_complete_linear_order Fintype.toCompleteLinearOrder

-- See note [reducible non-instances]
/-- A finite boolean algebra is complete. -/
noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α
#align fintype.to_complete_boolean_algebra Fintype.toCompleteBooleanAlgebra

-- See note [reducible non-instances]
/-- A finite boolean algebra is complete and atomic. -/
noncomputable abbrev toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/-- A nonempty finite lattice is complete. If the lattice is already a `BoundedOrder`, then use
`Fintype.toCompleteLattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
noncomputable abbrev toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| @toBoundedOrder α _ ⟨Classical.arbitrary α⟩ _
#align fintype.to_complete_lattice_of_nonempty Fintype.toCompleteLatticeOfNonempty

-- See note [reducible non-instances]
/-- A nonempty finite linear order is complete. If the linear order is already a `BoundedOrder`,
then use `Fintype.toCompleteLinearOrder` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
  { toCompleteLatticeOfNonempty α, ‹LinearOrder α› with }
#align fintype.to_complete_linear_order_of_nonempty Fintype.toCompleteLinearOrderOfNonempty

end Nonempty

end Fintype

/-! ### Concrete instances -/


noncomputable instance Fin.completeLinearOrder {n : ℕ} : CompleteLinearOrder (Fin (n + 1)) :=
  Fintype.toCompleteLinearOrder _

noncomputable instance Bool.completeLinearOrder : CompleteLinearOrder Bool :=
  Fintype.toCompleteLinearOrder _

noncomputable instance Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _

noncomputable instance Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool :=
  Fintype.toCompleteAtomicBooleanAlgebra _

/-! ### Directed Orders -/


variable {α : Type*} {r : α → α → Prop} [IsTrans α r] {β γ : Type*} [Nonempty γ] {f : γ → α}
  [Finite β] (D : Directed r f)

theorem Directed.finite_set_le {s : Set γ} (hs : s.Finite) : ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert D.finset_le hs.toFinset; rw [Set.Finite.mem_toFinset]

theorem Directed.finite_le (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
    obtain ⟨z, hz⟩ := D.finite_set_le (Set.finite_range g)
    exact ⟨z, fun i => hz (g i) ⟨i, rfl⟩⟩
#align directed.fintype_le Directed.finite_le

variable [Nonempty α] [Preorder α]

theorem Finite.exists_le [IsDirected α (· ≤ ·)] (f : β → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.finite_le _
#align fintype.exists_le Finite.exists_le

theorem Finite.exists_ge [IsDirected α (· ≥ ·)] (f : β → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.finite_le (r := (· ≥ ·)) _

theorem Set.Finite.exists_le [IsDirected α (· ≤ ·)] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finite_set_le hs

theorem Set.Finite.exists_ge [IsDirected α (· ≥ ·)] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, M ≤ i :=
  directed_id.finite_set_le (r := (· ≥ ·)) hs

theorem Finite.bddAbove_range [IsDirected α (· ≤ ·)] (f : β → α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b
#align fintype.bdd_above_range Finite.bddAbove_range

theorem Finite.bddBelow_range [IsDirected α (· ≥ ·)] (f : β → α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[deprecated] alias Directed.fintype_le := Directed.finite_le
@[deprecated] alias Fintype.exists_le := Finite.exists_le
@[deprecated] alias Fintype.exists_ge := Finite.exists_ge
@[deprecated] alias Fintype.bddAbove_range := Finite.bddAbove_range
@[deprecated] alias Fintype.bddBelow_range := Finite.bddBelow_range
