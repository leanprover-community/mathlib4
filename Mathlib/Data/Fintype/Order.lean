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
@[reducible]
def toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le a := inf'_le _ <| mem_univ a
#align fintype.to_order_bot Fintype.toOrderBot

-- See note [reducible non-instances]
/-- Constructs the `⊤` of a finite nonempty `SemilatticeSup` -/
@[reducible]
def toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  -- Porting note: needed to make `id` explicit
  le_top a := le_sup' id <| mem_univ a
#align fintype.to_order_top Fintype.toOrderTop

-- See note [reducible non-instances]
/-- Constructs the `⊤` and `⊥` of a finite nonempty `Lattice`. -/
@[reducible]
def toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }
#align fintype.to_bounded_order Fintype.toBoundedOrder

end Nonempty

section BoundedOrder

variable (α)

open Classical

-- See note [reducible non-instances]
/-- A finite bounded lattice is complete. -/
@[reducible]
noncomputable def toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α :=
  { ‹Lattice α›,
    ‹BoundedOrder α› with
    sSup := fun s => s.toFinset.sup id
    sInf := fun s => s.toFinset.inf id
    le_sSup := fun _ _ ha => Finset.le_sup (f := id) (Set.mem_toFinset.mpr ha)
    sSup_le := fun s _ ha => Finset.sup_le fun b hb => ha _ <| Set.mem_toFinset.mp hb
    sInf_le := fun _ _ ha => Finset.inf_le (Set.mem_toFinset.mpr ha)
    le_sInf := fun s _ ha => Finset.le_inf fun b hb => ha _ <| Set.mem_toFinset.mp hb }
#align fintype.to_complete_lattice Fintype.toCompleteLattice

-- Porting note: `convert` doesn't work as well as it used to.
-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
@[reducible]
noncomputable def toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α :=
  { toCompleteLattice α with
    iInf_sup_le_sup_sInf := fun a s => by
      convert (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
      rw [Finset.inf_eq_iInf]
      simp_rw [Set.mem_toFinset]
      rfl
    inf_sSup_le_iSup_inf := fun a s => by
      convert (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
      rw [Finset.sup_eq_iSup]
      simp_rw [Set.mem_toFinset]
      rfl }
#align fintype.to_complete_distrib_lattice Fintype.toCompleteDistribLattice

-- See note [reducible non-instances]
/-- A finite bounded linear order is complete. -/
@[reducible]
noncomputable def toCompleteLinearOrder [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α› with }
#align fintype.to_complete_linear_order Fintype.toCompleteLinearOrder

-- See note [reducible non-instances]
/-- A finite boolean algebra is complete. -/
@[reducible]
noncomputable def toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α :=
  -- Porting note: using `Fintype.toCompleteDistribLattice α` caused timeouts
  { Fintype.toCompleteLattice α,
    ‹BooleanAlgebra α› with
    iInf_sup_le_sup_sInf := fun a s => by
      convert (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
      rw [Finset.inf_eq_iInf]
      simp_rw [Set.mem_toFinset]
      rfl
    inf_sSup_le_iSup_inf := fun a s => by
      convert (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
      rw [Finset.sup_eq_iSup]
      simp_rw [Set.mem_toFinset]
      rfl }
#align fintype.to_complete_boolean_algebra Fintype.toCompleteBooleanAlgebra

-- See note [reducible non-instances]
/-- A finite boolean algebra is complete and atomic. -/
@[reducible]
noncomputable def toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/-- A nonempty finite lattice is complete. If the lattice is already a `BoundedOrder`, then use
`Fintype.toCompleteLattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible]
noncomputable def toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| @toBoundedOrder α _ ⟨Classical.arbitrary α⟩ _
#align fintype.to_complete_lattice_of_nonempty Fintype.toCompleteLatticeOfNonempty

-- See note [reducible non-instances]
/-- A nonempty finite linear order is complete. If the linear order is already a `BoundedOrder`,
then use `Fintype.toCompleteLinearOrder` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible]
noncomputable def toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
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


variable {α : Type*}

theorem Directed.fintype_le {r : α → α → Prop} [IsTrans α r] {β γ : Type*} [Nonempty γ] {f : γ → α}
    [Fintype β] (D : Directed r f) (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
    obtain ⟨z, hz⟩ := D.finset_le (Finset.image g Finset.univ)
    exact ⟨z, fun i => hz (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))⟩
#align directed.fintype_le Directed.fintype_le

theorem Fintype.exists_le [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] {β : Type*} [Fintype β]
    (f : β → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.fintype_le _
#align fintype.exists_le Fintype.exists_le

theorem Fintype.exists_ge [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {β : Type*} [Fintype β]
    (f : β → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.fintype_le (r := (· ≥ ·)) _

theorem Fintype.bddAbove_range [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] {β : Type*}
    [Fintype β] (f : β → α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Fintype.exists_le f
  refine' ⟨M, fun a ha => _⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b
#align fintype.bdd_above_range Fintype.bddAbove_range

theorem Fintype.bddBelow_range [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {β : Type*}
    [Fintype β] (f : β → α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Fintype.exists_ge f
  refine' ⟨M, fun a ha => _⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b
