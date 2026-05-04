/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Set.Finite.Basic  -- shake: keep (IsAtomic α), cf. lean#13417
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Atoms

import Mathlib.Data.Finite.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

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

public section


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

-- See note [reducible non-instances]
/-- Constructs the `⊤` of a finite nonempty `SemilatticeSup` -/
abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  le_top a := le_sup' id <| mem_univ a

-- See note [reducible non-instances]
/-- Constructs the `⊤` and `⊥` of a finite nonempty `Lattice`. -/
abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }

end Nonempty

section BoundedOrder

variable (α)

open scoped Classical in
-- See note [reducible non-instances]
/-- A finite bounded lattice is complete. -/
noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
noncomputable abbrev toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice.MinimalAxioms α where
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

-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α := .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

-- See note [reducible non-instances]
/-- A finite bounded linear order is complete.

If the `α` is already a `BiheytingAlgebra`, then prefer to construct this instance manually using
`Fintype.toCompleteLattice` instead, to avoid creating a diamond with
`LinearOrder.toBiheytingAlgebra`. -/
noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

-- See note [reducible non-instances]
/-- A finite Boolean algebra is complete. -/
noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

-- See note [reducible non-instances]
/-- A finite Boolean algebra is complete and atomic. -/
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
  @toCompleteLattice _ _ _ <| toBoundedOrder α

-- See note [reducible non-instances]
/-- A nonempty finite linear order is complete. If the linear order is already a `BoundedOrder`,
then use `Fintype.toCompleteLinearOrder` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
  @toCompleteLinearOrder _ _ _ <| toBoundedOrder α

end Nonempty

end Fintype

/-! ### Concrete instances -/

noncomputable instance Fin.completeLinearOrder {n : ℕ} [NeZero n] : CompleteLinearOrder (Fin n) :=
  Fintype.toCompleteLinearOrder _

noncomputable instance Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _

noncomputable instance Bool.completeLinearOrder : CompleteLinearOrder Bool where
  __ := Fintype.toCompleteLattice _
  __ : BiheytingAlgebra Bool := inferInstance
  __ : LinearOrder Bool := inferInstance

noncomputable instance Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool :=
  Fintype.toCompleteAtomicBooleanAlgebra _

/-! ### Directed Orders -/

section DirectedOrders

variable {α : Type*} {r : α → α → Prop} [IsTrans α r] {β γ : Type*} [Nonempty γ] {f : γ → α}
  [Finite β]

theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

theorem Directed.finite_le (D : Directed r f) (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
    obtain ⟨z, hz⟩ := D.finite_set_le (Set.finite_range g)
    exact ⟨z, fun i => hz (g i) ⟨i, rfl⟩⟩

variable [Nonempty α] [Preorder α]

theorem Finite.exists_le [IsDirectedOrder α] (f : β → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.finite_le _

theorem Finite.exists_ge [IsCodirectedOrder α] (f : β → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.finite_le (r := (· ≥ ·)) _

theorem Set.Finite.exists_le [IsDirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finite_set_le hs

theorem Set.Finite.exists_ge [IsCodirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, M ≤ i :=
  directed_id.finite_set_le (r := (· ≥ ·)) hs

@[simp]
theorem Finite.bddAbove_range [IsDirectedOrder α] (f : β → α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[simp]
theorem Finite.bddBelow_range [IsCodirectedOrder α] (f : β → α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

end DirectedOrders

/-!
### Suprema and infima over finite types

We state simplified versions of `le_ciSup_if_le` and `ciSup_mono` when the indexing type
is finite. This avoids having to explicitly use `Finite.bddAbove_range`.

Similarly for `ciInf`.
-/

section ciSup

namespace Finite

section CCL

variable {α ι ι' : Type*} [Finite ι] [Finite ι'] [ConditionallyCompleteLattice α]

lemma le_ciSup_of_le {a : α} {f : ι → α} (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  _root_.le_ciSup_of_le (bddAbove_range f) c h

lemma ciInf_le_of_le {a : α} {f : ι → α} (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  _root_.ciInf_le_of_le (bddBelow_range f) c h

lemma ciSup_mono {f g : ι → α} (H : ∀ (x : ι), f x ≤ g x) : iSup f ≤ iSup g :=
  _root_.ciSup_mono (bddAbove_range g) H

lemma ciInf_mono {f g : ι → α} (H : ∀ (x : ι), f x ≤ g x) : iInf f ≤ iInf g :=
  _root_.ciInf_mono (bddBelow_range f) H

lemma le_ciSup (f : ι → α) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup_of_le i le_rfl

lemma ciInf_le (f : ι → α) (i : ι) : ⨅ j, f j ≤ f i :=
  le_ciSup (α := αᵒᵈ) f i

lemma ciSup_sup [Nonempty ι] {f : ι → α} {a : α} :
    (⨆ i, f i) ⊔ a = ⨆ i, f i ⊔ a := by
  refine le_antisymm (sup_le ?_ ?_) <| ciSup_le fun i ↦ sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i ↦ le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right

lemma ciInf_inf [Nonempty ι] {f : ι → α} {a : α} :
    (⨅ i, f i) ⊓ a = ⨅ i, f i ⊓ a :=
  ciSup_sup (α := αᵒᵈ) ..

lemma ciSup_prod (f : ι × ι' → α) :
    ⨆ a, f a = ⨆ i, ⨆ i', f (i, i') :=
  _root_.ciSup_prod (bddAbove_range f)

lemma ciInf_prod (f : ι × ι' → α) :
    ⨅ a, f a = ⨅ i, ⨅ i', f (i, i') :=
  ciSup_prod (α := αᵒᵈ) f

end CCL

section CCLO

variable {α β ι : Type*} [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLattice β]
  [Finite ι] [Nonempty ι]

lemma map_iSup_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨆ i, g (f i) := by
  obtain ⟨j, hj⟩ : ∃ j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
  exact le_antisymm (le_ciSup_of_le j le_rfl) <|
    ciSup_le fun i ↦ hg (hs i) (hs j) (hj ▸ le_ciSup f i)

lemma map_iInf_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h ↦ hg hj hi h) hs

lemma map_iSup_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs

lemma map_iInf_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs

lemma map_iSup_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨆ i, f i) = ⨆ i, g (f i) :=
  map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i ↦ Set.mem_univ (f i))

lemma map_iInf_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h ↦ hg h

lemma map_iSup_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (β := βᵒᵈ) f hg

lemma map_iInf_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotone (β := βᵒᵈ) f hg

end CCLO

end Finite

end ciSup
