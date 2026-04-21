/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.SetNotation

/-!
# Definition of complete lattices

This file contains the definition of complete lattices with suprema/infima of arbitrary sets.

## Main definitions

* `sSup` and `sInf` are the supremum and the infimum of a set;
* `iSup (f : ι → α)` and `iInf (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `sSup` and `sInf` of the range of this function;
* class `CompleteLattice`: a bounded lattice such that `sSup s` is always the least upper boundary
  of `s` and `sInf s` is always the greatest lower boundary of `s`;
* class `CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

@[expose] public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

@[to_dual]
instance OrderDual.supSet (α) [h : InfSet α] : SupSet αᵒᵈ :=
  ⟨fun s ↦ h.sInf s⟩

@[to_dual]
instance OrderDual.orderSupSet (α) [LE α] [OrderInfSet α] : OrderSupSet αᵒᵈ where
  isLUB_sSup_of_isLUB _ _ := isGLB_sInf_of_isGLB (α := α)

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Every set has a least upper bound. -/
  isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[to_dual]
class CompleteSemilatticeInf (α : Type*) extends PartialOrder α, InfSet α where
  /-- Every set has a greatest lower bound. -/
  isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[to_dual]
theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  CompleteSemilatticeSup.isLUB_sSup _

@[to_dual]
instance (priority := 100) CompleteSemilatticeSup.toOrderSupSet [CompleteSemilatticeSup α] :
    OrderSupSet α where
  isLUB_sSup_of_isLUB _ _ _ := isLUB_sSup _

@[to_dual sInf_le]
theorem le_sSup (h : a ∈ s) : a ≤ sSup s :=
  (isLUB_sSup s).1 h

@[to_dual le_sInf]
theorem sSup_le (h : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_sSup s).2 h

@[to_dual]
lemma isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a :=
  ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

@[to_dual sInf_le_of_le]
theorem le_sSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_sSup hb)

@[to_dual (attr := gcongr)]
theorem sSup_le_sSup (h : s ⊆ t) : sSup s ≤ sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h

@[to_dual (attr := simp) le_sInf_iff]
theorem sSup_le_iff : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_sSup s)

@[to_dual sInf_le_iff]
theorem le_sSup_iff : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

@[to_dual iInf_le_iff]
theorem le_iSup_iff {s : ι → α} : a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]

end

@[to_dual]
instance {α : Type*} [CompleteSemilatticeInf α] : CompleteSemilatticeSup αᵒᵈ where
  isLUB_sSup := isGLB_sInf (α := α)

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
    CompleteSemilatticeInf α, BoundedOrder α

attribute [to_dual existing] CompleteLattice.toCompleteSemilatticeInf
attribute [to_dual self (reorder := toSupSet toInfSet, isLUB_sSup isGLB_sInf)] CompleteLattice.mk

-- Shortcut instance to ensure that the path
-- `CompleteLattice α → CompletePartialOrder α → PartialOrder α` isn't taken,
-- as it tricks `#min_imports` into believing `Order.CompletePartialOrder` is a necessary import.
-- See note [lower instance priority]
instance (priority := 100) CompleteLattice.toPartialOrder' [CompleteLattice α] : PartialOrder α :=
  inferInstance

/-- Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
@[implicit_reducible]
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
  le_top a := (isGLB_sInf ∅).2 <| by simp
  sup a b := sInf { x : α | a ≤ x ∧ b ≤ x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
  inf_le_right _ _ := (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf_le_left _ _ := (isGLB_sInf _).1 <| mem_insert _ _
  sup_le a b c hac hbc := (isGLB_sInf _).1 <| by simp [*]
  le_sup_left _ _ := (isGLB_sInf _).2 fun _ => And.left
  le_sup_right _ _ := (isGLB_sInf _).2 fun _ => And.right
  sSup s := sInf (upperBounds s)
  isGLB_sInf := isGLB_sInf
  isLUB_sSup s := isGLB_upperBounds.mp (isGLB_sInf _)

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
@[implicit_reducible]
def completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s

/-- Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
@[implicit_reducible]
def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
  bot_le x := (isLUB_sSup ∅).2 <| by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
  le_sup_left _ _ := (isLUB_sSup _).1 <| mem_insert _ _
  le_sup_right _ _ := (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf a b := sSup { x | x ≤ a ∧ x ≤ b }
  le_inf a b c hab hac := (isLUB_sSup _).1 <| by simp [*]
  inf_le_left _ _ := (isLUB_sSup _).2 fun _ => And.left
  inf_le_right _ _ := (isLUB_sSup _).2 fun _ => And.right
  sInf s := sSup (lowerBounds s)
  isLUB_sSup := isLUB_sSup
  isGLB_sInf s := isLUB_lowerBounds.mp (isLUB_sSup _)

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
@[implicit_reducible]
def completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s

/-- A complete linear order is a linear order whose lattice structure is complete. -/
-- Note that we do not use `extends LinearOrder α`,
-- and instead construct the forgetful instance manually.
class CompleteLinearOrder (α : Type*) extends CompleteLattice α, BiheytingAlgebra α, Ord α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

instance CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrder α where
  __ := i
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

namespace OrderDual

instance instCompleteLattice [CompleteLattice α] : CompleteLattice αᵒᵈ where

instance instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

end OrderDual

open OrderDual

section

section OrderDual

@[to_dual (attr := simp)]
theorem toDual_sSup [SupSet α] (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
theorem ofDual_sSup [InfSet α] (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
theorem toDual_iSup [SupSet α] (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl

@[to_dual (attr := simp)]
theorem ofDual_iSup [InfSet α] (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl

end OrderDual

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s : Set α} {a b : α}

@[to_dual sInf_lt_iff]
theorem lt_sSup_iff : b < sSup s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_sSup s

@[to_dual]
theorem sSup_eq_top : sSup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h _ hb => lt_sSup_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨_, ha, h⟩ := h _ h'
        (h.trans_le <| le_sSup ha).false⟩

@[to_dual iInf_lt_iff]
theorem lt_iSup_iff {f : ι → α} : a < iSup f ↔ ∃ i, a < f i :=
  lt_sSup_iff.trans exists_range_iff

@[to_dual]
theorem lt_biSup_iff {s : Set β} {f : β → α} : a < ⨆ i ∈ s, f i ↔ ∃ i ∈ s, a < f i := by
  simp [lt_iSup_iff]

end CompleteLinearOrder

end

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `SupSet` across an `Equiv`. -/
protected abbrev supSet [SupSet β] : SupSet α where
  sSup s := e.symm (⨆ a ∈ s, e a)

lemma supSet_def [SupSet β] (s : Set α) :
    letI := e.supSet
    sSup s = e.symm (⨆ a ∈ s, e a) := rfl

/-- Transfer `InfSet` across an `Equiv`. -/
protected abbrev infSet [InfSet β] : InfSet α where
  sInf s := e.symm (⨅ a ∈ s, e a)

lemma infSet_def [InfSet β] (s : Set α) :
    letI := e.infSet
    sInf s = e.symm (⨅ a ∈ s, e a) := rfl

end Equiv
