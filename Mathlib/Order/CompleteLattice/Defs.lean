/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.SetNotation

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

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

instance OrderDual.supSet (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(sInf : Set α → α)⟩

instance OrderDual.infSet (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(sSup : Set α → α)⟩

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Any element of a set is less than the set supremum. -/
  le_sSup : ∀ s, ∀ a ∈ s, a ≤ sSup s
  /-- Any upper bound is more than the set supremum. -/
  sSup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → sSup s ≤ a

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

theorem le_sSup : a ∈ s → a ≤ sSup s :=
  CompleteSemilatticeSup.le_sSup s a

theorem sSup_le : (∀ b ∈ s, b ≤ a) → sSup s ≤ a :=
  CompleteSemilatticeSup.sSup_le s a

theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  ⟨fun _ ↦ le_sSup, fun _ ↦ sSup_le⟩

lemma isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a :=
  ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq

theorem le_sSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_sSup hb)

@[gcongr]
theorem sSup_le_sSup (h : s ⊆ t) : sSup s ≤ sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h

@[simp]
theorem sSup_le_iff : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_sSup s)

theorem le_sSup_iff : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

theorem le_iSup_iff {s : ι → α} : a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]

end

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeInf (α : Type*) extends PartialOrder α, InfSet α where
  /-- Any element of a set is more than the set infimum. -/
  sInf_le : ∀ s, ∀ a ∈ s, sInf s ≤ a
  /-- Any lower bound is less than the set infimum. -/
  le_sInf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ sInf s

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

theorem sInf_le : a ∈ s → sInf s ≤ a :=
  CompleteSemilatticeInf.sInf_le s a

theorem le_sInf : (∀ b ∈ s, a ≤ b) → a ≤ sInf s :=
  CompleteSemilatticeInf.le_sInf s a

theorem isGLB_sInf (s : Set α) : IsGLB s (sInf s) :=
  ⟨fun _ => sInf_le, fun _ => le_sInf⟩

lemma isGLB_iff_sInf_eq : IsGLB s a ↔ sInf s = a :=
  ⟨(isGLB_sInf s).unique, by rintro rfl; exact isGLB_sInf _⟩

alias ⟨IsGLB.sInf_eq, _⟩ := isGLB_iff_sInf_eq

theorem sInf_le_of_le (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (sInf_le hb) h

@[gcongr]
theorem sInf_le_sInf (h : s ⊆ t) : sInf t ≤ sInf s :=
  (isGLB_sInf s).mono (isGLB_sInf t) h

@[simp]
theorem le_sInf_iff : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_sInf s)

theorem sInf_le_iff : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_sInf hb) h, fun hb => hb _ fun _ => sInf_le⟩

theorem iInf_le_iff {s : ι → α} : iInf s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [iInf, sInf_le_iff, lowerBounds]

end

instance {α : Type*} [CompleteSemilatticeInf α] : CompleteSemilatticeSup αᵒᵈ where
  le_sSup := @CompleteSemilatticeInf.sInf_le α _
  sSup_le := @CompleteSemilatticeInf.le_sInf α _

instance {α : Type*} [CompleteSemilatticeSup α] : CompleteSemilatticeInf αᵒᵈ where
  le_sInf := @CompleteSemilatticeSup.sSup_le α _
  sInf_le := @CompleteSemilatticeSup.le_sSup α _


/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
    CompleteSemilatticeInf α, BoundedOrder α

/-- Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  min := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
  le_top a := (isGLB_sInf ∅).2 <| by simp
  max a b := sInf { x : α | a ≤ x ∧ b ≤ x }
  min a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
  inf_le_right _ _ := (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf_le_left _ _ := (isGLB_sInf _).1 <| mem_insert _ _
  sup_le a b c hac hbc := (isGLB_sInf _).1 <| by simp [*]
  le_sup_left _ _ := (isGLB_sInf _).2 fun _ => And.left
  le_sup_right _ _ := (isGLB_sInf _).2 fun _ => And.right
  le_sInf s _ ha := (isGLB_sInf s).2 ha
  sInf_le s _ ha := (isGLB_sInf s).1 ha
  sSup s := sInf (upperBounds s)
  le_sSup s _ ha := (isGLB_sInf (upperBounds s)).2 fun _ hb => hb ha
  sSup_le s _ ha := (isGLB_sInf (upperBounds s)).1 ha

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
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
  min := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
  bot_le x := (isLUB_sSup ∅).2 <| by simp
  max a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
  le_sup_left _ _ := (isLUB_sSup _).1 <| mem_insert _ _
  le_sup_right _ _ := (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
  min a b := sSup { x | x ≤ a ∧ x ≤ b }
  le_inf a b c hab hac := (isLUB_sSup _).1 <| by simp [*]
  inf_le_left _ _ := (isLUB_sSup _).2 fun _ => And.left
  inf_le_right _ _ := (isLUB_sSup _).2 fun _ => And.right
  sInf s := sSup (lowerBounds s)
  sSup_le s _ ha := (isLUB_sSup s).2 ha
  le_sSup s _ ha := (isLUB_sSup s).1 ha
  sInf_le s _ ha := (isLUB_sSup (lowerBounds s)).2 fun _ hb => hb ha
  le_sInf s _ ha := (isLUB_sSup (lowerBounds s)).1 ha

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
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
  __ := instBoundedOrder α
  le_sSup := @CompleteLattice.sInf_le α _
  sSup_le := @CompleteLattice.le_sInf α _
  sInf_le := @CompleteLattice.le_sSup α _
  le_sInf := @CompleteLattice.sSup_le α _

instance instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

end OrderDual

open OrderDual

section

section OrderDual

@[simp]
theorem toDual_sSup [SupSet α] (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl

@[simp]
theorem toDual_sInf [InfSet α] (s : Set α) : toDual (sInf s) = sSup (ofDual ⁻¹' s) :=
  rfl

@[simp]
theorem ofDual_sSup [InfSet α] (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl

@[simp]
theorem ofDual_sInf [SupSet α] (s : Set αᵒᵈ) : ofDual (sInf s) = sSup (toDual ⁻¹' s) :=
  rfl

@[simp]
theorem toDual_iSup [SupSet α] (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl

@[simp]
theorem toDual_iInf [InfSet α] (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl

@[simp]
theorem ofDual_iSup [InfSet α] (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl

@[simp]
theorem ofDual_iInf [SupSet α] (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl

end OrderDual

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s : Set α} {a b : α}

theorem lt_sSup_iff : b < sSup s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_sSup s

theorem sInf_lt_iff : sInf s < b ↔ ∃ a ∈ s, a < b :=
  isGLB_lt_iff <| isGLB_sInf s

theorem sSup_eq_top : sSup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h _ hb => lt_sSup_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨_, ha, h⟩ := h _ h'
        (h.trans_le <| le_sSup ha).false⟩

theorem sInf_eq_bot : sInf s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @sSup_eq_top αᵒᵈ _ _

theorem lt_iSup_iff {f : ι → α} : a < iSup f ↔ ∃ i, a < f i :=
  lt_sSup_iff.trans exists_range_iff

theorem iInf_lt_iff {f : ι → α} : iInf f < a ↔ ∃ i, f i < a :=
  sInf_lt_iff.trans exists_range_iff

theorem lt_biSup_iff {s : Set β} {f : β → α} : a < ⨆ i ∈ s, f i ↔ ∃ i ∈ s, a < f i := by
  simp [lt_iSup_iff]

theorem biInf_lt_iff {s : Set β} {f : β → α} : ⨅ i ∈ s, f i < a ↔ ∃ i ∈ s, f i < a := by
  simp [iInf_lt_iff]

end CompleteLinearOrder

end
