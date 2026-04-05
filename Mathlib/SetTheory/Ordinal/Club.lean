/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.Order.DirSupClosed

/-!
# Club sets

A subset of a well-ordered type `α` is called a club set when it is closed in the order topology and
cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and unbounded;
hence the name.

## Implementation notes

To avoid importing topology, we spell out the closure property using `DirSupClosed`. For any type
equipped with the Scott-Hausdorff topology (which includes well-orders with the order topology),
`DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

@[expose] public section

universe u

open Cardinal

structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  dirSupClosed : DirSupClosed s
  isCofinal : IsCofinal s

variable {α : Type*} {s t : Set α} {x : α} [LinearOrder α]

-- This is in another PR.
private theorem DirSupClosed.union (hs : DirSupClosed s) (ht : DirSupClosed t) :
    DirSupClosed (s ∪ t) :=
  sorry

@[simp]
private theorem DirSupClosed.of_isEmpty [IsEmpty α] (s : Set α) : DirSupClosed s :=
  fun _ _ ⟨a, _⟩ ↦ isEmptyElim a

@[simp]
theorem IsClub.of_isEmpty [IsEmpty α] (s : Set α) : IsClub s :=
  ⟨.of_isEmpty s, .of_isEmpty s⟩

theorem IsClub.univ : IsClub (.univ (α := α)) :=
  ⟨.univ, .univ⟩

theorem IsClub.union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t) :=
  ⟨.union hs.dirSupClosed ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩

theorem IsClub.isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (Std.Total.directedOn _) hx

theorem IsClub.csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t ∈ s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

variable [WellFoundedLT α]

theorem IsClub.sInter {s : Set (Set α)} (hα : ℵ₀ < Order.cof α) (hsα : #s < Order.cof α)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  have := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, fun a ↦ ?_⟩
  choose f hf using fun x : s ↦ (hs _ x.2).isCofinal
  let g : ℕ → α := Nat.rec a fun _ IH ↦ sSup (.range (f · IH))
  sorry

namespace Ordinal

protected theorem isClub_sInter {s : Set (Set Ordinal)} [Small.{u} s] (hs : ∀ x ∈ s, IsClub x) :
    IsClub (⋂₀ s) := by
  refine .sInter ?_ ?_ hs <;> simp
