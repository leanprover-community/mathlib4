/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet

! This file was ported from Lean 3 source module order.pfilter
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal Pᵒᵈ`.
- `order.is_pfilter P`: a predicate for when a `set P` is a filter.


Note the relation between `order/filter` and `order/pfilter`: for any
type `α`, `filter α` represents the same mathematical object as
`pfilter (set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/


namespace Order

variable {P : Type _}

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure Pfilter (P) [Preorder P] where
  dual : Ideal Pᵒᵈ
#align order.pfilter Order.Pfilter

/-- A predicate for when a subset of `P` is a filter. -/
def IsPfilter [Preorder P] (F : Set P) : Prop :=
  @IsIdeal Pᵒᵈ _ F
#align order.is_pfilter Order.IsPfilter

theorem IsPfilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPfilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, Nonempty, Directed⟩
#align order.is_pfilter.of_def Order.IsPfilter.of_def

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def IsPfilter.toPfilter [Preorder P] {F : Set P} (h : IsPfilter F) : Pfilter P :=
  ⟨h.toIdeal⟩
#align order.is_pfilter.to_pfilter Order.IsPfilter.toPfilter

namespace Pfilter

section Preorder

variable [Preorder P] {x y : P} (F s t : Pfilter P)

instance [Inhabited P] : Inhabited (Pfilter P) :=
  ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : Coe (Pfilter P) (Set P) :=
  ⟨fun F => F.dual.carrier⟩

/-- For the notation `x ∈ F`. -/
instance : Membership P (Pfilter P) :=
  ⟨fun x F => x ∈ (F : Set P)⟩

@[simp]
theorem mem_coe : x ∈ (F : Set P) ↔ x ∈ F :=
  iff_of_eq rfl
#align order.pfilter.mem_coe Order.Pfilter.mem_coe

theorem isPfilter : IsPfilter (F : Set P) :=
  F.dual.IsIdeal
#align order.pfilter.is_pfilter Order.Pfilter.isPfilter

theorem nonempty : (F : Set P).Nonempty :=
  F.dual.Nonempty
#align order.pfilter.nonempty Order.Pfilter.nonempty

theorem directed : DirectedOn (· ≥ ·) (F : Set P) :=
  F.dual.Directed
#align order.pfilter.directed Order.Pfilter.directed

theorem mem_of_le {F : Pfilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h
#align order.pfilter.mem_of_le Order.Pfilter.mem_of_le

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := by
  cases s
  cases t
  exact congr_arg _ (ideal.ext h)
#align order.pfilter.ext Order.Pfilter.ext

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : PartialOrder (Pfilter P) :=
  PartialOrder.lift coe ext

@[trans]
theorem mem_of_mem_of_le {F G : Pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
  Ideal.mem_of_mem_of_le
#align order.pfilter.mem_of_mem_of_le Order.Pfilter.mem_of_mem_of_le

/-- The smallest filter containing a given element. -/
def principal (p : P) : Pfilter P :=
  ⟨Ideal.principal p⟩
#align order.pfilter.principal Order.Pfilter.principal

@[simp]
theorem mem_def (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : Pfilter P) ↔ OrderDual.toDual x ∈ I :=
  Iff.rfl
#align order.pfilter.mem_def Order.Pfilter.mem_def

@[simp]
theorem principal_le_iff {F : Pfilter P} : principal x ≤ F ↔ x ∈ F :=
  Ideal.principal_le_iff
#align order.pfilter.principal_le_iff Order.Pfilter.principal_le_iff

@[simp]
theorem mem_principal : x ∈ principal y ↔ y ≤ x :=
  Ideal.mem_principal
#align order.pfilter.mem_principal Order.Pfilter.mem_principal

-- defeq abuse
theorem antitone_principal : Antitone (principal : P → Pfilter P) := by delta Antitone <;> simp
#align order.pfilter.antitone_principal Order.Pfilter.antitone_principal

theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp
#align order.pfilter.principal_le_principal_iff Order.Pfilter.principal_le_principal_iff

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : Pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp]
theorem top_mem : ⊤ ∈ F :=
  Ideal.bot_mem _
#align order.pfilter.top_mem Order.Pfilter.top_mem

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (Pfilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorder P] [OrderBot P] : OrderTop (Pfilter P)
    where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : Pfilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F :=
  Ideal.sup_mem hx hy
#align order.pfilter.inf_mem Order.Pfilter.inf_mem

@[simp]
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  Ideal.sup_mem_iff
#align order.pfilter.inf_mem_iff Order.Pfilter.inf_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P] {F : Pfilter P}

theorem infₛ_gc :
    GaloisConnection (fun x => OrderDual.toDual (principal x)) fun F =>
      infₛ (OrderDual.ofDual F : Pfilter P) :=
  fun x F => by
  simp
  rfl
#align order.pfilter.Inf_gc Order.Pfilter.infₛ_gc

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def infGi :
    GaloisCoinsertion (fun x => OrderDual.toDual (principal x)) fun F =>
      infₛ (OrderDual.ofDual F : Pfilter P)
    where
  choice F _ := infₛ (id F : Pfilter P)
  gc := infₛ_gc
  u_l_le s := infₛ_le <| mem_principal.2 <| le_refl s
  choice_eq _ _ := rfl
#align order.pfilter.Inf_gi Order.Pfilter.infGi

end CompleteSemilatticeInf

end Pfilter

end Order

