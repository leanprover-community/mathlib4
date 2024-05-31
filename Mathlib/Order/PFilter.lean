/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import Mathlib.Order.Ideal

#align_import order.pfilter from "leanprover-community/mathlib"@"740acc0e6f9adf4423f92a485d0456fc271482da"

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more structure,
such as a bottom element, a top element, or a join-semilattice structure.

- `Order.PFilter P`: The type of nonempty, downward directed, upward closed subsets of `P`.
               This is dual to `Order.Ideal`, so it simply wraps `Order.Ideal Pᵒᵈ`.
- `Order.IsPFilter P`: a predicate for when a `Set P` is a filter.

Note the relation between `Order/Filter` and `Order/PFilter`: for any type `α`,
`Filter α` represents the same mathematical object as `PFilter (Set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

open OrderDual

namespace Order

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ
#align order.pfilter Order.PFilter

variable {P : Type*}

/-- A predicate for when a subset of `P` is a filter. -/
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)
#align order.is_pfilter Order.IsPFilter

theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩
#align order.is_pfilter.of_def Order.IsPFilter.of_def

/-- Create an element of type `Order.PFilter` from a set satisfying the predicate
`Order.IsPFilter`. -/
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩
#align order.is_pfilter.to_pfilter Order.IsPFilter.toPFilter

namespace PFilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

instance [Inhabited P] : Inhabited (PFilter P) := ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : SetLike (PFilter P) P where
  coe F := toDual ⁻¹' F.dual.carrier
  coe_injective' := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk <| Ideal.ext h
#align order.pfilter.mem_coe SetLike.mem_coeₓ

theorem isPFilter : IsPFilter (F : Set P) := F.dual.isIdeal
#align order.pfilter.is_pfilter Order.PFilter.isPFilter

protected theorem nonempty : (F : Set P).Nonempty := F.dual.nonempty
#align order.pfilter.nonempty Order.PFilter.nonempty

theorem directed : DirectedOn (· ≥ ·) (F : Set P) := F.dual.directed
#align order.pfilter.directed Order.PFilter.directed

theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h
#align order.pfilter.mem_of_le Order.PFilter.mem_of_le

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h
#align order.pfilter.ext Order.PFilter.ext

@[trans]
theorem mem_of_mem_of_le {F G : PFilter P} (hx : x ∈ F) (hle : F ≤ G) : x ∈ G :=
  hle hx
#align order.pfilter.mem_of_mem_of_le Order.PFilter.mem_of_mem_of_le

/-- The smallest filter containing a given element. -/
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal (toDual p)⟩
#align order.pfilter.principal Order.PFilter.principal

@[simp]
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : PFilter P) ↔ toDual x ∈ I :=
  Iff.rfl
#align order.pfilter.mem_def Order.PFilter.mem_mk

@[simp]
theorem principal_le_iff {F : PFilter P} : principal x ≤ F ↔ x ∈ F :=
  Ideal.principal_le_iff (x := toDual x)
#align order.pfilter.principal_le_iff Order.PFilter.principal_le_iff

@[simp] theorem mem_principal : x ∈ principal y ↔ y ≤ x := Iff.rfl
#align order.pfilter.mem_principal Order.PFilter.mem_principal

theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp
#align order.pfilter.principal_le_principal_iff Order.PFilter.principal_le_principal_iff

-- defeq abuse
theorem antitone_principal : Antitone (principal : P → PFilter P) := fun _ _ =>
  principal_le_principal_iff.2
#align order.pfilter.antitone_principal Order.PFilter.antitone_principal

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : PFilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp] theorem top_mem : ⊤ ∈ F := Ideal.bot_mem _
#align order.pfilter.top_mem Order.PFilter.top_mem

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : PFilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F :=
  Ideal.sup_mem hx hy
#align order.pfilter.inf_mem Order.PFilter.inf_mem

@[simp]
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  Ideal.sup_mem_iff
#align order.pfilter.inf_mem_iff Order.PFilter.inf_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P] {F : PFilter P}

theorem sInf_gc :
    GaloisConnection (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  fun x F => by
  simp only [le_sInf_iff, SetLike.mem_coe]
  rfl
#align order.pfilter.Inf_gc Order.PFilter.sInf_gc

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def infGi :
    GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  sInf_gc.toGaloisCoinsertion fun _ => sInf_le <| mem_principal.2 le_rfl
#align order.pfilter.Inf_gi Order.PFilter.infGi

end CompleteSemilatticeInf

end PFilter

end Order
