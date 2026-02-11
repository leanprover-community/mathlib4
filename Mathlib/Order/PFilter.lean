/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
module

public import Mathlib.Order.Ideal

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

@[expose] public section

open OrderDual

namespace Order

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ

variable {P : Type*}

/-- A predicate for when a subset of `P` is a filter. -/
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)

theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F := by
  refine ⟨fun x y h hb => mem_of_le h hb, ?_, fun a ha b hb => ?_⟩
  · obtain ⟨a, ha⟩ := nonempty
    exact ⟨toDual a, ha⟩
  · obtain ⟨c, hc, hca, hcb⟩ := directed (ofDual a) ha (ofDual b) hb
    exact ⟨toDual c, hc, hca, hcb⟩

/-- Create an element of type `Order.PFilter` from a set satisfying the predicate
`Order.IsPFilter`. -/
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩

namespace PFilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

instance [Inhabited P] : Inhabited (PFilter P) := ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : SetLike (PFilter P) P where
  coe F := toDual ⁻¹' F.dual.carrier
  coe_injective' := by
    intro ⟨d₁⟩ ⟨d₂⟩ h
    congr 1; apply Ideal.ext; ext x
    change x ∈ d₁.carrier ↔ x ∈ d₂.carrier
    have := Set.ext_iff.mp h (ofDual x)
    simp only [Set.mem_preimage, toDual_ofDual] at this
    exact this

instance : PartialOrder (PFilter P) := .ofSetLike (PFilter P) P

@[simp] theorem mem_dual {F : PFilter P} {x : P} : toDual x ∈ F.dual ↔ x ∈ F := by
  cases F; exact Iff.rfl

theorem isPFilter : IsPFilter (F : Set P) := by
  have h := F.dual.isIdeal
  refine ⟨fun x y hxy hy => ?_, ?_, fun a ha b hb => ?_⟩
  · simp only [Set.mem_preimage] at hy ⊢
    exact h.IsLowerSet hxy hy
  · obtain ⟨a, ha⟩ := h.Nonempty
    exact ⟨a, by simp only [Set.mem_preimage]; exact ha⟩
  · simp only [Set.mem_preimage] at ha hb ⊢
    exact h.Directed a ha b hb

protected theorem nonempty : (F : Set P).Nonempty := by
  obtain ⟨a, ha⟩ := F.dual.nonempty
  exact ⟨ofDual a, ha⟩

theorem directed : DirectedOn (· ≥ ·) (F : Set P) := by
  intro a ha b hb
  have hd := F.dual.directed
  obtain ⟨c, hc, hca, hcb⟩ := hd (toDual a) ha (toDual b) hb
  exact ⟨ofDual c, hc, hca, hcb⟩

theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h hx => by
  rw [← mem_dual] at hx ⊢
  exact F.dual.lower h hx

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h

@[trans]
theorem mem_of_mem_of_le {F G : PFilter P} (hx : x ∈ F) (hle : F ≤ G) : x ∈ G :=
  hle hx

/-- The smallest filter containing a given element. -/
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal (toDual p)⟩

@[simp]
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : PFilter P) ↔ toDual x ∈ I :=
  Iff.rfl

@[simp] theorem mem_principal : x ∈ principal y ↔ y ≤ x :=
  Ideal.mem_principal

@[simp]
theorem principal_le_iff {F : PFilter P} : principal x ≤ F ↔ x ∈ F := by
  simp only [SetLike.le_def]
  constructor
  · intro h; exact h (mem_principal.mpr le_rfl)
  · intro hx y hy; exact mem_of_le (mem_principal.mp hy) hx

theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp

-- defeq abuse
theorem antitone_principal : Antitone (principal : P → PFilter P) := fun _ _ =>
  principal_le_principal_iff.2

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : PFilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp] theorem top_mem : ⊤ ∈ F := by
  rw [← mem_dual]
  exact Ideal.bot_mem _

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F x hx := by
    rw [← mem_dual] at hx ⊢
    exact (bot_le : (⊥ : Ideal Pᵒᵈ) ≤ F.dual) hx

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top F x hx := by
    rw [← mem_dual] at hx ⊢
    exact (le_top : F.dual ≤ (⊤ : Ideal Pᵒᵈ)) hx

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : PFilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F := by
  rw [← mem_dual] at hx hy ⊢
  exact Ideal.sup_mem hx hy

@[simp]
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F := by
  simp only [← mem_dual]
  exact Ideal.sup_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P]

theorem sInf_gc :
    GaloisConnection (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def infGi :
    GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  sInf_gc.toGaloisCoinsertion fun _ => sInf_le <| mem_principal.2 le_rfl

end CompleteSemilatticeInf

end PFilter

end Order
