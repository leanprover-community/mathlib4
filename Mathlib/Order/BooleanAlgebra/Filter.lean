/-
Copyright (c) 2023 Sam van Gool, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Filippo A. E. Nuccio
-/

import Mathlib.Order.BoundedOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.UpperLower.Basic



/-! # Filter -/

namespace BoundedLattice

structure Filter (α : Type*) [Lattice α] [BoundedOrder α] where
  /- The set of elements that belong to the filter. -/
  elements : Set α
  /- The top belongs to any filter. -/
  top_element : ⊤ ∈ elements
  /- If an element belongs to a filter, then any larger element belongs to the filter as well. -/
  upper_set : IsUpperSet elements
  /- If two elements belong to a filter, then their infimum belongs to the filter as well. -/
  inf_closed {x y} : x ∈ elements → y ∈ elements → x ⊓ y ∈ elements

-- theorem SetFilterIffLatticeFilter

def filter_of_powersetlattice_filter (X : Type*) (F : Filter (Set X))
  : _root_.Filter X := by sorry

def powersetlattice_filter_of_filter (X : Type*) (F : _root_.Filter X) : Filter (Set X) := by sorry


@[mk_iff]
structure IsFilter {α} [Lattice α] [BoundedOrder α] (F : Set α) : Prop where
  /-- The filter is an up-set. -/
  IsUpperSet : IsUpperSet F
  /-- The filter contains top. -/
  ContainsTop : ⊤ ∈ F
  /-- The filter is closed under binary infima. -/
  IsInfClosed : ∀ x y : α, x ∈ F → y ∈ F → x ⊓ y ∈ F


-- def filter_as_latticefilter (X : Type*) (F : _root_.Filter X) : Filter (set X) := by sorry

theorem filter_is_latticefilter (X : Type*)  (F : _root_.Filter X) : IsFilter F.1 := by sorry

section Hom


-- Lattice filters are exactly the inverse images of `true` under morphisms to the two-element
-- lattice which preserve finitary infima. This fact is encoded as follows.
-- When `F` is a filter in a lattice `α`, `F.elements` is of type `Set α`, which means `α → Prop`.
-- That map is an instance of `InfTopHom`.
def latticefilter_as_inftophom (α : Type*) [Lattice α] [BoundedOrder α] (F : Filter α) :
  InfTopHom α Prop := by sorry --use  F.elements

-- TODO: use InfTopHomClass

theorem inftophom_is_latticefilter  {α : Type*} [Lattice α] [BoundedOrder α]
  (f : InfTopHom α Prop) : IsFilter (f.1.1 : Set α) := by sorry

-- def inftophom_as_latticefilter (f : Set α) [InfTopHom f] : BoundedLattice.Filter α := by sorry

-- [@simp]
-- theorem mem_latticefilter_of_inftophom (f : Set α) [InfTopHom f] : x ∈ (inftophom_as_latticefilter f).1 ↔ x ∈ f  := by sorry

-- [@ext]
-- theorem eq_latticefilter_of_inftophom (f : Set α) [InfTopHom f] : (inftophom_as_latticefilter f).1 = f  := by sorry

end Hom

end BoundedLattice

namespace BoundedLatticeHom

open BoundedLattice

variable (α : Type*) [Lattice α] [BoundedOrder α]

structure Primefilter extends BoundedLattice.Filter α where
  protected prime {x y} : x ⊔ y ∈ elements → (x ∈ elements ∨ y ∈ elements)
  proper : ¬ (⊥ ∈ elements)


@[mk_iff]
structure IsPrimefilter {α} [Lattice α] [BoundedOrder α] (F : BoundedLattice.Filter α) : Prop where
  IsPrime : ∀ x y, x ⊔ y ∈ F.elements → (x ∈ F.elements ∨ y ∈ F.elements)
  IsProper : ¬ (⊥ ∈ F.elements)

/- As before, a set `f` of elements of a lattice `α` is a prime filter if and only if
 `f`, viewed as a function `α → Prop`, is a bounded lattice homomorphism. -/
theorem latticehom_is_primefilter (f : BoundedLatticeHom α Prop) : IsPrimefilter
  (inftophom_is_latticefilter (f : InfTopHom α Prop)) := by sorry

def latticehom_as_primefilter (f : Set α) [BoundedLatticeHom f] : Lattice.Primefilter α := by sorry

instance instTopologicalSpace (α : Type*) [Lattice α] [BoundedOrder α] : TopologicalSpace (Primefilter α) := by sorry

def stone_map (α : Type*) [Lattice α] [BoundedOrder α] : α → Set (Primefilter α) := fun a ↦ fun x ↦ a ∈ x

theorem stone_map_to_compact : ∀a, IsCompact (stone_map a) := by sorry

theorem stone_map_to_open : ∀a, IsOpen (stone_map a) := by sorry

instance instCompactOpen (a : α) : (Primefilter α).CompactOpens := {
  carrier := stone_map a
  isCompact' := stone_map_to_compact
  isOpen' := stone_map_to_open
}

instance instBoundedLatticeHom (α : Type*) [Lattice α] [BoundedOrder α] : BoundedLatticeHom (stone_map α)  := by sorry

-- check that it does not create double lattice structure on α
theorem stone_map_injective (α : Type*) [Lattice α] [BoundedOrder α] [DistribLattice α] : Injective (stone_map α) := by sorry

def distributive_of_stone_map_injective (α : Type*) [Lattice α] [BoundedOrder α] (h : Injective (stone_map α)) : DistribLattice α := by sorry


end BoundedLatticeHom
