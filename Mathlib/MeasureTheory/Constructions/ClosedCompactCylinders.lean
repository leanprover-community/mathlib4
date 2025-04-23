/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! # Cylinders with closed compact bases

We define the set of all cylinders with closed compact bases. Those sets play a role in the
proof of Kolmogorov's extension theorem.

## Main definitions

* `closedCompactCylinders X`: the set of all cylinders of `Π i, X i` based on closed compact sets.

## Main statements

* `mem_measurableCylinders_of_mem_closedCompactCylinders`: in a topological space with second
  countable topology and measurable open sets, a set in `closedCompactCylinders X` is a measurable
  cylinder.

-/

open Set

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {t : Set (Π i, X i)}

variable (X) in
/-- The set of all cylinders based on closed compact sets. Note that such a set is closed, but
not compact in general (for instance, the whole space is always a closed compact cylinder). -/
def closedCompactCylinders : Set (Set (Π i, X i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

variable (X) in
theorem empty_mem_closedCompactCylinders : ∅ ∈ closedCompactCylinders X := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

theorem mem_closedCompactCylinders (t : Set (Π i, X i)) :
    t ∈ closedCompactCylinders X
      ↔ ∃ (s S : _), IsClosed S ∧ IsCompact S ∧ t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff, exists_prop]

/-- A finset `s` such that `t = cylinder s S`. `S` is given by `closedCompactCylinders.set`. -/
noncomputable def closedCompactCylinders.finset (ht : t ∈ closedCompactCylinders X) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

/-- A set `S` such that `t = cylinder s S`. `s` is given by `closedCompactCylinders.finset`. -/
def closedCompactCylinders.set (ht : t ∈ closedCompactCylinders X) :
    Set (Π i : closedCompactCylinders.finset ht, X i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

theorem closedCompactCylinders.isClosed (ht : t ∈ closedCompactCylinders X) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.1

theorem closedCompactCylinders.isCompact (ht : t ∈ closedCompactCylinders X) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.1

theorem closedCompactCylinders.eq_cylinder (ht : t ∈ closedCompactCylinders X) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.2

theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (Π i : s, X i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S ∈ closedCompactCylinders X := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

theorem mem_measurableCylinders_of_mem_closedCompactCylinders [∀ i, MeasurableSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] [∀ i, OpensMeasurableSpace (X i)]
    (ht : t ∈ closedCompactCylinders X) :
    t ∈ measurableCylinders X := by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

end MeasureTheory
