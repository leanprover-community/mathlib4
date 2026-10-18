/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Topology.Compactness.CompactSystem

/-! # Cylinders with closed compact bases

We define the set of all cylinders with closed compact bases. Those sets play a role in the
proof of Kolmogorov's extension theorem.

## Main definitions

* `closedCompactCylinders X`: the set of all cylinders of `Π i, X i` based on closed compact sets.
* `compactClosedSquareCylinders X`: the set of all cylinders of `Π i, X i` based on products of
  closed compact sets.

## Main statements

* `mem_measurableCylinders_of_mem_closedCompactCylinders`: in a topological space with second
  countable topology and measurable open sets, a set in `closedCompactCylinders X` is a measurable
  cylinder.
* `isCompactSystem_closedCompactCylinders`: cylinders with compact closed bases form a compact
  system.

-/

@[expose] public section

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
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
noncomputable def closedCompactCylinders.set (ht : t ∈ closedCompactCylinders X) :
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

variable (X) in
/-- Cylinders with compact closed bases form a compact system. -/
theorem isCompactSystem_closedCompactCylinders : IsCompactSystem (closedCompactCylinders X) := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC h_nonempty ↦ ?_
  classical
  let J n := closedCompactCylinders.finset (hC n)
  let K n := closedCompactCylinders.set (hC n)
  have hC_eq n : C n = cylinder (J n) (K n) := closedCompactCylinders.eq_cylinder (hC n)
  have hC_closed n : IsClosed (C n) := by
    rw [hC_eq]
    exact (closedCompactCylinders.isClosed (hC n)).preimage (Finset.continuous_restrict _)
  choose y hy using h_nonempty
  -- `T i` is the projection on coordinate `i` of the base of the first cylinder that depends on
  -- `i`. The points of the finite intersections can be modified to belong to the compact `pi T`.
  let T : ∀ i, Set (X i) := fun i ↦
    if h : ∃ n, i ∈ J n then (fun x ↦ x ⟨i, Nat.find_spec h⟩) '' K (Nat.find h) else {y 0 i}
  have hT_compact i : IsCompact (T i) := by
    simp only [T]
    split_ifs with h
    · exact (closedCompactCylinders.isCompact (hC _)).image (continuous_apply _)
    · exact isCompact_singleton
  have h_mem_T {i} (h : ∃ n, i ∈ J n) {x} (hx : x ∈ C (Nat.find h)) : x i ∈ T i := by
    simp only [T, h, ↓reduceDIte]
    rw [hC_eq, mem_cylinder] at hx
    exact ⟨_, hx, rfl⟩
  refine ((isCompact_univ_pi hT_compact).inter_iInter_nonempty C hC_closed fun u ↦ ?_).mono
    inter_subset_right
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ u, n ≤ N := ⟨u.sup id, fun n hn ↦ Finset.le_sup (f := id) hn⟩
  let z : Π i, X i := fun i ↦ if ∃ n ≤ N, i ∈ J n then y N i
    else if h : ∃ n, i ∈ J n then y (Nat.find h) i else y 0 i
  refine ⟨z, fun i _ ↦ ?_, mem_iInter₂.mpr fun n hn ↦ ?_⟩
  · simp only [z]
    split_ifs with h₁ h₂
    · obtain ⟨n, hnN, hn⟩ := h₁
      exact h_mem_T ⟨n, hn⟩ (mem_dissipate.mp (hy N) _ ((Nat.find_min' _ hn).trans hnN))
    · exact h_mem_T h₂ (mem_dissipate.mp (hy _) _ le_rfl)
    · simp [T, h₂]
  · have : (J n).restrict z = (J n).restrict (y N) := by ext; simp [z]; grind
    rw [hC_eq, mem_cylinder, this, ← mem_cylinder, ← hC_eq]
    exact mem_dissipate.mp (hy N) _ (hN n hn)

end MeasureTheory
