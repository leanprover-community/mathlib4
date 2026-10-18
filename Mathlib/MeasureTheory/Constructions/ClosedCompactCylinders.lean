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
* `isCompactSystem_compactClosedSquareCylinders`: Compact and closed square cylinders form a
  compact system.
* `isCompactSystem_countableInfClosure_supClosure_compactClosedSquareCylinders`: Countable
  intersections of finite unions of compact and closed square cylinders form a compact system.
* `cylinder_mem_countableInfClosure_supClosure`: In a product of second-countable R₁ spaces, a
  cylinder with a compact closed base is a countable intersection of finite unions of compact and
  closed square cylinders.

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

section CompactClosedSquareCylinders

variable {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]

/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both closed and
compact for all `i ∈ s`. -/
def compactClosedSquareCylinders : Set (Set (Π i, X i)) :=
  MeasureTheory.squareCylinders fun i ↦ {t : Set (X i) | IsCompact t ∧ IsClosed t}

/-- Compact and closed square cylinders form a compact system. -/
theorem isCompactSystem_compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders X) := by
  refine (IsCompactSystem.pi fun i ↦ isCompactSystem_insert_univ_isCompact_isClosed (X i)).mono ?_
  rintro _ ⟨s, t, ht, rfl⟩
  classical
  exact ⟨fun i ↦ if i ∈ s then t i else univ, by grind⟩

/-- Countable intersections of finite unions of compact closed square cylinders (and of `∅`)
form a compact system. -/
theorem isCompactSystem_countableInfClosure_supClosure_compactClosedSquareCylinders :
    IsCompactSystem
      (countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders X)))) :=
  (isCompactSystem_compactClosedSquareCylinders X).insert_empty.supClosure.countableInfClosure

variable {X}

open MeasureTheory

/-- A cylinder whose base is a product of compact closed sets is a compact closed square
cylinder. -/
lemma cylinder_univ_pi_mem_compactClosedSquareCylinders {J : Finset ι}
    {t : ∀ j : J, Set (X j)} (ht_compact : ∀ j, IsCompact (t j))
    (ht_closed : ∀ j, IsClosed (t j)) :
    cylinder J (univ.pi t) ∈ compactClosedSquareCylinders X := by
  classical
  refine ⟨J, fun i ↦ if h : i ∈ J then t ⟨i, h⟩ else ∅, fun i _ ↦ ?_, ?_⟩
  · by_cases h : i ∈ J <;> simp [h, ht_compact, ht_closed]
  · ext x
    simpa [cylinder] using forall₂_congr fun i hi ↦ by simp [hi]

/-- A cylinder with a compact closed base is a countable intersection of finite unions of compact
closed square cylinders. -/
lemma cylinder_mem_countableInfClosure_supClosure [∀ i, SecondCountableTopology (X i)]
    [∀ i, R1Space (X i)] {J : Finset ι} {K : Set (Π j : J, X j)} (hK_compact : IsCompact K)
    (hK_closed : IsClosed K) :
    cylinder J K ∈
      countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders X))) := by
  classical
  -- `K` is contained in the box with compact closed sides `A j`
  let A : ∀ j : J, Set (X j) := fun j ↦ closure ((fun y ↦ y j) '' K)
  have hA_compact j : IsCompact (A j) := (hK_compact.image (continuous_apply j)).closure
  have hA_closed j : IsClosed (A j) := isClosed_closure
  have hKA : K ⊆ univ.pi A := fun y hy j _ ↦ subset_closure (mem_image_of_mem _ hy)
  -- the complement of `K` is a countable union of open boxes which do not meet `K`
  let 𝒰 : Set (∀ j : J, Set (X j)) := {u | (∀ j, IsOpen (u j)) ∧ Disjoint (univ.pi u) K}
  obtain ⟨T, hT𝒰, hT_count, hT⟩ := TopologicalSpace.isOpen_biUnion_countable 𝒰 (fun u ↦ univ.pi u)
    fun u hu ↦ isOpen_set_pi finite_univ fun j _ ↦ hu.1 j
  have hK_compl : Kᶜ = ⋃ u ∈ T, univ.pi u := by
    rw [hT]
    refine Subset.antisymm (fun y hy ↦ ?_)
      (iUnion₂_subset fun u hu ↦ subset_compl_iff_disjoint_right.mpr hu.2)
    obtain ⟨u, hu, hu_sub⟩ := isOpen_pi_iff'.mp hK_closed.isOpen_compl y hy
    exact mem_biUnion (x := u) ⟨fun j ↦ (hu j).1, subset_compl_iff_disjoint_right.mp hu_sub⟩
      fun j _ ↦ (hu j).2
  obtain rfl | hK := eq_or_ne K univ
  · refine subset_countableInfClosure (subset_supClosure (mem_insert_of_mem _ ?_))
    convert cylinder_univ_pi_mem_compactClosedSquareCylinders hA_compact hA_closed
    grind
  have _ : Nonempty T := by
    rw [nonempty_coe_sort]
    by_contra! rfl
    simp at hK_compl
    grind
  -- for each such box `univ.pi u`, `K` is covered by the boxes `B u j` for `j : J`, obtained by
  -- replacing the side `A j` by `A j \ u j`
  let B : (∀ j : J, Set (X j)) → J → ∀ k : J, Set (X k) :=
    fun u j k ↦ if k = j then A k \ u k else A k
  have hB_compact u (hu : u ∈ 𝒰) j k : IsCompact (B u j k) := by
    simp only [B]
    split_ifs
    exacts [(hA_compact k).diff (hu.1 k), hA_compact k]
  have hB_closed u (hu : u ∈ 𝒰) j k : IsClosed (B u j k) := by
    simp only [B]
    split_ifs
    exacts [(hA_closed k).sdiff (hu.1 k), hA_closed k]
  have hK_eq : K = ⋂ u : T, ⋃ j, univ.pi (B u j) := by
    refine Subset.antisymm (fun y hy ↦ mem_iInter.mpr fun u ↦ ?_) fun y hy ↦ ?_
    · have hyu : y ∉ univ.pi u.1 := fun h ↦ (hT𝒰 u.2).2.notMem_of_mem_left h hy
      simp only [mem_univ_pi, not_forall] at hyu
      obtain ⟨j, hj⟩ := hyu
      exact mem_iUnion.mpr ⟨j, fun k _ ↦ by grind⟩
    · by_contra hyK
      rw [← mem_compl_iff, hK_compl, mem_iUnion₂] at hyK
      obtain ⟨u, hu, hyu⟩ := hyK
      obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hy ⟨u, hu⟩)
      have hj' := hj j trivial
      grind
  -- conclude with closure properties
  have : Countable T := hT_count.to_subtype
  have h_eq : cylinder J K = ⋂ u : T, ⋃ j, cylinder J (univ.pi (B u j)) := by
    rw [hK_eq]
    simp [cylinder, preimage_iInter]
  rw [h_eq]
  refine iInf_mem_countableInfClosure fun u ↦ ?_
  exact supClosed_supClosure.iSup_mem (subset_supClosure (mem_insert _ _)) fun j ↦
    subset_supClosure (mem_insert_of_mem _ (cylinder_univ_pi_mem_compactClosedSquareCylinders
      (hB_compact u (hT𝒰 u.2) j) (hB_closed u (hT𝒰 u.2) j)))

end CompactClosedSquareCylinders

end MeasureTheory
