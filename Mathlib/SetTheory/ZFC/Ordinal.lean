/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Rank

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.

## TODO

- Define von Neumann ordinals.
- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `SetTheory/Ordinal/Arithmetic.lean`.
-/


universe u

variable {x y z : ZFSet.{u}}

open Order

namespace ZFSet

/-- A transitive set is one where every element is a subset. -/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
theorem empty_isTransitive : IsTransitive ∅ := fun y hy => (not_mem_empty y hy).elim

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x :=
  h y

theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion' fun z => _
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)

theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x :=
  ⟨fun h y hy => by
    rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩
    exact h.mem_trans hz' hz, fun H y hy z hz => H <| mem_sUnion_of_mem hz hy⟩

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h _ hy => mem_powerset.2 <| h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

/-- The von Neumann hierarchy is defined so that `vonNeumann o` is the union of the powerset of all
`vonNeumann a` for `a < o`. It satisfies the following properties:

- `vonNeumann_zero`: `vonNeumann 0 = ∅`
- `vonNeumann_succ`: `vonNeumann (succ a) = powerset (vonNeumann a)`
- `vonNeumann_of_isSuccPrelimit`: `IsSuccPrelimit a → vonNeumann a = ⋃ b < a, vonNeumann b` -/
noncomputable def vonNeumann (o : Ordinal) : ZFSet :=
  ⋃₀ range fun a : Set.Iio o ↦ powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (vonNeumann o) := by
  rw [vonNeumann]
  apply IsTransitive.sUnion'
  simp_rw [mem_range]
  rintro _ ⟨a, rfl⟩
  exact (isTransitive_vonNeumann a).powerset
termination_by o
decreasing_by exact a.2

theorem vonNeumann_mem_of_lt {a b : Ordinal} (h : a < b) : vonNeumann a ∈ vonNeumann b := by
  rw [vonNeumann, mem_sUnion]
  refine ⟨_, mem_range_self ⟨a, h⟩, ?_⟩
  rw [mem_powerset]

theorem vonNeumann_subset_of_le {a b : Ordinal} (h : a ≤ b) : vonNeumann a ⊆ vonNeumann b := by
  obtain rfl | h := h.eq_or_lt
  · rfl
  · exact (isTransitive_vonNeumann _).subset_of_mem (vonNeumann_mem_of_lt h)

theorem subset_vonNeumann {o : Ordinal} {x : ZFSet} : x ⊆ vonNeumann o ↔ rank x ≤ o := by
  rw [vonNeumann, rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_sUnion, mem_range]
    rintro z ⟨_, ⟨⟨a, rfl⟩, hz⟩⟩
    have := a.2
    rw [mem_powerset, subset_vonNeumann] at hz
    exact hz.trans_lt a.2
  · simp_rw [mem_sUnion, mem_range]
    have := hx hy
    refine ⟨_, Set.mem_range_self ⟨y.rank, this⟩, ?_⟩
    rw [mem_powerset, subset_vonNeumann]
termination_by o

theorem mem_vonNeumann {o : Ordinal} {x : ZFSet} : x ∈ vonNeumann o ↔ rank x < o := by
  rw [vonNeumann]
  simp_rw [mem_sUnion, mem_range]
  constructor
  · rintro ⟨_, ⟨⟨a, rfl⟩, h⟩⟩
    rw [mem_powerset] at h
    exact ((rank_mono h).trans (subset_vonNeumann.1 (subset_rfl))).trans_lt a.2
  · intro hx
    refine ⟨_, Set.mem_range_self ⟨x.rank, hx⟩, ?_⟩
    rw [mem_powerset, subset_vonNeumann]

@[simp]
theorem rank_vonNeumann (o : Ordinal) : rank (vonNeumann o) = o := by
  apply le_antisymm
  · rw [← subset_vonNeumann]
  · apply le_of_forall_lt
    intro a ha
    have := rank_lt_of_mem (vonNeumann_mem_of_lt ha)
    rwa [rank_vonNeumann] at this
termination_by o

@[simp]
theorem vonNeumann_zero : vonNeumann 0 = ∅ := by
  ext
  rw [vonNeumann]
  simp

@[simp]
theorem vonNeumann_succ (o : Ordinal) : vonNeumann (succ o) = powerset (vonNeumann o) := by
  ext
  rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_succ_iff]

@[simp]
theorem vonNeumann_of_isSuccPrelimit {o : Ordinal} (h : IsSuccPrelimit o) :
    vonNeumann o = (⋃₀ range fun a : Set.Iio o ↦ vonNeumann a : ZFSet) := by
  ext
  simpa [mem_vonNeumann] using h.lt_iff_forall_lt

end ZFSet
