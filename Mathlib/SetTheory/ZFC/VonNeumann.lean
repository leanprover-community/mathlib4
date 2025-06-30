/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Knala Solomon
-/
import Mathlib.SetTheory.ZFC.Class
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.Rank

/-!
# Von Neumann hierarchy

This file defines the von Neumann hierarchy of sets `V_ o` for ordinal `o`, which is recursively
defined so that `V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense
that `⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

universe u

open Order

namespace ZFSet

/-- The von Neumann hierarchy is defined so that `V_ o` is the union of the powersets of all
`V_ a` for `a < o`. It satisfies the following properties:

- `vonNeumann_zero`: `V_ 0 = ∅`
- `vonNeumann_succ`: `V_ (succ a) = powerset (V_ a)`
- `vonNeumann_of_isSuccPrelimit`: `IsSuccPrelimit a → V_ a = ⋃ b < a, V_ b`
-/
noncomputable def vonNeumann (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃₀ range fun a : Set.Iio o ↦ powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

variable {a b o : Ordinal} {x : ZFSet.{u}}

theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o) := by
  rw [vonNeumann]
  refine IsTransitive.sUnion' fun x hx ↦ ?_
  obtain ⟨⟨a, _⟩, rfl⟩ := mem_range.1 hx
  exact (isTransitive_vonNeumann a).powerset
termination_by o

theorem vonNeumann_mem_of_lt (h : a < b) : V_ a ∈ V_ b := by
  rw [vonNeumann]; aesop

theorem vonNeumann_subset_of_le (h : a ≤ b) : V_ a ⊆ V_ b :=
  h.eq_or_lt.rec (by aesop) fun h ↦ isTransitive_vonNeumann _ _ <| vonNeumann_mem_of_lt h

theorem subset_vonNeumann {o : Ordinal} {x : ZFSet} : x ⊆ V_ o ↔ rank x ≤ o := by
  rw [rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_vonNeumann']
    rintro z ⟨a, ha, hz⟩
    exact (subset_vonNeumann.1 hz).trans_lt ha
  · rw [mem_vonNeumann']
    have := hx hy
    exact ⟨_, this, subset_vonNeumann.2 le_rfl⟩
termination_by o

theorem mem_vonNeumann {x : ZFSet} : x ∈ V_ o ↔ rank x < o := by
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
theorem rank_vonNeumann (o : Ordinal) : rank (V_ o) = o := by
  apply le_antisymm
  · rw [← subset_vonNeumann]
  · exact le_of_forall_lt fun a ha ↦ rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]
theorem vonNeumann_mem_vonNeumann_iff : V_ a ∈ V_ b ↔ a < b := by
  simp [mem_vonNeumann]

@[simp]
theorem vonNeumann_subset_vonNeumann_iff : V_ a ⊆ V_ b ↔ a ≤ b := by
  simp [subset_vonNeumann]

theorem vonNeumann_strictMono : StrictMono vonNeumann :=
  strictMono_of_le_iff_le (by simp)

theorem vonNeumann_injective : Function.Injective vonNeumann :=
  vonNeumann_strictMono.injective

@[simp]
theorem vonNeumann_inj : V_ a = V_ b ↔ a = b :=
  vonNeumann_injective.eq_iff

@[simp]
theorem vonNeumann_zero : V_ 0 = ∅ := by
  ext
  rw [vonNeumann]
  simp

@[simp]
theorem vonNeumann_succ (o : Ordinal) : V_ (succ o) = powerset (V_ o) := by
  ext
  rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_succ_iff]

theorem vonNeumann_of_isSuccPrelimit (h : IsSuccPrelimit o) :
    V_ o = (⋃₀ range fun a : Set.Iio o ↦ vonNeumann a : ZFSet) := by
  ext
  simpa [mem_vonNeumann] using h.lt_iff_exists_lt

/-- Every set is in some element of the von Neumann hierarchy. -/
theorem exists_mem_vonNeumann (x : ZFSet) : ∃ o, x ∈ V_ o :=
  ⟨succ x.rank, by simp [subset_vonNeumann]⟩

theorem iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ :=
  Class.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 <| exists_mem_vonNeumann x

end ZFSet
