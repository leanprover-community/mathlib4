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

This file defines the von Neumann hierarchy of sets `V_ o`, which is recursively defined so that
`V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense that
`⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

open Order

namespace ZFSet

/-- The von Neumann hierarchy is defined so that `V_ o` is the union of the powersets of all
`V_ a` for `a < o`. It satisfies the following properties:

- `vonNeumann_zero`: `V_ 0 = ∅`
- `vonNeumann_succ`: `V_ (succ a) = powerset (V_ a)`
- `vonNeumann_of_isSuccPrelimit`: `IsSuccPrelimit a → V_ a = ⋃ b < a, V_ b`
-/
noncomputable def vonNeumann (o : Ordinal) : ZFSet :=
  ⋃₀ range fun a : Set.Iio o ↦ powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o) := by
  rw [vonNeumann]
  apply IsTransitive.sUnion'
  simp_rw [mem_range]
  rintro _ ⟨a, rfl⟩
  exact (isTransitive_vonNeumann a).powerset
termination_by o
decreasing_by exact a.2

private theorem vonNeumann_mem_of_lt {a b : Ordinal} (h : a < b) : V_ a ∈ V_ b := by
  rw [vonNeumann, mem_sUnion]
  refine ⟨_, mem_range_self ⟨a, h⟩, ?_⟩
  rw [mem_powerset]

private theorem vonNeumann_subset_of_le {a b : Ordinal} (h : a ≤ b) : V_ a ⊆ V_ b := by
  obtain rfl | h := h.eq_or_lt
  · rfl
  · exact (isTransitive_vonNeumann _).subset_of_mem (vonNeumann_mem_of_lt h)

theorem subset_vonNeumann {o : Ordinal} {x : ZFSet} : x ⊆ V_ o ↔ rank x ≤ o := by
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

theorem mem_vonNeumann {o : Ordinal} {x : ZFSet} : x ∈ V_ o ↔ rank x < o := by
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
theorem vonNeumann_mem_vonNeumann_iff {a b : Ordinal} : V_ a ∈ V_ b ↔ a < b := by
  simp [mem_vonNeumann]

@[simp]
theorem vonNeumann_subset_vonNeumann_iff {a b : Ordinal} : V_ a ⊆ V_ b ↔ a ≤ b := by
  simp [subset_vonNeumann]

theorem vonNeumann_strictMono : StrictMono vonNeumann :=
  strictMono_of_le_iff_le fun _ _ ↦ vonNeumann_subset_vonNeumann_iff.symm

theorem vonNeumann_injective : Function.Injective vonNeumann :=
  vonNeumann_strictMono.injective

@[simp]
theorem vonNeumann_inj {a b : Ordinal} : V_ a = V_ b ↔ a = b :=
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

theorem vonNeumann_of_isSuccPrelimit {o : Ordinal} (h : IsSuccPrelimit o) :
    V_ o = (⋃₀ range fun a : Set.Iio o ↦ vonNeumann a : ZFSet) := by
  ext
  simpa [mem_vonNeumann] using h.lt_iff_exists_lt

/-- Every set is in some element of the von Neumann hierarchy. -/
theorem exists_mem_vonNeumann (x : ZFSet) : ∃ o, x ∈ V_ o := by
  use succ (rank x)
  rw [mem_vonNeumann]
  exact lt_succ _

theorem iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ :=
  Class.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 <| exists_mem_vonNeumann x

theorem rank_def {x : ZFSet} {o : Ordinal} : rank x = o ↔ x ⊆ V_ o ∧ ∀ o' < o, ¬ x ⊆ V_ o' := by
  simp_rw [subset_vonNeumann, not_le, forall_lt_iff_le, le_antisymm_iff]

end ZFSet
