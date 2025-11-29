/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.ZFC.Class

/-!
# Von Neumann hierarchy

This file defines the von Neumann hierarchy of sets `V_ o` for ordinal `o`, which is recursively
defined so that `V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense
that `⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

@[expose] public section

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
  ⋃ a : Set.Iio o, powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

variable {a b o : Ordinal.{u}} {x : ZFSet.{u}}

lemma mem_vonNeumann' : x ∈ V_ o ↔ ∃ a < o, x ⊆ V_ a := by rw [vonNeumann]; simp

theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o) := by
  rw [vonNeumann]
  exact .iUnion fun ⟨a, _⟩ => (isTransitive_vonNeumann a).powerset
termination_by o

@[gcongr] theorem vonNeumann_mem_of_lt (h : a < b) : V_ a ∈ V_ b := by
  rw [vonNeumann]; aesop

@[gcongr] theorem vonNeumann_subset_of_le (h : a ≤ b) : V_ a ⊆ V_ b :=
  h.eq_or_lt.rec (by simp_all) fun h ↦ isTransitive_vonNeumann _ _ <| vonNeumann_mem_of_lt h

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

theorem subset_vonNeumann_self (x : ZFSet) : x ⊆ V_ (rank x) := by
  simp [subset_vonNeumann]

theorem mem_vonNeumann : x ∈ V_ o ↔ rank x < o := by
  simp_rw [mem_vonNeumann', subset_vonNeumann]
  exact ⟨fun ⟨a, h₁, h₂⟩ ↦ h₂.trans_lt h₁, by aesop⟩

theorem mem_vonNeumann_succ (x : ZFSet) : x ∈ V_ (succ (rank x)) := by
  simp [mem_vonNeumann]

/-- Every set is in some element of the von Neumann hierarchy. -/
theorem exists_mem_vonNeumann (x : ZFSet) : ∃ o, x ∈ V_ o :=
  ⟨_, mem_vonNeumann_succ x⟩

@[simp]
theorem rank_vonNeumann (o : Ordinal) : rank (V_ o) = o :=
  le_antisymm (by rw [← subset_vonNeumann]) <| le_of_forall_lt fun a ha ↦
    rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]
theorem vonNeumann_mem_vonNeumann_iff : V_ a ∈ V_ b ↔ a < b := by
  simp [mem_vonNeumann]

@[simp]
theorem vonNeumann_subset_vonNeumann_iff : V_ a ⊆ V_ b ↔ a ≤ b := by
  simp [subset_vonNeumann]

theorem mem_vonNeumann_of_subset {y : ZFSet} (h : x ⊆ y) (hy : y ∈ V_ o) : x ∈ V_ o := by
  rw [mem_vonNeumann] at *
  exact (rank_mono h).trans_lt hy

theorem vonNeumann_strictMono : StrictMono vonNeumann :=
  strictMono_of_le_iff_le (by simp)

theorem vonNeumann_injective : Function.Injective vonNeumann :=
  vonNeumann_strictMono.injective

@[simp]
theorem vonNeumann_inj : V_ a = V_ b ↔ a = b :=
  vonNeumann_injective.eq_iff

@[gcongr]
alias ⟨_, _root_.GCongr.ZFSet.vonNeumann_inj⟩ := vonNeumann_inj

@[simp]
theorem vonNeumann_zero : V_ 0 = ∅ :=
  (eq_empty _).2 (by simp [mem_vonNeumann])

@[simp]
theorem vonNeumann_succ (o : Ordinal) : V_ (succ o) = powerset (V_ o) :=
  ext fun z ↦ by rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_succ_iff]

theorem vonNeumann_of_isSuccPrelimit (h : IsSuccPrelimit o) :
    V_ o = ⋃ a : Set.Iio o, vonNeumann a :=
  ext fun z ↦ by simpa [mem_vonNeumann] using h.lt_iff_exists_lt

theorem iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ :=
  Class.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 <| exists_mem_vonNeumann x

theorem _root_.Ordinal.toZFSet_subset_vonNeumann (o : Ordinal) : o.toZFSet ⊆ V_ o := by
  simp [subset_vonNeumann]

lemma _root_.Ordinal.card_le_card_vonNeumann (o : Ordinal) : o.card ≤ card (V_ o) := by
  simpa using card_mono o.toZFSet_subset_vonNeumann

open Cardinal in
theorem card_vonNeumann (o : Ordinal.{u}) : card (V_ o) = preBeth o := by
  induction o using Ordinal.limitRecOn with
  | zero =>
    rw [vonNeumann_zero, card_empty, preBeth_zero]
  | succ o ih =>
    rw [vonNeumann_succ, card_powerset, ih, preBeth_succ]
  | limit o ho ih =>
    simp_rw [preBeth_limit ho.isSuccPrelimit, ← fun i : Set.Iio o => ih i i.2,
      vonNeumann_of_isSuccPrelimit ho.isSuccPrelimit]
    apply iSup_card_le_card_iUnion.antisymm'
    rw [← lift_le.{u + 1}]
    apply lift_card_iUnion_le_sum_card.trans
    refine (sum_eq_lift_iSup_of_lift_mk_le_lift_iSup ?_ ?_).le
    · rw [Ordinal.mk_Iio_ordinal, ← lift_aleph0.{u + 1, u}, lift_le, Ordinal.aleph0_le_card]
      exact Ordinal.omega0_le_of_isSuccLimit ho
    · rw [Ordinal.mk_Iio_ordinal, lift_lift, lift_le]
      by_contra! h
      refine (⨆ i : Set.Iio o, (V_ ↑i).card).card_ord.not_lt <|
        (Ordinal.card_le_card_vonNeumann _).trans_lt <| (cantor _).trans_le ?_
      rw [← card_powerset, ← vonNeumann_succ]
      refine le_ciSup (bddAbove_of_small _) (⟨_, ho.succ_lt ?_⟩ : Set.Iio o)
      exact (ord_card_le _).trans_lt' (ord_strictMono h)

end ZFSet
