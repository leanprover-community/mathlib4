/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

@[expose] public section

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex
variable [WellFoundedLT ι]

private def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i

@[no_expose]
instance : InfSet (Πₗ i, α i) where
  sInf s := toLex (inf s)

theorem sInf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j < i, e j = sInf s j}, e.1 i := by
  simp [sInf, inf]

theorem sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sInf s j) : sInf s i ≤ e i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

theorem le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i := by
  rw [sInf_apply]
  apply le_sInf
  grind

private theorem sInf_le {s : Set (Πₗ i, α i)} {e : Πₗ i, α i}
    (he : e ∈ s) : sInf s ≤ e := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  exact ha.2.not_ge (sInf_apply_le he ha.1)

private theorem le_sInf {s : Set (Πₗ i, α i)} {e : Πₗ i, α i}
    (h : ∀ b ∈ s, e ≤ b) : e ≤ sInf s := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  refine ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ apply_le_of_toLex (h f hf) ?_
  simp_all

private def sup [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨆ e : {e ∈ s | ∀ j < i, e j = sup s j}, e.1 i
termination_by wellFounded_lt.wrap i

@[no_expose]
instance : SupSet (Πₗ i, α i) where
  sSup s := toLex (sup s)

theorem sSup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j < i, e j = sSup s j}, e.1 i := by
  simp [sSup, sup]

theorem le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sSup s j) : e i ≤ sSup s i := by
  rw [sSup_apply]
  exact le_sSup ⟨⟨e, he, h⟩, rfl⟩

theorem sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i := by
  rw [sSup_apply]
  apply sSup_le
  grind

private theorem le_sSup {s : Set (Πₗ i, α i)} {e : Πₗ i, α i}
    (he : e ∈ s) : e ≤ sSup s := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  exact ha.2.not_ge (le_sSup_apply he fun j hj ↦ (ha.1 j hj).symm)

private theorem sSup_le {s : Set (Πₗ i, α i)} {e : Πₗ i, α i}
    (h : ∀ b ∈ s, b ≤ e) : sSup s ≤ e := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  refine ha.2.not_ge <| sSup_apply_le fun f hf hf' ↦ apply_le_of_toLex (h f hf) ?_
  simp_all

noncomputable instance completeLattice : CompleteLattice (Πₗ i, α i) where
  sInf_le _ _ := by exact sInf_le
  le_sInf _ _ := by exact le_sInf
  le_sSup _ _ := by exact le_sSup
  sSup_le _ _ := by exact sSup_le

noncomputable instance : CompleteLinearOrder (Πₗ i, α i) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Lex

/-! ### Colexicographic ordering -/

namespace Colex
variable [WellFoundedGT ι]

private def inf [WellFoundedGT ι] (s : Set (Colex ((i : ι) → α i))) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j > i, e j = inf s j}, e.1 i
termination_by wellFounded_gt.wrap i

@[no_expose]
instance : InfSet (Colex ((i : ι) → α i)) where
  sInf s := toColex (inf s)

theorem sInf_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j > i, e j = sInf s j}, e.1 i := by
  simp [sInf, inf]

theorem sInf_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sInf s j) : sInf s i ≤ e i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

theorem le_sInf_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i := by
  rw [sInf_apply]
  apply le_sInf
  grind

private def sup [WellFoundedGT ι] (s : Set (Colex ((i : ι) → α i))) (i : ι) : α i :=
  ⨆ e : {e ∈ s | ∀ j > i, e j = sup s j}, e.1 i
termination_by wellFounded_gt.wrap i

@[no_expose]
instance : SupSet (Colex ((i : ι) → α i)) where
  sSup s := toColex (sup s)

theorem sSup_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j > i, e j = sSup s j}, e.1 i := by
  simp [sSup, sup]

theorem le_sSup_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sSup s j) : e i ≤ sSup s i := by
  rw [sSup_apply]
  exact le_sSup ⟨⟨e, he, h⟩, rfl⟩

theorem sSup_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i := by
  rw [sSup_apply]
  apply sSup_le
  grind

private theorem sInf_le {s : Set (Colex ((i : ι) → α i))} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) : sInf s ≤ e := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  exact ha.2.not_ge (sInf_apply_le he ha.1)

private theorem le_sInf {s : Set (Colex ((i : ι) → α i))} {e : Colex ((i : ι) → α i)}
    (h : ∀ b ∈ s, e ≤ b) : e ≤ sInf s := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  refine ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ apply_le_of_toColex (h f hf) ?_
  simp_all

private theorem le_sSup {s : Set (Colex ((i : ι) → α i))} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) : e ≤ sSup s := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  exact ha.2.not_ge (le_sSup_apply he fun j hj ↦ (ha.1 j hj).symm)

private theorem sSup_le {s : Set (Colex ((i : ι) → α i))} {e : Colex ((i : ι) → α i)}
    (h : ∀ b ∈ s, b ≤ e) : sSup s ≤ e := by
  by_contra! hs
  obtain ⟨a, ha⟩ := hs
  refine ha.2.not_ge <| sSup_apply_le fun f hf hf' ↦ apply_le_of_toColex (h f hf) ?_
  simp_all

noncomputable instance completeLattice : CompleteLattice (Colex ((i : ι) → α i)) where
  sInf_le _ _ := by exact sInf_le
  le_sInf _ _ := by exact le_sInf
  le_sSup _ _ := by exact le_sSup
  sSup_le _ _ := by exact sSup_le

noncomputable instance : CompleteLinearOrder (Colex ((i : ι) → α i)) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Colex
end Pi
