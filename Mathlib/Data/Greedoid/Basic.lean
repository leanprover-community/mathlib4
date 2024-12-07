/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Greedoid.Accessible
import Mathlib.Data.Greedoid.Exchange

/-!
# Greedoid

This file contains the definition of `ExchangeProperty` and `AccessibleProperty`, along with the
main subject `Greedoid α`.

Greedoid is a set system, i.e., a family of sets, over a finite ground set, which satisfies both
exchange and accessible properties.

Main definitions:

* `Greedoid`: The greedoid structure.

* `Greedoid.ground`: The ground set of the greedoid.

* `Greedoid.Feasible`: The feasible property of the greedoid.

* `Greedoid.Bases`: A bases of a greedoid `G` is a maximal feasible set of `G`.

* `Greedoid.Basis`: A basis of a set `s` with respect to a greedoid `G` is a maximal subset of `s`
  which is feasible in `G`.
-/

/-- Greedoid is a nonempty (finite) set system satisfying both accessible and exchange property. -/
structure Greedoid (α : Type*) where
  /-- The ground set which every element lies on. -/
  ground : Finset α
  /-- The feasible property of the greedoid. -/
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  exchange_property : Greedoid.ExchangeProperty Feasible
  subset_ground : ∀ s, Feasible s → s ⊆ ground

section Greedoid

variable {α : Type*}

end Greedoid

namespace Greedoid

variable {α : Type*}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
    G₁.ground = G₂.ground → G₁.Feasible = G₂.Feasible → G₁ = G₂
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

@[simp]
theorem feasible_injective :
    Function.Injective (fun G : Greedoid α => (G.ground, G.Feasible)) :=
  fun _ _ => by simp; exact eq_of_veq

@[simp]
theorem feasible_inj {G₁ G₂ : Greedoid α} :
    G₁.ground = G₂.ground ∧ G₁.Feasible = G₂.Feasible ↔ G₁ = G₂ :=
  ⟨fun h => by apply eq_of_veq <;> simp [h], fun h => by simp [h]⟩

variable {G : Greedoid α}
variable {s : Finset α}
variable {s₁ : Finset α} (hs₁ : G.Feasible s₁)
variable {s₂ : Finset α} (hs₂ : G.Feasible s₂)

protected theorem accessible_property :
    AccessibleProperty G.Feasible := by
  intro s h₁ h₂; by_contra h'; simp only [not_exists, not_and] at h'
  have ⟨u, hu₁, hu₂⟩ : ∃ t : Finset α, #t < #s ∧ ∀ t', G.Feasible t' → #t' < #s → #t' ≤ #t := by
    by_contra h''; simp only [not_exists, not_and, not_forall, not_le] at h''
    have h₁ : ∀ n, ∃ t, G.Feasible t ∧ #t < #s ∧ #t = n := by
      intro n; induction n with
      | zero => exact ⟨∅, G.feasible_empty, card_pos.mpr h₂, rfl⟩
      | succ n ih =>
        rcases ih with ⟨t, ht₁, ht₂, _⟩
        rcases h'' t ht₂ with ⟨_, hu₁, _, hu₂⟩
        rcases G.exchange_property hu₁ ht₁ hu₂ with ⟨_, _, h₁, h₂⟩
        exact ⟨t.cons _ h₁, h₂, card_cons _ ▸ by omega, card_cons _ ▸ by omega⟩
    rcases h₁ #s with ⟨_, _, _⟩; omega
  rcases ExchangeProperty.exists_superset_of_card_le
    G.exchange_property h₁ G.feasible_empty (le_of_lt hu₁) (zero_le _)
    with ⟨t, ht₁, _, ht₂, ht₃⟩
  simp only [not_mem_empty, or_false] at ht₂
  rcases G.exchange_property h₁ ht₁ (ht₃ ▸ hu₁) with ⟨_, _, hx₁, hx₂⟩
  have h : #(t.cons _ hx₁) < #s := by by_contra h''; simp at h''; apply h' _ ht₂ _ ht₁; omega
  have := card_cons _ ▸ ht₃ ▸ hu₂ _ hx₂ h; omega

instance : Accessible G.Feasible :=
  ⟨G.accessible_property⟩

/-- The bases of a greedoid is a maximal feasible set. -/
protected def Bases (G : Greedoid α) : Finset α → Prop := fun b ↦
  Maximal (fun t ↦ G.Feasible t ∧ t ⊆ G.ground) b

/-- The basis of a greedoid with respect to a set `s` is a maximal feasible subset of `s`. -/
protected def Basis (G : Greedoid α) (s : Finset α) : Finset α → Prop := fun b ↦
  s ⊆ G.ground ∧ Maximal (fun t ↦ G.Feasible t ∧ t ⊆ s) b

section Bases

variable {b : Finset α}

theorem bases_eq_basis_ground : G.Bases = G.Basis G.ground := by
  funext x; simp [Greedoid.Bases, Greedoid.Basis]

theorem bases_feasible (hb : G.Bases b) : G.Feasible b :=
  hb.prop.1

theorem basis_feasible (hb : G.Basis s b) : G.Feasible b :=
  hb.2.prop.1

theorem bases_subset_ground (hb : G.Bases b) : b ⊆ G.ground :=
  hb.prop.2

theorem basis_subset (hb : G.Basis s b) : b ⊆ s :=
  hb.2.prop.2

theorem basis_subset_ground (hb : G.Basis s b) : b ⊆ G.ground :=
  subset_trans (basis_subset hb) hb.1

theorem bases_maximal (hb : G.Bases b) : Maximal (fun t ↦ G.Feasible t ∧ t ⊆ G.ground) b :=
  hb

theorem basis_maximal (hb : G.Basis s b) : Maximal (fun t ↦ G.Feasible t ∧ t ⊆ s) b :=
  hb.2

theorem basis_card_eq
    {b₁ : Finset α} (hb₁ : G.Basis s b₁) {b₂ : Finset α} (hb₂ : G.Basis s b₂) :
    #b₁ = #b₂ := by
  by_contra h'; rcases ne_iff_lt_or_gt.mp h' with h' | h'
  · have ⟨_, h₁, h₂, h₃⟩ := G.exchange_property (basis_feasible hb₂) (basis_feasible hb₁) h'
    have ⟨⟨_, h₄⟩, h₅⟩ := basis_maximal hb₁
    have ⟨h₆, _⟩ := Finset.cons_subset.mp
      (h₅ ⟨h₃, (Finset.cons_subset.mpr ⟨basis_subset hb₂ h₁, h₄⟩)⟩ (subset_cons _))
    exact h₂ h₆
  · have ⟨_, h₁, h₂, h₃⟩ := G.exchange_property (basis_feasible hb₁) (basis_feasible hb₂) h'
    have ⟨⟨_, h₄⟩, h₅⟩ := basis_maximal hb₂
    have ⟨h₆, _⟩ := Finset.cons_subset.mp
      (h₅ ⟨h₃, (Finset.cons_subset.mpr ⟨basis_subset hb₁ h₁, h₄⟩)⟩ (subset_cons _))
    exact h₂ h₆

theorem bases_card_eq
    {b₁ : Finset α} (hb₁ : G.Bases b₁) {b₂ : Finset α} (hb₂ : G.Bases b₂) :
    #b₁ = #b₂ :=
  basis_card_eq (bases_eq_basis_ground ▸ hb₁) (bases_eq_basis_ground ▸ hb₂)

end Bases

end Greedoid

