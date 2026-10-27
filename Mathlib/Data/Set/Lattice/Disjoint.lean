/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Disjoint indexed families of sets

This file studies indexed unions of disjoint families of sets. It includes criteria for an
indexed or set-indexed union to be disjoint from another set, a complement formula for a partition,
and the natural maps and equivalences between an indexed union and the corresponding dependent
sum.
-/

@[expose] public section

open Function

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

/-!
### Disjoint sets
-/

section Disjoint

variable {s t : Set α}

namespace Set

@[simp]
theorem disjoint_iUnion_left {ι : Sort*} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  iSup_disjoint_iff

@[simp]
theorem disjoint_iUnion_right {ι : Sort*} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_iSup_iff

theorem disjoint_iUnion₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  iSup₂_disjoint_iff

theorem disjoint_iUnion₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_iSup₂_iff

@[simp]
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀ S) t ↔ ∀ s ∈ S, Disjoint s t :=
  sSup_disjoint_iff

@[simp]
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀ S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_sSup_iff

lemma biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ {ι : Type*} {Es : ι → Set α}
    (Es_union : ⋃ i, Es i = univ) (Es_disj : Pairwise fun i j ↦ Disjoint (Es i) (Es j))
    (I : Set ι) :
    (⋃ i ∈ I, Es i)ᶜ = ⋃ i ∈ Iᶜ, Es i := by
  ext x
  obtain ⟨i, hix⟩ : ∃ i, x ∈ Es i := by simp [← mem_iUnion, Es_union]
  have obs : ∀ (J : Set ι), x ∈ ⋃ j ∈ J, Es j ↔ i ∈ J := by
    refine fun J ↦ ⟨?_, fun i_in_J ↦ by simpa only [mem_iUnion, exists_prop] using ⟨i, i_in_J, hix⟩⟩
    intro x_in_U
    simp only [mem_iUnion, exists_prop] at x_in_U
    obtain ⟨j, j_in_J, hjx⟩ := x_in_U
    rwa [show i = j by by_contra i_ne_j; exact Disjoint.ne_of_mem (Es_disj i_ne_j) hix hjx rfl]
  have obs' : ∀ (J : Set ι), x ∈ (⋃ j ∈ J, Es j)ᶜ ↔ i ∉ J :=
    fun J ↦ by simpa only [mem_compl_iff, not_iff_not] using obs J
  rw [obs, obs', mem_compl_iff]

end Set

end Disjoint

namespace Set

variable (t : α → Set β)

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToiUnion (x : Σ i, t i) : ⋃ i, t i :=
  ⟨x.2, mem_iUnion.2 ⟨x.1, x.2.2⟩⟩

theorem sigmaToiUnion_surjective : Surjective (sigmaToiUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩

theorem sigmaToiUnion_injective (h : Pairwise (Disjoint on t)) :
    Injective (sigmaToiUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h ne).le_bot this
    Sigma.eq a_eq <| Subtype.ext <| by subst b_eq; subst a_eq; rfl

theorem sigmaToiUnion_bijective (h : Pairwise (Disjoint on t)) :
    Bijective (sigmaToiUnion t) :=
  ⟨sigmaToiUnion_injective t h, sigmaToiUnion_surjective t⟩

/-- Equivalence from the disjoint union of a family of sets forming a partition of `β`, to `β`
itself. -/
noncomputable def sigmaEquiv (s : α → Set β) (hs : ∀ b, ∃! i, b ∈ s i) :
    (Σ i, s i) ≃ β where
  toFun | ⟨_, b⟩ => b
  invFun b := ⟨(hs b).choose, b, (hs b).choose_spec.1⟩
  left_inv | ⟨i, b, hb⟩ => Sigma.subtype_ext ((hs b).choose_spec.2 i hb).symm rfl

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β}
    (h : Pairwise (Disjoint on t)) :
    (⋃ i, t i) ≃ Σ i, t i :=
  (Equiv.ofBijective _ <| sigmaToiUnion_bijective t h).symm

@[simp]
lemma coe_unionEqSigmaOfDisjoint_symm_apply {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : (i : α) × t i) :
    ((Set.unionEqSigmaOfDisjoint h).symm x : β) = x.2 := by
  rfl

@[simp]
lemma coe_snd_unionEqSigmaOfDisjoint {α β : Type*} {t : α → Set β}
    (h : Pairwise (Disjoint on t)) (x : ⋃ (i : α), t i) :
    ((Set.unionEqSigmaOfDisjoint h x).snd : β) = x := by
  conv => right; rw [← unionEqSigmaOfDisjoint h |>.symm_apply_apply x]
  rfl

end Set
