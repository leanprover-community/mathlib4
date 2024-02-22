/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Card

/-!
# Partitioned

## Main definitions

* `partitioned`

## Main statements

* `fooBar_unique`

-/

open Set

variable {α : Type*}

def partitioned (f : ℕ → Set α) : ℕ → Set (Set α)
  | 0 => {f 0, (f 0)ᶜ}
  | n + 1 => ⋃ u ∈ partitioned f n, {u ∩ f (n + 1), u \ f (n + 1)}

@[simp]
lemma partitioned_zero (f : ℕ → Set α) : partitioned f 0 = {f 0, (f 0)ᶜ} := rfl

lemma partitioned_succ (f : ℕ → Set α) (n : ℕ) :
    partitioned f (n + 1) = ⋃ u ∈ partitioned f n, {u ∩ f (n + 1), u \ f (n + 1)} := rfl

lemma disjoint_partitioned (f : ℕ → Set α) (n : ℕ) :
    ∀ u ∈ partitioned f n, ∀ v ∈ partitioned f n, u ≠ v → Disjoint u v := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, partitioned_zero, union_singleton, mem_insert_iff,
      mem_singleton_iff, ne_eq, forall_eq_or_imp, forall_eq, not_true_eq_false, disjoint_self,
      bot_eq_empty, compl_empty_iff, IsEmpty.forall_iff, true_and, and_true]
    exact ⟨fun _ ↦ disjoint_compl_right, fun _ ↦ disjoint_compl_left⟩
  | succ n ih =>
    intro u hu v hv huv
    rw [partitioned_succ] at hu hv
    simp only [union_singleton, mem_iUnion, mem_insert_iff, mem_singleton_iff, exists_prop] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _) (ih u' hu' v' hv' ?_)
      exact fun huv' ↦ huv (huv' ▸ rfl)
    · by_cases huv' : u' = v'
      · rw [huv']
        exact Disjoint.mono_left (inter_subset_right _ _) Set.disjoint_sdiff_right
      · exact Disjoint.mono (inter_subset_left _ _) (diff_subset _ _) (ih u' hu' v' hv' huv')
    · by_cases huv' : u' = v'
      · rw [huv']
        exact Disjoint.mono_right (inter_subset_right _ _) Set.disjoint_sdiff_left
      · exact Disjoint.mono (diff_subset _ _) (inter_subset_left _ _) (ih u' hu' v' hv' huv')
    · refine Disjoint.mono (diff_subset _ _) (diff_subset _ _) (ih u' hu' v' hv' ?_)
      refine fun huv' ↦ huv (huv' ▸ rfl)

lemma sUnion_partitioned (f : ℕ → Set α) (n : ℕ) : ⋃₀ partitioned f n = univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [partitioned_succ]
    ext x
    have : x ∈ ⋃₀ partitioned f n := by simp [ih]
    simp only [mem_sUnion, mem_iUnion, mem_insert_iff, mem_singleton_iff, exists_prop, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x ∈ f (n + 1)
    · exact ⟨t ∩ f (n + 1), ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f (n + 1), ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩

lemma partitioned_finite (f : ℕ → Set α) (n : ℕ) : Set.Finite (partitioned f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [partitioned_succ]
    have : Finite (partitioned f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    refine Finite.Set.finite_biUnion (partitioned f n) _ (fun u _ ↦ ?_)
    rw [Set.finite_coe_iff]
    simp

noncomputable
instance instFintypePartitioned (f : ℕ → Set α) (n : ℕ) : Fintype (partitioned f n) :=
  Set.Finite.fintype (partitioned_finite f n)
